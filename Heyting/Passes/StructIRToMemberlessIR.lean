/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Languages.StructIR
import Heyting.Languages.MemberlessIR

/-!
# StructIR → MemberlessIR Pass

Eliminates the struct-member hierarchy from `StructIR`, producing a
`MemberlessIR` module where every variable is a flat felt slot.

## Concern handled by this pass

**Struct flattening** only.  `readMember`, `writeMember`, `newStruct`, and
the `InstancePath`/`ObjEnv` machinery are entirely eliminated.  Cross-struct
`call` statements are kept as-is (call inlining happens in Pass 2).

## Compilation strategy

Each `StructIR.ConstrainStmt` maps to at most one `MemberlessIR.Stmt`:

| StructIR statement | MemberlessIR output | Notes |
|---|---|---|
| `feltAdd/Sub/Mul/Div/Neg/Const` | same op, same local-var IDs | identity |
| `constrainEq` | `constrainEq` | identity |
| `readMember dest self member` | *(nothing)* | witness pre-populates `dest` |
| `call target args` | `call target args` | identity |

Because `StructIR.LocalVar = MemberlessIR.LocalVar = Nat`, local variable
IDs are preserved verbatim.

## Witness translation

### Forward (`compileWitness`)

Given a `StructIR` witness `ws : VarId → F`, the `MemberlessIR` witness is:

```
mw v = evalEnv(ws, body)[v]
```

where `evalEnv` tracks the felt environment as `StructIR.evalConstrainBody`
would, but only records the value at each local variable after assignment.

Concretely, `compileWitness` mirrors `StructIR.evalConstrainBody` structurally,
threading the `LocalEnv` and `ObjEnv`, and at each `readMember dest self member`
sets `mw dest = ws(objEnv self, member.val)`.  For all other assignments (felt
ops), `mw dest = computed value`.  For `constrainEq` and `call`, no assignment.

### Backward (`extractWitness`)

Given a `MemberlessIR` witness `mw : Nat → F`, the `StructIR` witness is:

```
ws (path, member) = mw (readSlot path member)
```

where `readSlot path member` is the local variable ID that `readMember` stored
the value of `(path, member)` into.  This mapping is computed by `buildReadMap`,
which mirrors `compileConstrainBody` but records `readMember` allocations.

## Correctness

**Preservation**: if `ws` satisfies `StructIR.Module m`, then `compileWitness ws`
satisfies `MemberlessIR.Module (compile m)`.

**Reflection**: if `mw` satisfies `MemberlessIR.Module (compile m)`, then
`extractWitness mw` satisfies `StructIR.Module m`.
-/

namespace StructIRToMemberlessIR

open StructIR MemberlessIR

variable {F : Type} [Field F] {n : Nat}

/-! ## Program compilation -/

/-- Compile a single `StructIR.ConstrainStmt` into zero or one
    `MemberlessIR.Stmt`s.  `readMember` produces nothing; everything
    else is preserved verbatim. -/
def compileStmt {numMembers : Nat} (i : Fin n)
    (stmt : StructIR.ConstrainStmt n i F numMembers) :
    Option (MemberlessIR.Stmt n i F) :=
  match stmt with
  | .feltAdd dest src1 src2  => some (.feltAdd dest src1 src2)
  | .feltSub dest src1 src2  => some (.feltSub dest src1 src2)
  | .feltMul dest src1 src2  => some (.feltMul dest src1 src2)
  | .feltDiv dest src1 src2  => some (.feltDiv dest src1 src2)
  | .feltNeg dest src        => some (.feltNeg dest src)
  | .feltConst dest c        => some (.feltConst dest c)
  | .constrainEq src1 src2   => some (.constrainEq src1 src2)
  | .readMember _ _ _        => none   -- witness pre-populates; no instruction needed
  | .call target args        => some (.call target args)

/-- Compile a list of `StructIR.ConstrainStmt`s, dropping `readMember`s. -/
def compileStmts {numMembers : Nat} (i : Fin n)
    (stmts : List (StructIR.ConstrainStmt n i F numMembers)) :
    List (MemberlessIR.Stmt n i F) :=
  stmts.filterMap (compileStmt i)

/-- Compile a single `StructIR.StructDef` into a `MemberlessIR.Func`. -/
def compileFunc (i : Fin n) (sd : StructIR.StructDef n i F) :
    MemberlessIR.Func n i F where
  numParams := sd.constrain.numParams
  body      := compileStmts i sd.constrain.body

/-- Compile a whole `StructIR.Module` into a `MemberlessIR.Module`.
    Struct index structure (`Fin n`) is preserved. -/
def compile (m : StructIR.Module (n + 1) F) : MemberlessIR.Module (n + 1) F :=
  fun i => compileFunc i (m.structs i)

/-! ## Witness translation (forward) -/

/-- Thread the `StructIR` env/objEnv state through a constrain body and
    produce a `MemberlessIR` witness: a function `Nat → F` recording the
    felt value of every local variable at the point where it was last written.

    Mirrors `StructIR.evalConstrainBody` exactly.  For `readMember`, the value
    is read from the StructIR witness `ws`; for felt ops, it is computed. -/
def compileWitness (m : StructIR.Module n F) (ws : StructIR.Witness F)
    (i : Fin n) (env : StructIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (acc : Nat → F) : (Nat → F) :=
  match stmts with
  | [] => acc
  | stmt :: rest =>
    let (env', objEnv', acc') :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        let v := env src1 + env src2
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltSub dest src1 src2 =>
        let v := env src1 - env src2
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltMul dest src1 src2 =>
        let v := env src1 * env src2
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltDiv dest src1 src2 =>
        let v := env src1 * (env src2)⁻¹
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltNeg dest src =>
        let v := -(env src)
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltConst dest c =>
        (env.update dest c, objEnv,
         fun k => if k == dest then c else acc k)
      | .readMember dest self member =>
        let path := objEnv self
        let v    := ws (path, member.val)
        (env.update dest v, objEnv.update dest (path ++ [member.val]),
         fun k => if k == dest then v else acc k)
      | .constrainEq _ _ =>
        (env, objEnv, acc)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let calleeEnv : StructIR.LocalEnv F := fun param =>
          match args[param]? with
          | some arg => env arg
          | none     => 0
        let calleeObjEnv : StructIR.ObjEnv := fun param =>
          match args[param]? with
          | some arg => objEnv arg
          | none     => []
        let acc' := compileWitness m ws j calleeEnv calleeObjEnv
          (m.structs j).constrain.body acc
        (env, objEnv, acc')
    compileWitness m ws i env' objEnv' rest acc'
  termination_by (i, stmts.length)

/-- Build the top-level `MemberlessIR` witness from a `StructIR` witness.

    The initial `StructIR` environment has `env k = ws([], k)` (matching
    `satisfies`). The initial `MemberlessIR` accumulator is pre-seeded with
    the same values so that param slots are visible before any statement runs. -/
def compileModuleWitness (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    Nat → F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  -- Seed the initial env from the witness at root-path positions,
  -- matching the new StructIR.satisfies seeding: env k = ws ([], k).
  let initEnv    : StructIR.LocalEnv F := fun k => ws ([], k)
  let initObjEnv : StructIR.ObjEnv    :=
    StructIR.ObjEnv.update (fun _ => []) 0 []
  -- Pre-seed the accumulator with the param values so they are visible
  -- even for params that are never explicitly written by a statement.
  let numParams := (m.structs mainIdx).constrain.numParams
  let initAcc : Nat → F := fun k => if k < numParams then ws ([], k) else 0
  compileWitness m ws mainIdx initEnv initObjEnv
    (m.structs mainIdx).constrain.body initAcc

/-! ## Witness extraction (backward) -/

/-- `ReadMap`: maps each `StructIR.VarId` (i.e. `InstancePath × Nat`) to the
    `LocalVar` index that holds its value in the compiled MemberlessIR program.
    Computed by `buildReadMap`. -/
abbrev ReadMap := StructIR.VarId → StructIR.LocalVar

/-- Build the `ReadMap` by mirroring `compileConstrainBody`, recording for
    each `readMember` which local variable (`dest`) received the value of
    `(objEnv self, member.val)`. -/
def buildReadMap (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (acc : ReadMap) : ReadMap :=
  match stmts with
  | [] => acc
  | stmt :: rest =>
    let (objEnv', acc') :=
      match stmt with
      | .readMember dest self member =>
        let path := objEnv self
        (objEnv.update dest (path ++ [member.val]),
         fun vid => if vid == (path, member.val) then dest else acc vid)
      | .feltAdd _ _ _ | .feltSub _ _ _ | .feltMul _ _ _
      | .feltDiv _ _ _ | .feltNeg _ _ | .feltConst _ _ =>
        (objEnv, acc)
      | .constrainEq _ _ =>
        (objEnv, acc)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let calleeObjEnv : StructIR.ObjEnv := fun param =>
          match args[param]? with
          | some arg => objEnv arg
          | none     => []
        let acc' := buildReadMap m j calleeObjEnv (m.structs j).constrain.body acc
        (objEnv, acc')
    buildReadMap m i objEnv' rest acc'
  termination_by (i, stmts.length)

/-- Extract a `StructIR` witness from a `MemberlessIR` witness `mw`.

    Uses `buildReadMap` to find which local-variable slot corresponds to each
    `(path, member)` pair, then reads `mw` at that slot. -/
def extractWitness (m : StructIR.Module (n + 1) F) (mw : Nat → F) :
    StructIR.Witness F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initObjEnv : StructIR.ObjEnv :=
    StructIR.ObjEnv.update (fun _ => []) 0 []
  let rmap := buildReadMap m mainIdx initObjEnv
    (m.structs mainIdx).constrain.body (fun _ => 0)
  fun vid => mw (rmap vid)

/-! ## Witness relation -/

/-- The witness relation for Pass 1: `mw` is related to `ws` if `mw` agrees
    with `ws` on all variables that were written by the compiled body — that is,
    `mw v = env v` where `env` is the StructIR local environment after evaluating
    the body with witness `ws`.

    Concretely, `mw = compileModuleWitness m ws` (the relation is the graph of
    `compileModuleWitness`). -/
def witnessRel (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F)
    (mw : Nat → F) : Prop :=
  mw = compileModuleWitness m ws

/-! ## Correctness theorems (sorried — to be proved) -/

/-- **Preservation**: if `ws` satisfies the `StructIR` module `m`, then
    `compileModuleWitness m ws` satisfies the compiled `MemberlessIR` module. -/
theorem preservation (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F)
    (h : StructIR.satisfies ws m) :
    MemberlessIR.satisfies (compileModuleWitness m ws) (compile m) := by
  sorry

/-- **Reflection**: if `mw` satisfies the compiled `MemberlessIR` module, then
    `extractWitness m mw` satisfies the original `StructIR` module `m`. -/
theorem reflection (m : StructIR.Module (n + 1) F)
    (mw : Nat → F)
    (h : MemberlessIR.satisfies mw (compile m)) :
    StructIR.satisfies (extractWitness m mw) m := by
  sorry

end StructIRToMemberlessIR
