/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Core.Pass
import Heyting.Languages.StructInlineIR
import Heyting.Languages.MemberlessIR
import Mathlib.Data.List.Nodup

/-!
# StructInlineIR → MemberlessIR Pass

Eliminates struct-member hierarchy from the call-free `StructInlineIR`,
producing a `MemberlessIR` module where every variable is a flat felt slot.

## Concern handled by this pass

**Struct flattening** only. `readMember` and the `ObjEnv`/`InstancePath`
machinery are entirely eliminated. StructInlineIR has no `call` statement
(it is call-free by construction, Pass 1's output), so there is nothing to
inline here.

## Compilation strategy (Option 2: drop `readMember`, pre-populate via witness)

Each `StructInlineIR.ConstrainStmt` maps to at most one `MemberlessIR.Stmt`:

| StructInlineIR statement          | MemberlessIR output  | Notes                        |
|-----------------------------------|----------------------|------------------------------|
| `feltAdd/Sub/Mul/Div/Neg/Const`   | same op, same vars   | identity                     |
| `constrainEq`                     | `constrainEq`        | identity                     |
| `readMember dest self member`     | *(nothing)*          | witness pre-populates `dest` |

`ObjEnv` is threaded through `compileBody` statically so we know the concrete
`InstancePath` for each `readMember` at compile time — but it's only used to
compute witness values; the compiled MemberlessIR body drops `readMember`
entirely.

Local variable IDs are preserved verbatim (StructInlineIR.LocalVar =
MemberlessIR.LocalVar = Nat).

## Witness translation (forward)

`compileWitness m ws` replays the StructInlineIR body with ObjEnv threading,
producing a MemberlessIR witness `mw : Nat → F`. At each `readMember dest self
member`, it sets `mw dest := ws(objEnv self, member)`. For felt ops, it sets
`mw dest` to the computed value. For `constrainEq` and no-op statements, it
leaves `mw` unchanged.

## Witness translation (backward)

`extractWitness m mw` builds a `ReadMap : VarId → LocalVar` via `buildReadMap`,
which replays the body and records which local variable received each
`(path, member)` value. Then `ws vid := mw (readMap vid)`.

## Correctness

- **Preservation**: if `ws` satisfies `StructInlineIR.Module m`, then
  `compileWitness m ws` satisfies `MemberlessIR.Module (compile m)`.
- **Reflection**: if `mw` satisfies `MemberlessIR.Module (compile m)`, then
  `extractWitness m mw` satisfies `StructInlineIR.Module m`. Requires
  `m.noDupReads`.
-/

namespace StructInlineIRToMemberlessIR

open StructIR StructInlineIR MemberlessIR

variable {F : Type} [Field F] {n : Nat}

/-! ## Program compilation -/

/-- Compile a single `StructInlineIR.ConstrainStmt` into zero or one
    `MemberlessIR.Stmt`s. `readMember` produces nothing; everything else
    is preserved verbatim. -/
def compileStmt {n : Nat} {F : Type} {i : Fin n}
    (stmt : StructInlineIR.ConstrainStmt n F) :
    Option (MemberlessIR.Stmt n i F) :=
  match stmt with
  | .feltAdd dest src1 src2  => some (.feltAdd dest src1 src2)
  | .feltSub dest src1 src2  => some (.feltSub dest src1 src2)
  | .feltMul dest src1 src2  => some (.feltMul dest src1 src2)
  | .feltDiv dest src1 src2  => some (.feltDiv dest src1 src2)
  | .feltNeg dest src        => some (.feltNeg dest src)
  | .feltConst dest c        => some (.feltConst dest c)
  | .constrainEq src1 src2   => some (.constrainEq src1 src2)
  | .readMember _ _ _        => none -- witness pre-populates; no instruction needed

/-- Compile a list of `StructInlineIR.ConstrainStmt`s, dropping `readMember`s. -/
def compileStmts {n : Nat} {F : Type} {i : Fin n}
    (stmts : List (StructInlineIR.ConstrainStmt n F)) :
    List (MemberlessIR.Stmt n i F) :=
  stmts.filterMap compileStmt

/-- Compile a single `StructInlineIR.StructDef` into a `MemberlessIR.Func`. -/
def compileFunc (i : Fin n) (sd : StructInlineIR.StructDef n F) :
    MemberlessIR.Func n i F where
  numParams := sd.constrain.numParams
  body      := compileStmts (i := i) sd.constrain.body

/-- Compile a whole `StructInlineIR.Module` into a `MemberlessIR.Module`. -/
def compile (m : StructInlineIR.Module (n + 1) F) : MemberlessIR.Module (n + 1) F :=
  fun i => compileFunc i (m.structs i)

/-! ## Witness translation (forward) -/

/-- Thread env + ObjEnv through a StructInlineIR body, producing a MemberlessIR
    witness `mw : Nat → F`. Mirrors `StructInlineIR.evalConstrainBody` in its
    env/objEnv evolution. Each written slot receives the StructInlineIR env
    value at the point of the last write; other slots are kept at their
    initial value (`ws([],k)`). -/
def compileWitnessBody (ws : StructInlineIR.Witness F)
    (env : StructInlineIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : Nat → F) : Nat → F :=
  match stmts with
  | [] => acc
  | stmt :: rest =>
    let (env', objEnv', acc') :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        let v := env src1 + env src2
        (env.update dest v, objEnv, fun k => if k == dest then v else acc k)
      | .feltSub dest src1 src2 =>
        let v := env src1 - env src2
        (env.update dest v, objEnv, fun k => if k == dest then v else acc k)
      | .feltMul dest src1 src2 =>
        let v := env src1 * env src2
        (env.update dest v, objEnv, fun k => if k == dest then v else acc k)
      | .feltDiv dest src1 src2 =>
        let v := env src1 * (env src2)⁻¹
        (env.update dest v, objEnv, fun k => if k == dest then v else acc k)
      | .feltNeg dest src =>
        let v := -(env src)
        (env.update dest v, objEnv, fun k => if k == dest then v else acc k)
      | .feltConst dest c =>
        (env.update dest c, objEnv, fun k => if k == dest then c else acc k)
      | .readMember dest self member =>
        let path := objEnv self
        let v := ws (path, member)
        (env.update dest v,
         StructIR.ObjEnv.update objEnv dest (path ++ [member]),
         fun k => if k == dest then v else acc k)
      | .constrainEq _ _ =>
        (env, objEnv, acc)
    compileWitnessBody ws env' objEnv' rest acc'

/-- Build the top-level `MemberlessIR` witness from a `StructInlineIR` witness.

    The initial env is seeded from `ws` at root-path positions, matching
    `StructInlineIR.satisfies`. The initial accumulator matches the initial env
    so that unwritten positions agree. -/
def compileWitness (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) : Nat → F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initEnv : StructInlineIR.LocalEnv F := fun k => ws ([], k)
  let initObjEnv : StructIR.ObjEnv :=
    StructIR.ObjEnv.update (fun _ => []) 0 []
  let initAcc : Nat → F := fun k => ws ([], k)
  compileWitnessBody ws initEnv initObjEnv
    (m.structs mainIdx).constrain.body initAcc

/-! ## Compile-witness agreement lemma -/

/-- `compileWitnessBody` maintains `acc = env` pointwise throughout the
    body evaluation. Combined with the initial seeding `acc = initEnv`, this
    means the output `mw` equals the final StructInlineIR env. -/
theorem compileWitnessBody_agrees (ws : StructInlineIR.Witness F)
    (env : StructInlineIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : Nat → F) (hAcc : ∀ k, acc k = env k) :
    ∀ k, compileWitnessBody ws env objEnv stmts acc k =
      (StructInlineIR.runState ws env objEnv stmts).1 k := by
  induction stmts generalizing env objEnv acc with
  | nil =>
    intro k
    simp [compileWitnessBody, StructInlineIR.runState, hAcc]
  | cons stmt rest ih =>
    intro k
    have acc_update_agrees : ∀ (dest : Nat) (v : F),
        ∀ k', (fun k' => if k' == dest then v else acc k') k' =
              (env.update dest v) k' := by
      intro dest v k'
      simp only [StructInlineIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hAcc k'
    match stmt with
    | .feltAdd dest src1 src2 =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .feltSub dest src1 src2 =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .feltMul dest src1 src2 =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .feltDiv dest src1 src2 =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .feltNeg dest src =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .feltConst dest c =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .readMember dest self member =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ (acc_update_agrees dest _) k
    | .constrainEq src1 src2 =>
      simp only [compileWitnessBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih _ _ _ hAcc k

/-! ## Witness translation (backward) -/

/-- A `ReadMap` records, for each `(path, member)` pair, the local variable
    ID that `readMember` stored the value of that pair into. -/
abbrev ReadMap := StructIR.VarId → StructInlineIR.LocalVar

/-- Build the `ReadMap` by mirroring `compileWitnessBody`, recording for each
    `readMember` which local variable (`dest`) received the value of
    `(objEnv self, member)`. -/
def buildReadMap (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : ReadMap) : ReadMap :=
  match stmts with
  | [] => acc
  | stmt :: rest =>
    let (objEnv', acc') :=
      match stmt with
      | .readMember dest self member =>
        let path := objEnv self
        (StructIR.ObjEnv.update objEnv dest (path ++ [member]),
         fun vid => if vid == (path, member) then dest else acc vid)
      | .feltAdd _ _ _ | .feltSub _ _ _ | .feltMul _ _ _
      | .feltDiv _ _ _ | .feltNeg _ _ | .feltConst _ _ =>
        (objEnv, acc)
      | .constrainEq _ _ =>
        (objEnv, acc)
    buildReadMap objEnv' rest acc'

/-- Extract a `StructInlineIR` witness from a `MemberlessIR` witness `mw`.

    Uses `buildReadMap` to find which local-variable slot corresponds to each
    `(path, member)` pair, then reads `mw` at that slot. For root-level params
    (path=[]), reads from `mw` directly. -/
def extractWitness (m : StructInlineIR.Module (n + 1) F) (mw : Nat → F) :
    StructInlineIR.Witness F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initObjEnv : StructIR.ObjEnv :=
    StructIR.ObjEnv.update (fun _ => []) 0 []
  let rmap := buildReadMap initObjEnv
    (m.structs mainIdx).constrain.body (fun _ => 0)
  fun vid =>
    if vid.1 = [] then mw vid.2 else mw (rmap vid)

/-! ## Witness relation -/

/-- The witness relation: `mw = compileWitness m ws` (graph of `compileWitness`). -/
def witnessRel (m : StructInlineIR.Module (n + 1) F) (ws : StructInlineIR.Witness F)
    (mw : Nat → F) : Prop :=
  mw = compileWitness m ws

theorem witnessRel_compileWitness (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) :
    witnessRel m ws (compileWitness m ws) := rfl

/-! ## `Pass` instance and correctness theorems (sorried, proof in progress) -/

/-- **Preservation**: if `ws` satisfies the `StructInlineIR` module `m`, then
    `compileWitness m ws` satisfies the compiled `MemberlessIR` module.

    Requires SSA (`m.isSSA`) and def-before-use to relate intermediate env values
    at each felt-op assertion to the final witness. -/
theorem preservation (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F)
    (h : StructInlineIR.satisfies ws m) :
    MemberlessIR.satisfies (compileWitness m ws) (compile m) := by
  sorry

/-- **Reflection**: if `mw` satisfies the compiled `MemberlessIR` module, then
    `extractWitness m mw` satisfies the original `StructInlineIR` module `m`.

    Requires `m.noDupReads` for `buildReadMap` injectivity at read positions. -/
theorem reflection (m : StructInlineIR.Module (n + 1) F)
    (mw : Nat → F)
    (h : MemberlessIR.satisfies mw (compile m)) :
    StructInlineIR.satisfies (extractWitness m mw) m := by
  sorry

instance Pass (n : Nat) (F : Type) [Field F] :
    Pass (StructInlineIR.Language n F) (MemberlessIR.instLanguage n F) where
  compile := compile
  witnessRel := witnessRel

end StructInlineIRToMemberlessIR
