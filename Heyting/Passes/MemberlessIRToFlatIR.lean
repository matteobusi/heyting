/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Languages.MemberlessIR
import Heyting.Languages.FlatIR

/-!
# MemberlessIR → FlatIR Pass

Lowers `MemberlessIR` felt-arithmetic operations to a flat list of
`FlatIR` instructions.

## Concerns handled by this pass

1. **Param absorption**: felt parameters (`0..numParams-1`) are absorbed into
   the flat variable namespace via the initial `VarMap`.
2. **Member read handling**: `readMember dest self index` allocates a slot for
   `dest` but emits no instruction — the witness value is pre-populated by the
   compileWitness chain from Pass 2.

After this pass the result is a single flat list of `FlatIR.Instr` with no
control flow; it can then be encoded as R1CS by `FlatIRToR1CS`.

## Variable allocation

A monotonically increasing counter `next : Nat` allocates fresh `FlatIR.VarId`s.
A `VarMap : LocalVar → FlatIR.VarId` translates `MemberlessIR` local variables
to `FlatIR` variable IDs.

### Statement mapping

| MemberlessIR statement | FlatIR output | VarMap update |
|---|---|---|
| `feltAdd dest src1 src2` | `assignAdd next (vm src1) (vm src2)` | `vm[dest] := next; next++` |
| `feltSub dest src1 src2` | `assignSub next (vm src1) (vm src2)` | `vm[dest] := next; next++` |
| `feltMul dest src1 src2` | `assignMul next (vm src1) (vm src2)` | `vm[dest] := next; next++` |
| `feltDiv dest src1 src2` | `assignDiv next (vm src1) (vm src2)` | `vm[dest] := next; next++` |
| `feltNeg dest src` | `assignNeg next (vm src)` | `vm[dest] := next; next++` |
| `feltConst dest c` | `assignConst next c` | `vm[dest] := next; next++` |
| `constrainEq src1 src2` | `assertEq (vm src1) (vm src2)` | none |
| `readMember dest self index` | *(none — pre-populated slot)* | `vm[dest] := next; next++` |

## Witness translation

### Forward (`compileWitness`)

Mirrors `compileBody`, threading both the `FlatIR` accumulator and the
`MemberlessIR` local environment.

### Backward (`extractWitness`)

```
extractWitness wt = fun v => wt (.var (compileVar m v))
```

where `compileVar` gives the `FlatIR` slot for MemberlessIR local `v`.
-/

namespace MemberlessIRToFlatIR

open MemberlessIR FlatIR

variable {F : Type} [Field F] {n : Nat}

/-! ## Variable map -/

/-- Maps `MemberlessIR.LocalVar → FlatIR.VarId`. -/
abbrev VarMap := MemberlessIR.LocalVar → FlatIR.VarId

/-- Update a `VarMap` at a single local variable. -/
def VarMap.update (vm : VarMap) (local_ : MemberlessIR.LocalVar) (flat : FlatIR.VarId) :
    VarMap :=
  fun v => if v == local_ then flat else vm v

/-! ## Program compilation -/

/-- Compile a `MemberlessIR` body to `FlatIR`.

    Returns `(instructions, next')` where `next'` is the next available
    `FlatIR.VarId` after all allocations in this body.

    `memberSlot` is a function that maps member index to its pre-allocated
    FlatIR slot (for readMember operations).

    Termination: structural on `stmts.length`. -/
def compileBody (m : MemberlessIR.Module n F) (i : Fin n) (vm : VarMap) (next : Nat)
    (memberSlot : Nat → Nat)
    (stmts : List (MemberlessIR.Stmt n i F)) :
    List (FlatIR.Instr F) × Nat :=
  match stmts with
  | [] => ([], next)
  | stmt :: rest =>
    let (instrs, vm', next') :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        -- Felt ops: reference sources via vm, output to fresh slot
        ([FlatIR.Instr.assignAdd next (vm src1) (vm src2)],
         vm.update dest next, next + 1)
      | .feltSub dest src1 src2 =>
        ([FlatIR.Instr.assignSub next (vm src1) (vm src2)],
         vm.update dest next, next + 1)
      | .feltMul dest src1 src2 =>
        ([FlatIR.Instr.assignMul next (vm src1) (vm src2)],
         vm.update dest next, next + 1)
      | .feltDiv dest src1 src2 =>
        ([FlatIR.Instr.assignDiv next (vm src1) (vm src2)],
         vm.update dest next, next + 1)
      | .feltNeg dest src =>
        ([FlatIR.Instr.assignNeg next (vm src)],
         vm.update dest next, next + 1)
      | .feltConst dest c =>
        ([FlatIR.Instr.assignConst next c],
         vm.update dest next, next + 1)
      | .constrainEq src1 src2 =>
        ([FlatIR.Instr.assertEq (vm src1) (vm src2)], vm, next)
      | .readMember dest _self _index =>
        -- readMember allocates a fresh slot for `dest` and emits no instruction.
        -- The witness value is assigned by `compileWitness`.
        ([], vm.update dest next, next + 1)
    let (restInstrs, finalNext) := compileBody m i vm' next' memberSlot rest
    (instrs ++ restInstrs, finalNext)
  termination_by stmts.length

/-- Collect all member indices accessed by readMember in the main function body.
    Each member index corresponds to a pre-allocated signal in the FlatIR. -/
def collectReadMemberIndices (m : MemberlessIR.Module (n + 1) F) :
    List Nat :=
  let mainIdx := Fin.last n
  (m mainIdx).body.filterMap fun stmt =>
    match stmt with
    | .readMember _ _ index => some index
    | _ => none

/-- Helper to find the pre-allocated slot for a member index. -/
def findMemberSlot (memberSignalMap : List (Nat × Nat)) (memberIdx : Nat) : Nat :=
  match memberSignalMap.find? (fun (idx, _) => idx = memberIdx) with
  | some (_, slot) => slot
  | none => 0  -- fallback, should not happen for valid programs

/-- Compile a whole `MemberlessIR.Module` to a `FlatIR.Program`.

    The main function is at index `n`.  Its parameters occupy FlatIR slots
    `0..numParams-1` via the initial `VarMap`. Each struct member accessed by
    readMember gets a pre-allocated slot (no constraint emitted). Felt ops
    allocate fresh slots for their results. -/
def compile (m : MemberlessIR.Module (n + 1) F) : FlatIR.Program F :=
  let mainIdx := Fin.last n
  let numParams := (m mainIdx).numParams
  let initVm : VarMap := fun v => if v < numParams then v else 0
  let initNext := numParams
  let memberSlot : Nat → Nat := fun _ => 0
  (compileBody m mainIdx initVm initNext memberSlot (m mainIdx).body).1

/-! ## Witness translation (forward) -/

/-- Build the `FlatIR` witness from a `MemberlessIR` witness `mw`.

    Mirrors `compileBody`, threading a `LocalEnv` and an accumulator for
    the `FlatIR` witness.
    `memberSlot` maps member index to its pre-allocated FlatIR slot. -/
def compileWitness (m : MemberlessIR.Module n F)
    (mw : Nat → F)
    (i : Fin n) (vm : VarMap) (next : Nat) (memberSlot : Nat → Nat)
    (env : MemberlessIR.LocalEnv F)
    (stmts : List (MemberlessIR.Stmt n i F))
    (acc : FlatIR.VarId → F) : (FlatIR.VarId → F) × Nat :=
  match stmts with
  | [] => (acc, next)
  | stmt :: rest =>
    let (env', vm', next', acc') :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        let v := env src1 + env src2
        (env.update dest v, vm.update dest next, next + 1,
         fun k => if k == next then v else acc k)
      | .feltSub dest src1 src2 =>
        let v := env src1 - env src2
        (env.update dest v, vm.update dest next, next + 1,
         fun k => if k == next then v else acc k)
      | .feltMul dest src1 src2 =>
        let v := env src1 * env src2
        (env.update dest v, vm.update dest next, next + 1,
         fun k => if k == next then v else acc k)
      | .feltDiv dest src1 src2 =>
        let v := env src1 * (env src2)⁻¹
        (env.update dest v, vm.update dest next, next + 1,
         fun k => if k == next then v else acc k)
      | .feltNeg dest src =>
        let v := -(env src)
        (env.update dest v, vm.update dest next, next + 1,
         fun k => if k == next then v else acc k)
      | .feltConst dest c =>
        (env.update dest c, vm.update dest next, next + 1,
         fun k => if k == next then c else acc k)
      | .constrainEq _ _ =>
        (env, vm, next, acc)
      | .readMember dest _self _index =>
        -- readMember allocates a fresh slot and writes witness value `mw dest`.
        let v := mw dest
        (env.update dest v, vm.update dest next, next + 1,
         fun k => if k == next then v else acc k)
    compileWitness m mw i vm' next' memberSlot env' rest acc'
  termination_by stmts.length

/-- Build the top-level `FlatIR` witness from a `MemberlessIR` witness `mw`.

    The main function's initial env is `mw` itself (seeded from the MemberlessIR
    witness).  The initial FlatIR accumulator agrees with `mw` on param slots. -/
def compileModuleWitness (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F) :
    FlatIR.VarId → F :=
  let mainIdx := Fin.last n
  let numParams := (m mainIdx).numParams
  let memberSlot : Nat → Nat := fun _ => 0
  let initVm : VarMap := fun v => if v < numParams then v else 0
  let initNext := numParams
  let initAcc := fun (k : FlatIR.VarId) =>
    if k < numParams then mw k else 0
  (compileWitness m mw mainIdx initVm initNext memberSlot mw (m mainIdx).body initAcc).1

/-! ## Witness extraction (backward) -/

/-- Build a map from `MemberlessIR.LocalVar → FlatIR.VarId` (same allocation
    as `compileBody`) so we can read back values after the fact. -/
def buildVarMap (m : MemberlessIR.Module n F) (i : Fin n) (vm : VarMap) (next : Nat)
    (stmts : List (MemberlessIR.Stmt n i F)) : VarMap × Nat :=
match stmts with
  | [] => (vm, next)
  | stmt :: rest =>
    let (vm', next') :=
      match stmt with
      | .feltAdd dest _ _ | .feltSub dest _ _ | .feltMul dest _ _
      | .feltDiv dest _ _ | .feltNeg dest _ | .feltConst dest _ =>
        (vm.update dest next, next + 1)
      | .constrainEq _ _ => (vm, next)
      | .readMember dest _self _index =>
        (vm.update dest next, next + 1)
    buildVarMap m i vm' next' rest
  termination_by stmts.length

/-- Extract a `MemberlessIR` witness from a `FlatIR` witness `wt`.

    Each MemberlessIR local variable `v` maps to `wt (vm v)` where `vm` is the
    variable map produced by `buildVarMap`. -/
def extractWitness (m : MemberlessIR.Module (n + 1) F) (wt : FlatIR.VarId → F) :
    Nat → F :=
  let mainIdx : Fin (n + 1) := Fin.last n
  let numParams := (m mainIdx).numParams
  let initVm : VarMap := fun v => if v < numParams then v else 0
  let initNext := numParams
  let (finalVm, _) := buildVarMap m mainIdx initVm initNext (m mainIdx).body
  fun v => wt (finalVm v)

/-! ## Witness relation -/

/-- The witness relation: `wt` is related to `mw` if `wt = compileModuleWitness m mw`
    (i.e., `wt` is the FlatIR witness produced by forward translation from `mw`). -/
def witnessRel (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F)
    (wt : FlatIR.VarId → F) : Prop :=
  wt = compileModuleWitness m mw

theorem witnessRel_compileModuleWitness
    (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F) :
    witnessRel m mw (compileModuleWitness m mw) := rfl

/-! ## Preservation and reflection theorems -/

theorem preservation (m : MemberlessIR.Module (n + 1) F)
    (mw : Nat → F)
    (h : MemberlessIR.satisfies mw m) :
    FlatIR.satisfies (compileModuleWitness m mw) (compile m) := by
  -- Strategy: prove by induction on body length
  -- Key invariant: compileWitness agrees with MemberlessIR env on vm positions
  -- For each compiled instruction, show it's satisfied by the compiled witness
  sorry

theorem reflection (m : MemberlessIR.Module (n + 1) F)
    (wt : FlatIR.VarId → F)
    (h : FlatIR.satisfies wt (compile m)) :
    MemberlessIR.satisfies (extractWitness m wt) m := by
  sorry

/-! ## Typeclass instances -/

instance PresReflPass (n : Nat) (F : Type) [Field F] :
    PresReflPass (MemberlessIR.instLanguage n F) (FlatIR.Language F) where
  compile := compile
  witnessRel := witnessRel
  preservation := by
    intro mw p hs
    exact ⟨compileModuleWitness p mw, witnessRel_compileModuleWitness p mw, preservation p mw hs⟩
  reflection := by
    intro wt p hs
    use extractWitness p wt
    constructor
    · -- witnessRel: need to show wt = compileModuleWitness p (extractWitness p wt)
      -- This is the round-trip property: compiling witness then extracting gives original
      sorry
    · exact reflection p wt hs

instance Pass (n : Nat) (F : Type) [Field F] :
    Pass (MemberlessIR.instLanguage n F) (FlatIR.Language F) :=
  inferInstance

end MemberlessIRToFlatIR
