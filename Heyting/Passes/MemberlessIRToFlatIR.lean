/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Languages.MemberlessIR
import Heyting.Languages.FlatIR

/-!
# MemberlessIR → FlatIR Pass

Inlines all cross-function calls and lowers felt-arithmetic operations to a
flat list of `FlatIR` instructions.

## Concerns handled by this pass

1. **Call inlining**: `MemberlessIR.Stmt.call` is replaced by the callee body
   with arguments substituted into a fresh variable map.
2. **Param absorption**: felt parameters (`0..numParams-1`) are absorbed into
   the flat variable namespace via the initial `VarMap`.

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
| `call target args` | *(recurse on callee body)* | none |

## Witness translation

### Forward (`compileWitness`)

Mirrors `compileConstrainBody`, threading both the `FlatIR` accumulator and the
`MemberlessIR` local environment (to track argument values for inlined calls).

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

/-- Compile a `MemberlessIR` body (with inline call expansion) to `FlatIR`.

    Returns `(instructions, next')` where `next'` is the next available
    `FlatIR.VarId` after all allocations in this body.

    Termination: structural on `(i, stmts.length)` — callee `j < i`. -/
def compileBody (m : MemberlessIR.Module n F) (i : Fin n) (vm : VarMap) (next : Nat)
    (stmts : List (MemberlessIR.Stmt n i F)) :
    List (FlatIR.Instr F) × Nat :=
  match stmts with
  | [] => ([], next)
  | stmt :: rest =>
    let (instrs, vm', next') :=
      match stmt with
      | .feltAdd dest src1 src2 =>
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
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let calleeVm : VarMap := fun param =>
          match args[param]? with
          | some arg => vm arg
          | none     => 0  -- unused params default to flat var 0
        let (callInstrs, next'') := compileBody m j calleeVm next (m j).body
        (callInstrs, vm, next'')
    let (restInstrs, finalNext) := compileBody m i vm' next' rest
    (instrs ++ restInstrs, finalNext)
  termination_by (i, stmts.length)

/-- Compile a whole `MemberlessIR.Module` to a `FlatIR.Program`.

    The main function is at index `n`.  Its parameters occupy FlatIR slots
    `0..numParams-1` via the initial `VarMap` (identity on `0..numParams-1`).
    The counter starts at `numParams` (or 1 if `numParams = 0`). -/
def compile (m : MemberlessIR.Module (n + 1) F) : FlatIR.Program F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numParams := (m mainIdx).numParams
  -- Identity map on 0..numParams-1; everything else maps to 0
  let initVm : VarMap := fun v => if v < numParams then v else 0
  let initNext := max numParams 1
  (compileBody m mainIdx initVm initNext (m mainIdx).body).1

/-! ## Witness translation (forward) -/

/-- Build the `FlatIR` witness from a `MemberlessIR` witness `mw`.

    Mirrors `compileBody`, threading a `LocalEnv` to track argument values
    through inlined calls, and an accumulator for the `FlatIR` witness. -/
def compileWitness (m : MemberlessIR.Module n F)
    (mw : Nat → F)
    (i : Fin n) (vm : VarMap) (next : Nat)
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
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let calleeEnv : MemberlessIR.LocalEnv F := fun param =>
          match args[param]? with
          | some arg => env arg
          | none     => 0
        let calleeVm : VarMap := fun param =>
          match args[param]? with
          | some arg => vm arg
          | none     => 0
        let (acc', next') := compileWitness m mw j calleeVm next calleeEnv
          (m j).body acc
        (env, vm, next', acc')
    compileWitness m mw i vm' next' env' rest acc'
  termination_by (i, stmts.length)

/-- Build the top-level `FlatIR` witness from a `MemberlessIR` witness `mw`.

    The main function's initial env is `mw` itself (seeded from the MemberlessIR
    witness).  The initial FlatIR accumulator agrees with `mw` on param slots. -/
def compileModuleWitness (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F) :
    FlatIR.VarId → F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numParams := (m mainIdx).numParams
  let initVm : VarMap := fun v => if v < numParams then v else 0
  let initNext := max numParams 1
  -- Initial FlatIR accumulator: param slots agree with mw
  let initAcc : FlatIR.VarId → F := fun k => if k < numParams then mw k else 0
  (compileWitness m mw mainIdx initVm initNext mw (m mainIdx).body initAcc).1

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
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let calleeVm : VarMap := fun param =>
          match args[param]? with
          | some arg => vm arg
          | none     => 0
        let (_, next'') := buildVarMap m j calleeVm next (m j).body
        (vm, next'')
    buildVarMap m i vm' next' rest
  termination_by (i, stmts.length)

/-- Extract a `MemberlessIR` witness from a `FlatIR` witness `wt`.

    Each MemberlessIR local variable `v` maps to `wt (vm v)` where `vm` is the
    variable map produced by `buildVarMap`. -/
def extractWitness (m : MemberlessIR.Module (n + 1) F) (wt : FlatIR.VarId → F) :
    Nat → F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numParams := (m mainIdx).numParams
  let initVm : VarMap := fun v => if v < numParams then v else 0
  let initNext := max numParams 1
  let (finalVm, _) := buildVarMap m mainIdx initVm initNext (m mainIdx).body
  fun v => wt (finalVm v)

/-! ## Witness relation -/

/-- The witness relation: `wt` is related to `mw` if `wt = compileModuleWitness m mw`
    (i.e., `wt` is the FlatIR witness produced by forward translation from `mw`). -/
def witnessRel (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F)
    (wt : FlatIR.VarId → F) : Prop :=
  wt = compileModuleWitness m mw

end MemberlessIRToFlatIR
