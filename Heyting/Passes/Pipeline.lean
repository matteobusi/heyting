/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Core.ComputingLanguage
import Heyting.Languages.StructIR
import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Core.VarIdEncoding
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRCompact
import Heyting.Passes.FlatIRToR1CS

/-!
# Executable Compiler Pipeline

Top-level executable composition used by the CLI.

Current path:

`StructIR -> FlatIR -> FlatIR(compact) -> R1CS`

This file contains only executable composition and witness plumbing. Proofs of
individual pass correctness live in the pass-specific files.
-/

namespace Pipeline

variable {n : Nat} {F : Type} [Field F]

/-! ## Active pipeline

Current executable pipeline:

```
StructIR --[StructIRToFlatIR]--> FlatIR --[FlatIRCompact]--> FlatIR --[FlatIRToR1CS]--> R1CS
```
-/

/-! ## Convenience definitions -/

/-- FlatIR witness induced by shifted witness-slot seeding. -/
def liftStructWitness (witnessBase : Nat) (w : StructIR.Witness F) : FlatIR.Witness F :=
  StructIRToFlatIR.witnessSlotLift witnessBase w

/-! ## Executable FlatIR witness execution

The compiler places all locals below `StructIRToFlatIR.witnessBase m` and all
shifted witness coordinates at or above that base. `liftStructWitness`
correctly fills witness slots from a `StructIR.Witness`, but locals remain `0`.
To produce a
witness that actually satisfies the compiled FlatIR (and hence the R1CS), we
single-pass execute the FlatIR program, materializing each local from
already-known values.

Used only at runtime (CLI). Proof of pass correctness uses the abstract
shifted witness-slot lift, not this executor. -/

/-- Witness construction state: current `FlatIR.Witness F` plus a predicate
    marking which variables have been concretely assigned. -/
private structure FlatWitnessState (F : Type) where
  witness : FlatIR.Witness F
  assigned : Nat → Bool

/-- Overwrite one variable in the witness state and mark it assigned. -/
private def FlatWitnessState.write (s : FlatWitnessState F) (dest : Nat) (val : F) :
    FlatWitnessState F :=
  { witness := fun v => if v = dest then val else s.witness v
    assigned := fun v => if v = dest then true else s.assigned v }

/-- Step the executable FlatIR witness builder. Returns `none` if a division
    by zero is forced during witness materialization. -/
private def stepFlatWitness [DecidableEq F] (s : FlatWitnessState F)
    (instr : FlatIR.Instr F) : Option (FlatWitnessState F) :=
  match instr with
  | .assignAdd dest src1 src2 =>
      some <| s.write dest (s.witness src1 + s.witness src2)
  | .assignSub dest src1 src2 =>
      some <| s.write dest (s.witness src1 - s.witness src2)
  | .assignMul dest src1 src2 =>
      some <| s.write dest (s.witness src1 * s.witness src2)
  | .assignDiv dest src1 src2 =>
      if s.witness src2 = 0 then
        none
      else
        some <| s.write dest (s.witness src1 * (s.witness src2)⁻¹)
  | .assignNeg dest src =>
      some <| s.write dest (-(s.witness src))
  | .assignConst dest c =>
      some <| s.write dest c
  | .assertEq src1 src2 =>
      -- Compiled materialization equalities always use `src1` as the local to
      -- fill from `src2` (main-param bindings, `readMember`). For ordinary
      -- `constrainEq`, both sides are already assigned. When both flags are
      -- false, prefer writing `src1` from `src2`.
      match s.assigned src1, s.assigned src2 with
      | false, true  => some <| s.write src1 (s.witness src2)
      | true,  false => some <| s.write src2 (s.witness src1)
      | false, false => some <| s.write src1 (s.witness src2)
      | true,  true  => some s

/-- Execute the compiled FlatIR program from a `StructIR.Witness`, producing a
    `FlatIR.Witness` with all locals materialized. -/
private def buildFlatWitness [DecidableEq F] (m : StructIR.Module (n + 1) F)
    (w : StructIR.Witness F) : Option (FlatIR.Witness F) := do
  let prog := StructIRToFlatIR.compileProgram m
  let wBase := StructIRToFlatIR.witnessBase m
  let s ← List.foldlM (fun s instr => stepFlatWitness (F := F) s instr)
    ({ witness := liftStructWitness wBase w, assigned := fun _ => false } : FlatWitnessState F) prog
  pure s.witness

/-- Compile StructIR program through direct StructIR -> FlatIR -> R1CS pipeline. -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  let flat := StructIRToFlatIR.compileProgram m
  let compact := FlatIRCompact.compileProgram flat
  FlatIRToR1CS.compileProgram F compact numPub

/-- Compile StructIR to FlatIR. -/
def compileFlatIR (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  FlatIRCompact.compileProgram (StructIRToFlatIR.compileProgram m)

/-- `R1CS.satisfies` ignores `numPublicInputs`, so compile variants with same constraints agree. -/
theorem satisfies_compileProgram_numPublicInputs_iff
    (w : R1CS.Witness F) (p : FlatIR.Program F) (numPublicInputs : Nat) :
    R1CS.satisfies w (FlatIRToR1CS.compileProgram F p numPublicInputs) ↔
      R1CS.satisfies w (FlatIRToR1CS.compileProgram F p) := by
  rfl

/-- Runtime witness compaction matching `FlatIRCompact.compileProgram`. -/
private def compactFlatWitness (p : FlatIR.Program F) (w : FlatIR.Witness F) : FlatIR.Witness F :=
  fun v =>
    match (FlatIRCompact.denseVars p)[v]? with
    | some src => w src
    | none => 0

/-- Pure correctness pipeline before CLI-only `numPublicInputs` annotation. -/
private def correctnessPass : PresReflPass (StructIR.Language n F) (R1CS.Language F) :=
  let pass1 : PresReflPass (StructIR.Language n F) (FlatIR.Language F) := inferInstance
  let pass12 : PresReflPass (FlatIR.Language F) (R1CS.Language F) :=
    PresReflPass.compose
      (pass1 := FlatIRCompact.CorrectPass (F := F))
      (pass2 := FlatIRToR1CS.CorrectPass (F := F))
  PresReflPass.compose
    (pass1 := pass1)
    (pass2 := pass12)

/-- High-level direct pipeline is fully proved as `PresReflPass`. -/
instance CorrectPass [DecidableEq F] :
    PresReflPass (StructIR.Language n F) (R1CS.Language F) where
  compile := compileProgram (F := F) (n := n)
  witnessRel := (correctnessPass (F := F) (n := n)).witnessRel
  preservation := by
    intro ws m hsat
    obtain ⟨wt, hwrel, hsat'⟩ := (correctnessPass (F := F) (n := n)).preservation ws m hsat
    refine ⟨wt, hwrel, ?_⟩
    let numPublicInputs :=
      (m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).members.countP (·.isPublic)
    exact (satisfies_compileProgram_numPublicInputs_iff (F := F) wt
      (compileFlatIR (F := F) (n := n) m) numPublicInputs).mpr hsat'
  reflection := by
    intro wt m hsat
    let numPublicInputs :=
      (m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).members.countP (·.isPublic)
    have hsat' :
        R1CS.satisfies wt (FlatIRToR1CS.compileProgram F (compileFlatIR (F := F) (n := n) m)) :=
      (satisfies_compileProgram_numPublicInputs_iff (F := F) wt
        (compileFlatIR (F := F) (n := n) m) numPublicInputs).mp hsat
    exact (correctnessPass (F := F) (n := n)).reflection wt m hsat'

/-- End-to-end executable witness generation through StructIR and FlatIR witnesses. -/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.bind fun ws =>
    buildFlatWitness (F := F) m ws |>.map fun wt =>
      let compactW := compactFlatWitness (StructIRToFlatIR.compileProgram m) wt
      FlatIRToR1CS.compileWitness (F := F) compactW

end Pipeline
