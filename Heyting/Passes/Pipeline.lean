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
import Heyting.Passes.FlatIRToR1CS

/-!
# Executable Compiler Pipeline

Top-level executable composition used by the CLI.

Current path:

`StructIR -> FlatIR -> R1CS`

This file contains only executable composition and witness plumbing. Proofs of
individual pass correctness live in the pass-specific files.
-/

namespace Pipeline

variable {n : Nat} {F : Type} [Field F]

/-! ## Direct pipeline

Current executable pipeline:

```
StructIR --[StructIRToFlatIR]--> FlatIR --[FlatIRToR1CS]--> R1CS
```

Old intermediate-language pipeline removed from build until those files return.
-/

/-! ## Convenience definitions -/

/-- FlatIR witness induced by decode-seeded StructIR witness semantics. -/
def liftStructWitness (w : StructIR.Witness F) : FlatIR.Witness F :=
  fun v => w (VarIdEncoding.decode v)

/-- Compile StructIR program through direct StructIR -> FlatIR -> R1CS pipeline. -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  FlatIRToR1CS.compileProgram F (StructIRToFlatIR.compileProgram m) numPub

/-- Compile StructIR to FlatIR. -/
def compileFlatIR (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  StructIRToFlatIR.compileProgram m

/-- `R1CS.satisfies` ignores `numPublicInputs`, so compile variants with same constraints agree. -/
theorem satisfies_compileProgram_numPublicInputs_iff
    (w : R1CS.Witness F) (p : FlatIR.Program F) (numPublicInputs : Nat) :
    R1CS.satisfies w (FlatIRToR1CS.compileProgram F p numPublicInputs) ↔
      R1CS.satisfies w (FlatIRToR1CS.compileProgram F p) := by
  rfl

/-- High-level direct pipeline reflects satisfiability from R1CS back to StructIR. -/
instance CorrectReflectingPass [DecidableEq F] :
    ReflectingPass (StructIR.Language n F) (R1CS.Language F) where
  compile := compileProgram (F := F) (n := n)
  witnessRel m ws wt :=
    let pass2pr : PresReflPass (FlatIR.Language F) (R1CS.Language F) :=
      FlatIRToR1CS.CorrectPass (F := F)
    let pass2 : ReflectingPass (FlatIR.Language F) (R1CS.Language F) :=
      { toPass := pass2pr.toPass
        reflection := pass2pr.reflection }
    let pass : ReflectingPass (StructIR.Language n F) (R1CS.Language F) :=
      ReflectingPass.compose
        (pass1 := StructIRToFlatIR.CorrectReflectingPass (F := F) (n := n))
        (pass2 := pass2)
    pass.witnessRel m ws wt
  reflection := by
    intro wt m hsat
    let pass2pr : PresReflPass (FlatIR.Language F) (R1CS.Language F) :=
      FlatIRToR1CS.CorrectPass (F := F)
    let pass2 : ReflectingPass (FlatIR.Language F) (R1CS.Language F) :=
      { toPass := pass2pr.toPass
        reflection := pass2pr.reflection }
    let pass : ReflectingPass (StructIR.Language n F) (R1CS.Language F) :=
      ReflectingPass.compose
        (pass1 := StructIRToFlatIR.CorrectReflectingPass (F := F) (n := n))
        (pass2 := pass2)
    have hsat' : R1CS.satisfies wt
        (FlatIRToR1CS.compileProgram F (StructIRToFlatIR.compileProgram m)) :=
      (satisfies_compileProgram_numPublicInputs_iff (F := F) wt
        (StructIRToFlatIR.compileProgram m)
        ((m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).members.countP (·.isPublic))).mp hsat
    have hsat'' : R1CS.satisfies wt (pass.compile m) := by
      simpa [pass, pass2, pass2pr, compileProgram] using hsat'
    simpa [pass, pass2, pass2pr, compileProgram] using pass.reflection wt m hsat''

/-- End-to-end executable witness generation through StructIR and FlatIR witnesses. -/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map fun ws =>
    FlatIRToR1CS.compileWitness (F := F) (liftStructWitness ws)

end Pipeline
