/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.WitnessCodec
import Heyting.Passes.FlatIRToR1CS

/-!
# Constructive FlatIR to R1CS witness codec

This packages the backend's executable auxiliary-witness construction with the
exact target system and a pointwise satisfaction theorem.
-/

namespace FlatIRToR1CS

open WitnessCodec

variable (F : Type) [Field F]

def compilationArtifact (program : FlatIR.Program F)
    (numPublicInputs : Nat := 0) :
    CompilationArtifact (FlatIR.Language F) (R1CS.Language F) program where
  target := compileProgram F program numPublicInputs
  forward witness := .ok (compileWitness F witness)
  readback := extractWitness F
  witnessRel source target := ∀ v, target (.var v) = source v
  forward_rel := by
    intro source target h
    have htarget : target = compileWitness F source := Except.ok.inj h.symm
    subst target
    intro v
    rfl
  satisfies_iff := by
    intro source target h
    have htarget : target = compileWitness F source := Except.ok.inj h.symm
    subst target
    simpa [compileProgram] using
      (compileWitness_satisfies_iff F source program).symm
  readback_forward := by
    intro source target h
    have htarget : target = compileWitness F source := Except.ok.inj h.symm
    subst target
    exact extract_compileWitness F source

def witnessTransportingPass :
    WitnessTransportingPass (FlatIR.Language F) (R1CS.Language F) where
  compileArtifact program := .ok (compilationArtifact F program)

end FlatIRToR1CS
