import Heyting.Dialects.R1CSLikePass
import Mathlib.Algebra.Field.Rat

namespace Dialect.R1CSLikePass.Tests

open Dialect

abbrev F := ℚ

def ix0 : Fin 1 := ⟨0, by omega⟩

def sourceStruct : StructDef SourceSet 1 ix0 F where
  name := "entry"
  members := []
  compute := {
    numParams := 2
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 2
    body := [
      .op ⟨0, by simp [SourceSet, CallPass.TargetSet]⟩ (.add 2 0 1),
      .op ⟨0, by simp [SourceSet, CallPass.TargetSet]⟩ (.const 3 5),
      .op ⟨1, by simp [SourceSet, CallPass.TargetSet]⟩ (.eq 2 3)]
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def sourceModule : Module SourceSet 1 F where
  structs
    | ⟨0, _⟩ => sourceStruct

def entry : Fin 1 := ix0

def loweredModule : Module TargetSet 1 F :=
  (dialectPass F).lowerModule sourceModule

#guard (loweredModule.structs entry).constrain.body.length == 3
#guard (R1CSLike.compileConstraints
  (loweredModule.structs entry).constrain.body).length == 3
#guard (compileEntryConstrain F loweredModule entry).constraints.length == 3

/-- Terminal codec preserves satisfaction of the selected leaf body. -/
example (w : R1CSLike.Witness F) :
    R1CS.satisfies (R1CSLike.compileWitness w)
        (R1CSLike.toR1CS (loweredModule.structs entry).constrain.body) ↔
      R1CSLike.satisfies w (loweredModule.structs entry).constrain.body :=
  R1CSLike.compileWitness_satisfies_iff w
    (loweredModule.structs entry).constrain.body

example (w : R1CSLike.Witness F) :
    (R1CSLike.compilationArtifact
      (.mk (loweredModule.structs entry).constrain.body)).readback
        (R1CSLike.compileWitness w) = w :=
  R1CSLike.readback_compileWitness w

example (env : LocalVar → F) :
    evalFuncConstrain (targetHandlers F) loweredModule
        (loweredModule.structs entry).constrain env ↔
      evalFuncConstrain (sourceHandlers F) sourceModule
        (sourceModule.structs entry).constrain env :=
  (moduleConstraintPass F).constrain_iff sourceModule entry env

end Dialect.R1CSLikePass.Tests

-- Reflection covers arbitrary target assignments, including unconstrained auxiliaries.
example {F : Type} [Field F] (program : Dialect.R1CSLike.Program F)
    (target : R1CS.Witness F)
    (h : R1CS.satisfies target (Dialect.R1CSLike.compileProgram program)) :
    ∃ source, (∀ v, target (.var v) = source v) ∧
      (Dialect.R1CSLike.Language F).satisfies source program :=
  (Dialect.R1CSLike.CorrectPass (F := F)).reflection target program h

#print axioms Dialect.R1CSLike.CorrectPass
#print axioms Dialect.R1CSLike.toR1CS_reflection
#print axioms Dialect.R1CSLike.compileWitness_satisfies_iff
