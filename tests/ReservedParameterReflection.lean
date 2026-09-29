import Heyting.Passes.DialectPipeline
import Mathlib.Algebra.Field.Rat

/-!
# Reserved-parameter reflection boundary

The intrinsic typed module permits using a reserved parameter as a field value.
Source initialization fixes that value to zero; emitted constraints now enforce it.
The all-one witness used to satisfy the emitted target despite source unsatisfiability.
This regression checks that canonical initialization closes that counterexample.
-/

namespace Dialect.ReservedParameterReflection

abbrev SourceSet := TypedSourceSemantics.SourceSet

def entry : Fin 1 := ⟨0, by decide⟩

def sourceStruct : StructDef SourceSet 1 entry ℚ where
  name := "reserved"
  members := []
  compute := {
    numParams := 0
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := [.op ⟨3, by decide⟩ (.const 1 1), .op ⟨4, by decide⟩ (.eq 0 1)]
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def source : Module SourceSet 1 ℚ where
  structs
    | ⟨0, _⟩ => sourceStruct

-- The executable compiler accepts the intrinsically certified source.
#guard (Pipeline.compileTypedEntryArtifact source entry).isOk

-- Canonical source observation rejects 0 = 1.
#guard !(TypedSourceSemantics.checkAt source entry [] [])

/-- No finite observation satisfies this source, regardless of list lengths.
Proof sketch: initialization fixes reserved local zero to zero; the body compares
it with a fresh constant one. Inputs and object observations cannot affect either. -/
theorem source_unsatisfied (inputs objects : List ℚ) :
    ¬ TypedSourceSemantics.satisfiesAt source entry inputs objects := by
  simp [TypedSourceSemantics.satisfiesAt, TypedSourceSemantics.checkAt,
    source, sourceStruct, entry, TypedSourceSemantics.evalBody.eq_def,
    TypedSourceSemantics.evalLeaf, TypedSourceSemantics.initialState,
    Felt.applyOp, Felt.evalVal, Felt.destVar, Felt.backendValidBool]

-- The exact compiled R1CS now rejects the all-one assignment, including varOne.
#guard !(match Pipeline.compileTypedEntryArtifact source entry with
  | .error _ => false
  | .ok compiled => compiled.artifact.target.constraints.all fun c ↦
      decide (R1CS.evalLinComb (fun _ ↦ (1 : ℚ)) c.A *
        R1CS.evalLinComb (fun _ ↦ (1 : ℚ)) c.B =
        R1CS.evalLinComb (fun _ ↦ (1 : ℚ)) c.C))

/-- Every compiled artifact for this source is unsatisfiable, including against
arbitrary prover witnesses. Proof sketch: whole-entry reflection would produce a
source observation, contradicting `source_unsatisfied`. -/
theorem target_unsatisfied (compiled : Pipeline.TypedEntryCompilationArtifact source entry)
    (w : R1CS.Witness ℚ) : ¬ R1CS.satisfies w compiled.artifact.target := by
  intro h
  exact source_unsatisfied _ _ (Pipeline.typed_source_of_r1cs source entry compiled w h)

#print axioms Dialect.ReservedParameterReflection.target_unsatisfied

end Dialect.ReservedParameterReflection
