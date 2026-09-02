import Heyting.Passes.DialectPipeline
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

namespace Dialect.Pipeline.Tests

abbrev F := ZMod 17

def program : FlatIR.Program F := [.assignMul 4 0 1, .assertEq 4 3]

def artifact : EntryCompilationArtifact F := {
  program
  numParams := 2
  computeParams := 2
  paramOffset := 0
  witnessSpan := 2
  numPublicInputs := 0
  backend := FlatIRToR1CS.compilationArtifact F program
}

def satisfying : SourceWitness F := { inputs := [3, 4], objects := [0, 12] }
def unsatisfying : SourceWitness F := { inputs := [3, 5], objects := [0, 12] }

example : checkSource artifact satisfying = true := by native_decide

-- Equality failure is satisfaction failure, not transport failure.
#guard match artifact.forward unsatisfying with
  | .ok _ => true
  | .error _ => false

example (source : SourceWitness F) (target : R1CS.Witness F)
    (h : artifact.forward source = .ok target) :
    Source.satisfies source artifact ↔ R1CS.satisfies target artifact.target :=
  pipeline_witness_iff artifact source target h

example (source : SourceWitness F) (target : R1CS.Witness F)
    (h : artifact.forward source = .ok target) : artifact.readback target = source :=
  pipeline_readback artifact source target h

example {n : Nat}
    (module : Dialect.Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (source : SourceWitness F) :
    checkTypedSource module entry source = true ↔
      TypedSourceSatisfies module entry source :=
  checkTypedSource_true_iff module entry source

example {n : Nat}
    (module : Dialect.Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F)
    (hcanonical : compiled.artifact.CanonicalSource source) :
    checkTypedSource module entry source = checkSource compiled.artifact source :=
  typed_source_check_eq_artifact module entry compiled source hcanonical

example {n : Nat}
    (module : Dialect.Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F) (target : R1CS.Witness F)
    (hforward : compiled.artifact.forward source = .ok target) :
    TypedSourceSatisfies module entry source ↔
      R1CS.satisfies target compiled.artifact.target :=
  typed_source_r1cs_iff module entry compiled source target hforward

end Dialect.Pipeline.Tests

#print axioms Dialect.Pipeline.checkSource_true_iff
#print axioms Dialect.Pipeline.pipeline_witness_iff
#print axioms Dialect.Pipeline.generated_witness_iff
#print axioms Dialect.Pipeline.pipeline_readback
#print axioms Dialect.Pipeline.typed_source_artifact_iff
#print axioms Dialect.Pipeline.typed_source_check_eq_artifact
#print axioms Dialect.Pipeline.generateSourceWitness_canonical
#print axioms Dialect.Pipeline.generated_typed_source_check_eq_artifact
#print axioms Dialect.Pipeline.typed_source_r1cs_iff
#print axioms Dialect.Pipeline.generated_typed_source_r1cs_iff
#print axioms Dialect.Pipeline.typed_pipeline_readback
