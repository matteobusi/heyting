import Heyting.Passes.FlatIRWitnessCodec
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

namespace FlatIRWitnessCodec.Tests

abbrev F := ZMod 17

def program : FlatIR.Program F :=
  [.assignMul 2 0 1, .assertEq 2 3]

def source : FlatIR.Witness F
  | 0 => 3
  | 1 => 4
  | 2 => 12
  | 3 => 12
  | _ => 0

def artifact := FlatIRToR1CS.compilationArtifact F program 1

example : artifact.forward source = .ok (FlatIRToR1CS.compileWitness F source) := rfl

example : artifact.readback (FlatIRToR1CS.compileWitness F source) = source := by
  exact FlatIRToR1CS.extract_compileWitness F source

example :
    FlatIR.satisfies source program ↔
      R1CS.satisfies (FlatIRToR1CS.compileWitness F source) artifact.target := by
  exact artifact.satisfies_iff source _ rfl

end FlatIRWitnessCodec.Tests
