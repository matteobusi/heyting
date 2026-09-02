import Heyting.Dialects.WitnessExecution
import Heyting.Dialects.R1CSLikePass
import Heyting.Languages.FlatIRChecked
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

namespace Dialect.WitnessExecution.Tests

abbrev F := ZMod 17
abbrev Ctx : Dialect.OpCtx := ⟨1, 0, 0⟩

def base (oracle : List F) : State F := {
  values := fun _ => 0
  objects := fun _ => []
  witness := fun _ => 0
  nextPath := 0
  oracle := { values := oracle }
}

def nextOp : Oracle.Op Ctx F := .next 3

#guard match (oracleHandler F).step nextOp (base [9]) with
  | .ok state => state.values 3 == 9 && state.oracle.cursor == 1
  | _ => false

#guard match (oracleHandler F).step nextOp (base []) with
  | .error .oracleUnderflow => true
  | _ => false

def unequal : FlatIR.Program F := [.assertEq 0 1]
def unequalSeed : FlatIR.Witness F
  | 0 => 2
  | 1 => 3
  | _ => 0

-- Equality does not make transport partial; the independent checker rejects
-- the resulting candidate.
#guard match R1CSLikePass.materializeWitness unequal unequalSeed with
  | .ok result => !FlatIRChecked.checkProgram result unequal
  | .error _ => false

end Dialect.WitnessExecution.Tests
