import Heyting.Dialects.Oracle
import Heyting.Dialects.OracleErasure
import Heyting.Parsers.InputJSON
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Dialect.Oracle.Tests

def stream : Stream Nat := { values := [7, 9] }

#guard stream.read == 7
#guard stream.advance.read == 9
#guard stream.advance.advance.read == 0

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

def parsed : Except String (List (ZMod 17)) :=
  InputJSON.parseOracleJson (ZMod 17) "[\"3\", \"-1\"]"

#guard match parsed with
  | .ok [a, b] => a == 3 && b == 16
  | _ => false

def oracleBody : List (Dialect.Stmt OracleErasure.SourceSet ⟨1, 0, 0⟩ Nat) :=
  [.op ⟨2, by simp [OracleErasure.SourceSet,
    LLZK.DialectLowering.WitnessSourceSet]⟩ (.next 4)]

#guard match OracleErasure.lowerBody oracleBody with
  | [.op ⟨2, _⟩ payload] => match payload with
    | .const dest value => dest == 4 && value == 0
    | _ => false
  | _ => false

#check OracleErasure.constrain_body_no_oracle
#check OracleErasure.lowerFunc_fields
#check OracleErasure.lowerStruct_fields
#check OracleErasure.lowerStruct_semantic_fields
#check OracleErasure.lowerModule_struct
#check OracleErasure.evalBody_lowerBody
#check OracleErasure.checkAt_eq_checkProjectedAt

end Dialect.Oracle.Tests
