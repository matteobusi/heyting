import Lean.Data.Json
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Languages.R1CS
import Heyting.Backends.R1CSJSON

namespace R1CSJSONTest

open R1CS Lean R1CSJSON

instance : Fact (Nat.Prime 1993) := ⟨by norm_num⟩

variable {F : Type} [Field F] [Repr F]

def dummySys : R1CS.System F :=
  { constraints := [
      { A := [(.var 1, 1)], B := [(.var 2, 1)], C := [(.var 3, 1)] },
      { A := [(.var 2, 1)], B := [(.varOne, 1)], C := [(.var 4, 1)] }
    ]
    numPublicInputs := 0 }

-- Basic checks using #eval and native_decide (or just run at compile time)

#eval do
  let s := summarize (dummySys (F := ZMod 1993))
  if s.numConstraints != 2 then IO.throwServerError "numConstraints mismatch"
  -- dummySys uses .var 1..4 → numRegVars = 5 (indices 0..4 covered)
  if s.numRegVars != 5 then
    IO.throwServerError s!"numRegVars mismatch: expected 5, got {s.numRegVars}"
  if s.numAuxVars != 0 then IO.throwServerError "numAuxVars mismatch"
  IO.println "Summary stats OK"

#eval do
  let json := systemToJson (dummySys (F := ZMod 1993))
  match json.getObjVal? "numConstraints" with
  | .ok (.num 2) => IO.println "numConstraints JSON OK"
  | _ => IO.throwServerError "numConstraints JSON mismatch"
  -- numWires = 1 + 5 + 0 = 6
  match json.getObjVal? "numWires" with
  | .ok (.num 6) => IO.println "numWires JSON OK"
  | _ => IO.throwServerError "numWires JSON mismatch"
  match json.getObjVal? "numRegVars" with
  | .ok (.num 5) => IO.println "numRegVars JSON OK"
  | _ => IO.throwServerError "numRegVars JSON mismatch"

end R1CSJSONTest