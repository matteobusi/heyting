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
    ] }

-- Basic checks using #eval and native_decide (or just run at compile time)

#eval do
  let s := summarize (dummySys (F := ZMod 1993))
  if s.numConstraints != 2 then IO.throwServerError "numConstraints mismatch"
  if s.numVars != 5 then IO.throwServerError s!"numVars mismatch: expected 5, got {s.numVars}"
  if s.numAuxVars != 0 then IO.throwServerError "numAuxVars mismatch"
  IO.println "Summary stats OK"

#eval do
  let json := systemToJson (dummySys (F := ZMod 1993))
  match json.getObjVal? "numConstraints" with
  | .ok (.num 2) => IO.println "numConstraints JSON OK"
  | _ => IO.throwServerError "numConstraints JSON mismatch"
  match json.getObjVal? "numVars" with
  | .ok (.num 5) => IO.println "numVars JSON OK"
  | _ => IO.throwServerError "numVars JSON mismatch"

end R1CSJSONTest