import Lean.Data.Json
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Backends.InputJSON

/-!
# Input JSON Test

Unit tests for `InputJSON.parseFieldElem` and `InputJSON.parseInputsJson`.

Uses `ZMod 1993` as the test field (small prime, decidable).
-/

namespace InputJSONTest

section
set_option linter.style.setOption false
set_option linter.style.nativeDecide false

instance : Fact (Nat.Prime 1993) := ⟨by native_decide⟩
abbrev F := ZMod 1993

open InputJSON

/-! ## parseFieldElem tests -/

-- Non-negative integer parses correctly
#eval do
  match parseFieldElem F "42" with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok v =>
    if v != (42 : F) then IO.throwServerError s!"expected 42, got {repr v}"
    IO.println "parseFieldElem '42' OK"

-- Negative integer parses correctly
#eval do
  match parseFieldElem F "-1" with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok v =>
    if v != (-1 : F) then IO.throwServerError s!"expected -1, got {repr v}"
    IO.println "parseFieldElem '-1' OK"

-- Zero parses correctly
#eval do
  match parseFieldElem F "0" with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok v =>
    if v != (0 : F) then IO.throwServerError s!"expected 0, got {repr v}"
    IO.println "parseFieldElem '0' OK"

-- Non-integer string returns an error
#eval do
  match parseFieldElem F "abc" with
  | .ok v    => IO.throwServerError s!"expected error, got Ok: {repr v}"
  | .error _ => IO.println "parseFieldElem 'abc' → error OK"

-- Empty string returns an error
#eval do
  match parseFieldElem F "" with
  | .ok v    => IO.throwServerError s!"expected error, got Ok: {repr v}"
  | .error _ => IO.println "parseFieldElem '' → error OK"

/-! ## parseInputsJson tests -/

-- Valid JSON with correct signal names → correct list
#eval do
  let params := ["a", "b"]
  let json := "{\"a\": \"2\", \"b\": \"3\"}"
  match parseInputsJson F params json with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok vals =>
    if vals != [(2 : F), (3 : F)] then
      IO.throwServerError s!"expected [2, 3], got {vals.map repr}"
    IO.println "parseInputsJson valid input OK"

-- Missing signal defaults to 0
#eval do
  let params := ["a", "b"]
  let json := "{\"a\": \"5\"}"
  match parseInputsJson F params json with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok vals =>
    if vals != [(5 : F), (0 : F)] then
      IO.throwServerError s!"expected [5, 0], got {vals.map repr}"
    IO.println "parseInputsJson missing signal defaults to 0 OK"

-- Empty params → empty list (even with extra JSON keys → those are unknown → error)
#eval do
  let params : List String := []
  let json := "{}"
  match parseInputsJson F params json with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok vals =>
    if !vals.isEmpty then IO.throwServerError s!"expected [], got {vals.map repr}"
    IO.println "parseInputsJson empty params OK"

-- Unknown key in JSON → error
#eval do
  let params := ["a"]
  let json := "{\"a\": \"1\", \"z\": \"9\"}"
  match parseInputsJson F params json with
  | .ok vals => IO.throwServerError s!"expected error for unknown key, got Ok: {vals.map repr}"
  | .error _ => IO.println "parseInputsJson unknown key → error OK"

-- Bad value (non-integer string) → error
#eval do
  let params := ["a"]
  let json := "{\"a\": \"bad\"}"
  match parseInputsJson F params json with
  | .ok vals => IO.throwServerError s!"expected error for bad value, got Ok: {vals.map repr}"
  | .error _ => IO.println "parseInputsJson bad value → error OK"

-- Non-string JSON value → error
#eval do
  let params := ["a"]
  let json := "{\"a\": 42}"
  match parseInputsJson F params json with
  | .ok vals => IO.throwServerError s!"expected error for non-string value, got Ok: {vals.map repr}"
  | .error _ => IO.println "parseInputsJson non-string value → error OK"

-- Invalid JSON → error
#eval do
  let params := ["a"]
  let json := "not json at all"
  match parseInputsJson F params json with
  | .ok vals => IO.throwServerError s!"expected error for invalid JSON, got Ok: {vals.map repr}"
  | .error _ => IO.println "parseInputsJson invalid JSON → error OK"

-- Negative value in field
#eval do
  let params := ["x"]
  let json := "{\"x\": \"-7\"}"
  match parseInputsJson F params json with
  | .error e => IO.throwServerError s!"expected Ok, got error: {e}"
  | .ok vals =>
    if vals != [(-7 : F)] then
      IO.throwServerError s!"expected [-7], got {vals.map repr}"
    IO.println "parseInputsJson negative value OK"

end

end InputJSONTest
