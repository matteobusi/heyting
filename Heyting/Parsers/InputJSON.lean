/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Mathlib.Algebra.Field.Basic

/-!
# Input JSON Parsing

Parses a public-input JSON file of the form `{"signal_name": "value", ...}` into a
positional `List F` suitable for `StructIR.computeWitness` / `Pipeline.pipelineWitness`.

## Signal-name convention

The `@compute` function of the main LLZK struct has params `[self, a, b, ...]` at
positions 0, 1, 2, …  Position 0 (`%self`) represents the circuit struct itself and
should be skipped; the remaining names are the user-visible signal names.

## Error policy

- Unknown key in JSON (does not match any param name) → error.
- Param absent from JSON → default value `0` (matches circom convention for missing inputs).
- Value that cannot be parsed as an integer → error.
-/

namespace InputJSON

open Lean

/-! ## Field-element parsing -/

/-- Parse a decimal string into a field element.

    Accepts non-negative integers (`"123"`) and negatives (`"-5"`).
    Rejects strings that are not valid integers. -/
def parseFieldElem (F : Type) [Field F] [IntCast F] (s : String) : Except String F :=
  match s.toInt? with
  | some i => .ok (IntCast.intCast i : F)
  | none   => .error s!"cannot parse field element: {repr s} (expected a decimal integer)"

/-! ## JSON input parsing -/

/-- Parse a JSON object `{"name": "value", ...}` into a positional `List F`.

    `paramNames` is the list of signal names in position order (index 0, 1, …),
    typically obtained from the main struct's `@compute` parameter list with the
    leading `"self"` entry already removed.

    For each name in `paramNames`:
    - If the JSON object contains an entry for it, parse the value string → `F`.
    - If the JSON object does not contain an entry, default to `0`.

    Returns an error if:
    - `jsonStr` is not valid JSON.
    - The top-level JSON value is not an object.
    - A JSON value is not a string.
    - A value string cannot be parsed as a decimal integer.
    - A key in the JSON object does not appear in `paramNames`. -/
def parseInputsJson (F : Type) [Field F] [IntCast F]
    (paramNames : List String) (jsonStr : String) : Except String (List F) := do
  -- 1. Parse JSON text
  let json ← Json.parse jsonStr
  -- 2. Extract the top-level object
  let obj ← json.getObj?
  -- 3. Check for unknown keys (keys not present in paramNames)
  let nameSet : Std.HashSet String := Std.HashSet.insertMany ∅ paramNames
  let unknown := (obj.toList.map Prod.fst).filter fun k => !nameSet.contains k
  if let k :: _ := unknown then
    throw s!"unknown signal name in input JSON: {repr k}"
  -- 4. For each param, look up in object (default 0) then parse
  paramNames.mapM fun name =>
    match obj.get? name with
    | none =>
      -- Missing entry → default to 0
      .ok (0 : F)
    | some jval =>
      match Json.getStr? jval with
      | .error _ => .error s!"value for signal {repr name} must be a JSON string, got: {jval}"
      | .ok s    => parseFieldElem F s

end InputJSON
