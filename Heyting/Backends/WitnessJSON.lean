/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Heyting.Languages.R1CS
import Heyting.Backends.R1CSJSON
import Heyting.Backends.WireAssignment

/-!
# Witness JSON Serializer

Serializes an `R1CS.Witness F` to a JSON array of field-element strings,
indexed by wire index as defined by `WireAssignment`.

## Format

```json
{
  "numWires": 6,
  "witness": ["1", "42", "7", "0", "0", "0"]
}
```

`witness[0]` is always the value of `varOne` (must be 1 for a valid witness).
`witness[i]` for `1 ≤ i ≤ numRegVars` is the value of `var (i-1)`.
`witness[i]` for `numRegVars + 1 ≤ i ≤ numRegVars + numAuxVars` is the value of
`aux (i - 1 - numRegVars)`.

## Relationship to verification

The witness array is the concrete representation of `R1CS.Witness F`.
The key correctness property of this module is:

  `witnessToArray wa w = witnessToArray wa w'  →  ∀ v, w v = w' v`

i.e., distinct witnesses produce distinct arrays (injectivity on the domain
`{varOne} ∪ {var n | n < wa.numRegVars} ∪ {aux n | n < wa.numAuxVars}`).

This follows from `WireAssignment.encode_injective` (future theorem).
-/

namespace WitnessJSON

open R1CS Lean WireAssignment

variable {F : Type} [Field F] [Repr F]

/-- Convert a witness to a dense array of field elements in wire-index order.
    Entry `i` is `w (decode wa i)`, defaulting to 0 for out-of-range indices. -/
def witnessToArray (wa : WireAssignment.Sizes) (w : R1CS.Witness F) : Array F :=
  (Array.range wa.numWires).map fun i =>
    match decode wa i with
    | some v => w v
    | none   => 0

/-- Serialize a witness to JSON.
    Produces `{ "numWires": n, "witness": ["f0", "f1", ...] }` where
    each string is the `repr` of the field element at that wire index. -/
def witnessToJson (wa : WireAssignment.Sizes) (w : R1CS.Witness F) : Json :=
  let arr := witnessToArray wa w
  Json.mkObj [
    ("numWires", Json.num wa.numWires),
    ("witness",  Json.arr <| arr.map R1CSJSON.fieldToJson)
  ]

/-- Serialize a witness to JSON, deriving the wire assignment from the constraint system. -/
def systemWitnessToJson (sys : R1CS.System F) (w : R1CS.Witness F) : Json :=
  witnessToJson (fromSystem sys) w

/-- Write the witness JSON to a file. -/
def saveWitnessJson (sys : R1CS.System F) (w : R1CS.Witness F) (path : String) : IO Unit := do
  let json := systemWitnessToJson sys w
  IO.FS.writeFile path (Json.pretty json)

end WitnessJSON
