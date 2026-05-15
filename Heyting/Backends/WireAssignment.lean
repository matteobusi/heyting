import Heyting.Languages.R1CS
import Heyting.Backends.R1CSJSON

/-!
# Wire Assignment

Maps each `R1CS.VarId` to a dense, 0-based wire index suitable for use in
binary formats (Circom `.r1cs`, `.wtns`) and the witness JSON array.

## Wire index layout

Given an R1CS system with `numRegVars` regular wires and `numAuxVars` auxiliary wires:

```
index 0                                         → varOne  (the constant-1 wire)
index 1 .. numRegVars                           → var 0 .. var (numRegVars-1)
index numRegVars+1 .. numRegVars+numAuxVars     → aux 0 .. aux (numAuxVars-1)
```

Total wires = `1 + numRegVars + numAuxVars`.

## Verifiability

The key pure-algebraic correctness property (future verification target):

`encode` is injective — no two distinct `VarId`s receive the same index.

Once proved, a serializer correctness theorem can be stated as:
`R1CS.satisfies w sys ↔ evalColumnVector (toWitnessVector wa w) (toConstraintMatrix wa sys) = 0`

Both are left as future theorem comments to document intent without obligating proofs now.
-/

namespace WireAssignment

variable {F : Type} [Field F]

/-- Wire-index namespace sizes for an R1CS system.
    Carry the two counts so that `encode`/`decode` are definable without
    re-scanning the constraint list. -/
structure Sizes where
  /-- Number of `.var n` slots: wire indices 1 .. numRegVars. -/
  numRegVars : Nat
  /-- Number of `.aux n` slots: wire indices numRegVars+1 .. numRegVars+numAuxVars. -/
  numAuxVars : Nat
  deriving Repr

/-- Total number of wires, including the constant-1 wire at index `0`. -/
def Sizes.numWires (wa : Sizes) : Nat :=
  1 + wa.numRegVars + wa.numAuxVars

/-- Compute `Sizes` from a constraint list by scanning all mentioned `VarId`s. -/
def fromConstraints [Repr F] (constraints : List (R1CS.Constraint F)) : Sizes :=
  { numRegVars := R1CSJSON.countRegVars constraints
    numAuxVars := R1CSJSON.countAuxVars constraints }

/-- Compute `Sizes` from an `R1CS.System`. -/
def fromSystem [Repr F] (sys : R1CS.System F) : Sizes :=
  fromConstraints sys.constraints

/-- Map a `VarId` to its dense wire index.
    - `varOne` → 0
    - `var n`  → n + 1
    - `aux n`  → numRegVars + 1 + n -/
def encode (wa : Sizes) : R1CS.VarId → Nat
  | .varOne => 0
  | .var n  => n + 1
  | .aux n  => wa.numRegVars + 1 + n

/-- Map a dense wire index back to a `VarId`.
    Returns `none` if the index is out of range. -/
def decode (wa : Sizes) (i : Nat) : Option R1CS.VarId :=
  if i == 0 then
    some .varOne
  else if i ≤ wa.numRegVars then
    some (.var (i - 1))
  else if i ≤ wa.numRegVars + wa.numAuxVars then
    some (.aux (i - 1 - wa.numRegVars))
  else
    none

-- Future theorem (encode is injective):
--   theorem encode_injective (wa : Sizes) : Function.Injective (encode wa) := ...
--
-- Future theorem (encode/decode are inverses within range):
--   theorem decode_encode (wa : Sizes) (v : R1CS.VarId)
--       (hv : encode wa v < wa.numWires) : decode wa (encode wa v) = some v := ...

end WireAssignment
