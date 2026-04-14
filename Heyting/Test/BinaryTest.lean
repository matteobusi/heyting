import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Languages.R1CS
import Heyting.Backends.FieldBytes
import Heyting.Backends.R1CSBinary
import Heyting.Backends.WitnessBinary

/-!
# Binary serialization tests

Smoke tests for `R1CSBinary` and `WitnessBinary`.

We use `ZMod 97` (a small prime) so `native_decide` / `norm_num` can certify primality and
`FieldBytes` can be instantiated without private axioms.

All tests are `#eval` blocks that throw on failure and print "OK" on success.
-/

namespace BinaryTest

open R1CS FieldBytes R1CSBinary WitnessBinary

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- Minimal `FieldBytes` instance for `ZMod 97`: 1-byte field elements. -/
private instance : FieldBytes (ZMod 97) where
  fieldSize    := 1
  toLeBytes    := fun x => natLeBytes x.val 1
  primeLeBytes := natLeBytes 97 1

/-- A tiny R1CS system: one constraint `(v0 + 1) * (v1) = (v2)`, no public inputs. -/
def tinySys : R1CS.System (ZMod 97) :=
  { constraints := [
      { A := [(.var 0, 1), (.varOne, 1)]
        B := [(.var 1, 1)]
        C := [(.var 2, 1)] }
    ]
    numPublicInputs := 0 }

-- ── .r1cs magic and version ────────────────────────────────────────────────────────────────────
#eval do
  let bytes := systemToBinary (F := ZMod 97) tinySys
  -- magic "r1cs" = 0x72 0x31 0x63 0x73
  if bytes.get! 0 != 0x72 || bytes.get! 1 != 0x31 ||
     bytes.get! 2 != 0x63 || bytes.get! 3 != 0x73 then
    IO.throwServerError "r1cs magic bytes wrong"
  -- version = 1 (LE u32) at bytes 4-7
  if bytes.get! 4 != 1 || bytes.get! 5 != 0 || bytes.get! 6 != 0 || bytes.get! 7 != 0 then
    IO.throwServerError "r1cs version bytes wrong"
  -- nSections = 3 (LE u32) at bytes 8-11
  if bytes.get! 8 != 3 || bytes.get! 9 != 0 || bytes.get! 10 != 0 || bytes.get! 11 != 0 then
    IO.throwServerError "r1cs nSections bytes wrong"
  IO.println "r1cs magic/version/nSections OK"

-- ── .r1cs byte-count sanity ────────────────────────────────────────────────────────────────────
-- fieldSize = 1, nWires = 4 (varOne + var0 + var1 + var2), nConstraints = 1
-- Header section body: 4 + 1 + 4 + 4 + 4 + 4 + 8 + 4 = 33 bytes
-- Header section (with framing): 4 + 8 + 33 = 45 bytes
-- Constraint A: nTerms=2 (4B) + 2*(4+1)B = 4 + 10 = 14 bytes
-- Constraint B: nTerms=1 (4B) + 1*(4+1)B = 4 + 5  = 9 bytes
-- Constraint C: nTerms=1 (4B) + 1*(4+1)B = 4 + 5  = 9 bytes
-- Constraint bytes: 14 + 9 + 9 = 32 bytes
-- Constraints section (with framing): 4 + 8 + 32 = 44 bytes
-- Wire2Label: 4 * 8 = 32 bytes (4 wires × 8B LE u64)
-- Wire2Label section (with framing): 4 + 8 + 32 = 44 bytes
-- File header: 4 (magic) + 4 (version) + 4 (nSections) = 12 bytes
-- Total: 12 + 45 + 44 + 44 = 145 bytes
#eval do
  let bytes := systemToBinary (F := ZMod 97) tinySys
  if bytes.size != 145 then
    IO.throwServerError s!"r1cs byte count wrong: expected 145, got {bytes.size}"
  IO.println "r1cs byte count OK"

-- ── .wtns magic and version ───────────────────────────────────────────────────────────────────
#eval do
  let w : R1CS.Witness (ZMod 97) := fun
    | .varOne  => 1
    | .var 0   => 3
    | .var 1   => 5
    | .var 2   => 15  -- 4 * 5 = 15... but (3+1)*5 = 20 in a real witness; value doesn't matter here
    | _        => 0
  let bytes := witnessToBinary (F := ZMod 97) tinySys w
  -- magic "wtns" = 0x77 0x74 0x6e 0x73
  if bytes.get! 0 != 0x77 || bytes.get! 1 != 0x74 ||
     bytes.get! 2 != 0x6e || bytes.get! 3 != 0x73 then
    IO.throwServerError "wtns magic bytes wrong"
  -- version = 2 (LE u32)
  if bytes.get! 4 != 2 || bytes.get! 5 != 0 || bytes.get! 6 != 0 || bytes.get! 7 != 0 then
    IO.throwServerError "wtns version bytes wrong"
  -- nSections = 2 (LE u32)
  if bytes.get! 8 != 2 || bytes.get! 9 != 0 || bytes.get! 10 != 0 || bytes.get! 11 != 0 then
    IO.throwServerError "wtns nSections bytes wrong"
  IO.println "wtns magic/version/nSections OK"

-- ── .wtns byte-count sanity ───────────────────────────────────────────────────────────────────
-- fieldSize = 1, nWires = 4
-- Header section body: 4 (n8) + 1 (prime) + 4 (nWitness) = 9 bytes
-- Header section (with framing): 4 + 8 + 9 = 21 bytes
-- Data section body: 4 wires × 1 byte = 4 bytes
-- Data section (with framing): 4 + 8 + 4 = 16 bytes
-- File header: 4 + 4 + 4 = 12 bytes
-- Total: 12 + 21 + 16 = 49 bytes
#eval do
  let w : R1CS.Witness (ZMod 97) := fun _ => 0
  let bytes := witnessToBinary (F := ZMod 97) tinySys w
  if bytes.size != 49 then
    IO.throwServerError s!"wtns byte count wrong: expected 49, got {bytes.size}"
  IO.println "wtns byte count OK"

-- ── FieldBytes helpers ────────────────────────────────────────────────────────────────────────
#eval do
  -- natLeBytes: 97 in 2 bytes = [0x61, 0x00]
  let b := natLeBytes 97 2
  if b.get! 0 != 0x61 || b.get! 1 != 0x00 then
    IO.throwServerError s!"natLeBytes wrong: {b.toList}"
  IO.println "natLeBytes OK"

#eval do
  -- u32LE: 0x01020304 → [0x04, 0x03, 0x02, 0x01]
  let b := u32LE 0x01020304
  if b.get! 0 != 0x04 || b.get! 1 != 0x03 || b.get! 2 != 0x02 || b.get! 3 != 0x01 then
    IO.throwServerError s!"u32LE wrong: {b.toList}"
  IO.println "u32LE OK"

#eval do
  -- u64LE: 256 = 0x0000000000000100 → [0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let b := u64LE 256
  if b.get! 0 != 0x00 || b.get! 1 != 0x01 || b.get! 2 != 0x00 then
    IO.throwServerError s!"u64LE wrong: {b.toList}"
  IO.println "u64LE OK"

end BinaryTest
