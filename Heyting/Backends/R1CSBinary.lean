import Heyting.Languages.R1CS
import Heyting.Backends.FieldBytes
import Heyting.Backends.R1CSJSON
import Heyting.Backends.WireAssignment

/-!
# R1CS Binary Serializer (Circom `.r1cs` format)

Serializes an `R1CS.System F` to the Circom `.r1cs` binary format as documented at
<https://github.com/iden3/r1csfile>.

## File structure

```
magic       "r1cs" (4 bytes)
version     1      (LE u32)
nSections   3      (LE u32)
[Section 1: Header]
[Section 2: Constraints]
[Section 3: Wire2Label]
```

### Header section (type = 1)

```
fieldSize       LE u32       byte width of one field element
prime           LE bytes     the prime p (fieldSize bytes)
nWires          LE u32       total number of wires (incl. constant 1)
nPubOut         LE u32       0  (we do not separate public outputs)
nPubIn          LE u32       sys.numPublicInputs
nPrvIn          LE u32       nWires - 1 - nPubIn
nLabels         LE u64       nWires (identity wire-to-label map)
mConstraints    LE u32       number of constraints
```

### Constraints section (type = 2)

For each constraint: write A, then B, then C.
Each linear combination: `[nTerms LE u32] [for each term: wireId LE u32 || coeff LE bytes]`.
Terms are sorted by wire index ascending (required by the spec).

### Wire2Label section (type = 3)

`nWires` LE u64 entries: wire `i → label i` (identity map).
-/

namespace R1CSBinary

open FieldBytes R1CS WireAssignment

variable {F : Type} [Field F] [Repr F] [FieldBytes F]

/-! ## Linear-combination serialization -/

/-- Serialize one term `(wireId, coeff)` of a linear combination.
    Wire ID is a LE u32; coefficient is the field element in `fieldSize` bytes. -/
private def termBytes (wa : Sizes) (v : VarId) (c : F) : ByteArray :=
  u32LE (UInt32.ofNat (encode wa v)) ++ toLeBytes c

/-- Serialize a linear combination.
    Sort terms by wire index (ascending), then write `[nTerms][term …]`. -/
private def linCombBytes (wa : Sizes) (lc : LinComb F) : ByteArray :=
  let sorted := lc.toArray.insertionSort (fun a b => encode wa a.1 < encode wa b.1)
  let termsBytes := sorted.foldl (fun acc (v, c) => acc ++ termBytes wa v c) ByteArray.empty
  u32LE (UInt32.ofNat sorted.size) ++ termsBytes

/-- Serialize one constraint (A, B, C). -/
private def constraintBytes (wa : Sizes) (c : Constraint F) : ByteArray :=
  linCombBytes wa c.A ++ linCombBytes wa c.B ++ linCombBytes wa c.C

/-! ## Section builders -/

/-- Build the Header section body (without section framing). -/
private def headerSectionBody (wa : Sizes) (sys : System F) : ByteArray :=
  let nWires   := wa.numWires
  let nPubIn   := sys.numPublicInputs
  let nPrvIn   := if nWires ≥ 1 + nPubIn then nWires - 1 - nPubIn else 0
  u32LE (UInt32.ofNat (fieldSize F))
    ++ primeLeBytes (F := F)
    ++ u32LE (UInt32.ofNat nWires)
    ++ u32LE 0                                  -- nPubOut
    ++ u32LE (UInt32.ofNat nPubIn)
    ++ u32LE (UInt32.ofNat nPrvIn)
    ++ u64LE (UInt64.ofNat nWires)              -- nLabels
    ++ u32LE (UInt32.ofNat sys.constraints.length)

/-- Build the Constraints section body. -/
private def constraintsSectionBody (wa : Sizes) (sys : System F) : ByteArray :=
  sys.constraints.foldl (fun acc c => acc ++ constraintBytes wa c) ByteArray.empty

/-- Build the Wire2Label section body: identity map, wire i → label i. -/
private def wire2LabelSectionBody (wa : Sizes) : ByteArray :=
  (Array.range wa.numWires).foldl (fun acc i => acc ++ u64LE (UInt64.ofNat i)) ByteArray.empty

/-! ## Top-level entry points -/

/-- Serialize `sys` to the Circom `.r1cs` binary format.
    Requires a `FieldBytes F` instance for the concrete field. -/
def systemToBinary (sys : System F) : ByteArray :=
  let wa       := fromSystem sys
  let hdr      := sectionHeader 1 (headerSectionBody wa sys)
  let constrs  := sectionHeader 2 (constraintsSectionBody wa sys)
  let w2l      := sectionHeader 3 (wire2LabelSectionBody wa)
  let magic    := ByteArray.mk #[0x72, 0x31, 0x63, 0x73]  -- "r1cs"
  fileHeader magic 1 3 (hdr ++ constrs ++ w2l)

/-- Write `sys` as a Circom `.r1cs` binary file. -/
def saveR1CSBinary (sys : System F) (path : String) : IO Unit := do
  let bytes := systemToBinary sys
  IO.FS.writeBinFile path bytes

end R1CSBinary
