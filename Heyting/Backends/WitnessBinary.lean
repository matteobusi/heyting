/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Languages.R1CS
import Heyting.Backends.FieldBytes
import Heyting.Backends.WireAssignment
import Heyting.Backends.WitnessJSON

/-!
# Witness Binary Serializer (Circom `.wtns` format)

Serializes an `R1CS.Witness F` to the Circom `.wtns` binary format as used by
snarkjs (`wtns_utils.js`).

## File structure

```
magic       "wtns" (4 bytes)
version     2      (LE u32)
nSections   2      (LE u32)
[Section 1: Header]
[Section 2: Data]
```

### Header section (type = 1)

```
n8          LE u32       byte width of one field element (= fieldSize F)
prime       LE bytes     the prime p (n8 bytes)
nWitness    LE u32       total number of witness entries (= numWires)
```

### Data section (type = 2)

`nWitness × n8` bytes — dense array of field elements in wire-index order,
same order as `WitnessJSON.witnessToArray`.
-/

namespace WitnessBinary

open FieldBytes R1CS WireAssignment WitnessJSON

variable {F : Type} [Field F] [Repr F] [FieldBytes F]

/-! ## Section builders -/

/-- Build the Header section body (without section framing). -/
private def headerSectionBody (wa : Sizes) : ByteArray :=
  u32LE (UInt32.ofNat (fieldSize F))
    ++ primeLeBytes (F := F)
    ++ u32LE (UInt32.ofNat wa.numWires)

/-- Build the Data section body: field elements in wire-index order. -/
private def dataSectionBody (wa : Sizes) (w : Witness F) : ByteArray :=
  let arr := witnessToArray wa w
  arr.foldl (fun acc fe => acc ++ toLeBytes fe) ByteArray.empty

/-! ## Top-level entry points -/

/-- Serialize `w` (relative to `sys`) to the Circom `.wtns` binary format. -/
def witnessToBinary (sys : System F) (w : Witness F) : ByteArray :=
  let wa    := fromSystem sys
  let hdr   := sectionHeader 1 (headerSectionBody (F := F) wa)
  let dat   := sectionHeader 2 (dataSectionBody wa w)
  let magic := ByteArray.mk #[0x77, 0x74, 0x6e, 0x73]  -- "wtns"
  fileHeader magic 2 2 (hdr ++ dat)

/-- Write a Circom `.wtns` binary file. -/
def saveWitnessBinary (sys : System F) (w : Witness F) (path : String) : IO Unit := do
  let bytes := witnessToBinary sys w
  IO.FS.writeBinFile path bytes

end WitnessBinary
