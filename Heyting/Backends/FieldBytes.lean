import Heyting.Languages.R1CS

/-!
# FieldBytes — little-endian binary serialization for field elements

This module provides a typeclass `FieldBytes` that supplies the two pieces of
information needed to write a field element into the Circom binary formats
(`.r1cs`, `.wtns`):

1. `fieldSize : Nat` — the byte-width of one field element (always a multiple of 8).
2. `toLeBytes : F → ByteArray` — little-endian encoding, padded to exactly `fieldSize` bytes.
3. `primeLeBytes : ByteArray` — the prime `p` itself, LE-encoded in `fieldSize` bytes.

Instances for each supported prime field are in `Heyting/CLI.lean`, alongside the
`private axiom` primality witnesses. They live there (not here) to keep this module
axiom-free.

## Binary writer helpers

`BinaryWriter` collects bytes into a growing `ByteArray` and provides:

- `writeU32LE`, `writeU64LE` — fixed-width little-endian integers.
- `writeBytes`             — raw byte array.
- `sectionHeader`          — 4-byte type + 8-byte size prefix.

The section-framing approach used by both `.r1cs` and `.wtns` is identical, so
all framing logic lives here and is imported by `R1CSBinary` and `WitnessBinary`.
-/

namespace FieldBytes

/-! ## Typeclass -/

set_option linter.dupNamespace false in
/-- Per-field serialization parameters required for Circom binary formats. -/
class FieldBytes (F : Type) where
  /-- Byte width of one field element. Must be a multiple of 8. -/
  fieldSize    : Nat
  /-- Little-endian encoding of a field element, padded to `fieldSize` bytes. -/
  toLeBytes    : F → ByteArray
  /-- Little-endian encoding of the prime `p` in `fieldSize` bytes. -/
  primeLeBytes : ByteArray

export FieldBytes (fieldSize toLeBytes primeLeBytes)

/-! ## Primitive LE writers -/

/-- Write `n` as a 4-byte little-endian `UInt32`. -/
def u32LE (n : UInt32) : ByteArray :=
  let b0 := (n &&& 0xff).toUInt8
  let b1 := ((n >>> 8) &&& 0xff).toUInt8
  let b2 := ((n >>> 16) &&& 0xff).toUInt8
  let b3 := ((n >>> 24) &&& 0xff).toUInt8
  ByteArray.mk #[b0, b1, b2, b3]

/-- Write `n` as an 8-byte little-endian `UInt64`. -/
def u64LE (n : UInt64) : ByteArray :=
  let b0 := (n &&& 0xff).toUInt8
  let b1 := ((n >>> 8) &&& 0xff).toUInt8
  let b2 := ((n >>> 16) &&& 0xff).toUInt8
  let b3 := ((n >>> 24) &&& 0xff).toUInt8
  let b4 := ((n >>> 32) &&& 0xff).toUInt8
  let b5 := ((n >>> 40) &&& 0xff).toUInt8
  let b6 := ((n >>> 48) &&& 0xff).toUInt8
  let b7 := ((n >>> 56) &&& 0xff).toUInt8
  ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]

/-- Encode `n : Nat` as a little-endian `ByteArray` of exactly `width` bytes.
    Truncates silently if `n` overflows (only the low `width` bytes are kept). -/
def natLeBytes (n : Nat) (width : Nat) : ByteArray :=
  let bytes := Array.range width |>.map fun i =>
    UInt8.ofNat ((n >>> (8 * i)) &&& 0xff)
  ByteArray.mk bytes

/-! ## Section framing helpers

Both `.r1cs` and `.wtns` use the same section format:
```
[4 bytes: sectionType LE] [8 bytes: sectionSize LE] [sectionSize bytes: content]
```
-/

/-- Prepend a section header (type + 8-byte size) to `content`. -/
def sectionHeader (sectionType : UInt32) (content : ByteArray) : ByteArray :=
  u32LE sectionType ++ u64LE (UInt64.ofNat content.size) ++ content

/-! ## File-level framing helpers -/

/-- Prepend a magic-number + version + section-count header. -/
def fileHeader (magic : ByteArray) (version : UInt32) (nSections : UInt32)
    (body : ByteArray) : ByteArray :=
  magic ++ u32LE version ++ u32LE nSections ++ body

end FieldBytes
