/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

/-!
# Object-coordinate encoding

Bijective encoding between concrete `(instance path, member)` pairs and natural
numbers.

This encoding is used by executable passes to represent witness coordinates as
flat register ids while keeping a proven inverse pair `encode`/`decode`.
-/

namespace VarIdEncoding

abbrev Coordinate := List Nat × Nat

/-- Encode an object coordinate `(path, member)` as a natural number. -/
def encode : Coordinate → Nat
  | (path, member) => Nat.pair (Equiv.listNatEquivNat path) member

/-- Decode a natural number into an object coordinate `(path, member)`. -/
def decode (k : Nat) : Coordinate :=
  let p := Nat.unpair k
  (Equiv.listNatEquivNat.symm p.1, p.2)

/-- `decode` is a left inverse of `encode`. -/
theorem decode_encode (v : Coordinate) : decode (encode v) = v := by
  rcases v with ⟨path, member⟩
  simp [encode, decode, Nat.unpair_pair]

/-- `encode` is a left inverse of `decode`. -/
theorem encode_decode (k : Nat) : encode (decode k) = k := by
  simp [encode, decode, Nat.pair_unpair]

/-- `encode` is injective because `decode` is its left inverse. -/
theorem encode_injective : Function.Injective encode := by
  intro v1 v2 h
  have h1 : decode (encode v1) = decode (encode v2) := by rw [h]
  simpa [decode_encode] using h1

/-- `decode` is injective because `encode` is its left inverse. -/
theorem decode_injective : Function.Injective decode := by
  intro k1 k2 h
  have h1 : encode (decode k1) = encode (decode k2) := by rw [h]
  simpa [encode_decode] using h1

end VarIdEncoding
