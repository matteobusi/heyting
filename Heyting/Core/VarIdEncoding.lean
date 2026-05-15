/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Languages.StructIR
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

/-!
# StructIR Variable-ID Encoding

Bijective encoding between concrete `StructIR.VarId = (path, member)` pairs and
natural numbers.

This encoding is used by executable passes to represent witness coordinates as
flat register ids while keeping a proven inverse pair `encode`/`decode`.
-/

namespace VarIdEncoding

open StructIR

/-- Encode a StructIR variable id `(path, member)` as a natural number. -/
def encode : StructIR.VarId -> Nat
  | (path, member) => Nat.pair (Equiv.listNatEquivNat path) member

/-- Decode a natural number into a StructIR variable id `(path, member)`. -/
def decode (k : Nat) : StructIR.VarId :=
  let p := Nat.unpair k
  (Equiv.listNatEquivNat.symm p.1, p.2)

/-- `decode` is a left inverse of `encode`. -/
theorem decode_encode (v : StructIR.VarId) : decode (encode v) = v := by
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
