/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Languages.StructIR
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

namespace VarIdEncoding

open StructIR

/-- Encode a StructIR variable id `(path, member)` as a natural number. -/
def encode : StructIR.VarId -> Nat
  | (path, member) => Nat.pair (Equiv.listNatEquivNat path) member

/-- Decode a natural number into a StructIR variable id `(path, member)`. -/
def decode (k : Nat) : StructIR.VarId :=
  let p := Nat.unpair k
  (Equiv.listNatEquivNat.symm p.1, p.2)

theorem decode_encode (v : StructIR.VarId) : decode (encode v) = v := by
  rcases v with ⟨path, member⟩
  simp [encode, decode, Nat.unpair_pair]

theorem encode_decode (k : Nat) : encode (decode k) = k := by
  simp [encode, decode, Nat.pair_unpair]

theorem encode_injective : Function.Injective encode := by
  intro v1 v2 h
  have h1 : decode (encode v1) = decode (encode v2) := by rw [h]
  simpa [decode_encode] using h1

theorem decode_injective : Function.Injective decode := by
  intro k1 k2 h
  have h1 : encode (decode k1) = encode (decode k2) := by rw [h]
  simpa [encode_decode] using h1

end VarIdEncoding
