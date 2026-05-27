/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

import Heyting.Languages.R1CS

/-!
# Pass Proof Tactics

General-purpose tactics for automating compiler pass correctness proofs.
Independent of any specific pass — they target recurring proof patterns.

## Tactics

- **`r1cs_arith`** — Closes R1CS arithmetic goals after all definitions have been
  unfolded to raw field expressions.

- **`r1cs_unfold_sat`** — Unfolds `R1CS.satisfiesLinComb`, `R1CS.evalLinComb`,
  and `List.foldl`.
-/

namespace Heyting.Tactic

/-- Unfold R1CS satisfaction and evaluation into raw field arithmetic. -/
macro "r1cs_unfold_sat" : tactic => `(tactic|
  simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, List.foldl] at *)

/-- Close an R1CS arithmetic goal. Assumes R1CS constraint definitions and
pass-specific definitions have already been unfolded to raw field arithmetic.
Tries, in order: `linear_combination`, `simp_all`, `ring_nf`, `field_simp`, `aesop`. -/
macro "r1cs_arith" : tactic => `(tactic| (
  first
  | linear_combination ‹_›.symm
  | linear_combination ‹_›
  | (simp_all only [one_mul, zero_add, mul_one, zero_mul, ne_eq,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]; done)
  | (ring_nf at *; simp_all only [one_mul, zero_add, mul_one]; done)
  | (ring_nf at *; aesop)
  | (field_simp at *; aesop)
  | aesop))

end Heyting.Tactic
