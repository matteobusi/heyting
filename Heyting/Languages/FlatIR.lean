/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Language

/-!
# FlatIR

Flat backend instruction language immediately above `R1CS`.

`FlatIR` is register-based and SSA-like. It keeps only felt arithmetic and
equality constraints, with calls and structured object operations already
eliminated or encoded.
-/

namespace FlatIR
  variable (F : Type) [Field F]

  /-- FlatIR variables are plain natural-number registers. -/
  abbrev VarId := Nat

  /--
  Flat instruction language used after structural dialect erasure.

  Instructions are SSA-like equations over registers, except `assertEq`, which
  records a constraint without producing a destination.
  -/
  inductive Instr (F : Type) where
    | assignAdd (dest : VarId) (src1 src2 : VarId)
    | assignSub (dest : VarId) (src1 src2 : VarId)
    | assignMul (dest : VarId) (src1 src2 : VarId)
    | assignDiv (dest : VarId) (src1 src2 : VarId)
    | assignNeg (dest : VarId) (src : VarId)
    /-- Field inverse with `inv(0) = 0`.  For `src ≠ 0`, `dest = src⁻¹`;
        for `src = 0`, `dest = 0`.  This matches LLZK semantics where
        `felt.inv` is a non-native op that does not panic on zero. -/
    | assignInv (dest : VarId) (src : VarId)
    | assignConst (dest : VarId) (c : F)
    | assertEq (src1 src2 : VarId)
    deriving Repr

  /-- A FlatIR program is a list of flat instructions. -/
  abbrev Program (F : Type) := List (Instr F)

  /-- A FlatIR witness assigns a field element to each flat register. -/
  abbrev Witness (F : Type) := VarId → F

  /-- Satisfaction of a single FlatIR instruction by a witness. -/
  def satisfiesInstr {F : Type} [Field F] (w : Witness F) (instr : Instr F) : Prop :=
    match instr with
    | .assignAdd dest src1 src2 => w dest = w src1 + w src2
    | .assignSub dest src1 src2 => w dest = w src1 - w src2
    | .assignMul dest src1 src2 => w dest = w src1 * w src2
    | .assignDiv dest src1 src2 => w src2 ≠ 0 ∧ w dest = w src1 * (w src2)⁻¹
    | .assignNeg dest src       => w dest = -(w src)
    | .assignInv dest src       => w dest = (w src)⁻¹  -- inv(0) = 0 by field convention
    | .assignConst dest c       => w dest = c
    | .assertEq src1 src2       => w src1 = w src2

  /-- All variables referenced by an instruction, including its destination. -/
  def instrVars {F : Type} (instr : Instr F) : List VarId :=
    match instr with
    | .assignAdd dest src1 src2 => [dest, src1, src2]
    | .assignSub dest src1 src2 => [dest, src1, src2]
    | .assignMul dest src1 src2 => [dest, src1, src2]
    | .assignDiv dest src1 src2 => [dest, src1, src2]
    | .assignNeg dest src       => [dest, src]
    | .assignInv dest src       => [dest, src]
    | .assignConst dest _       => [dest]
    | .assertEq src1 src2       => [src1, src2]

  /-- If two witnesses agree on all variables of an instruction, satisfaction transfers. -/
  theorem satisfiesInstr_congr {F : Type} [Field F] {w1 w2 : Witness F}
      {instr : Instr F}
      (h : ∀ v ∈ instrVars instr, w1 v = w2 v) :
      satisfiesInstr w1 instr ↔ satisfiesInstr w2 instr := by
    cases instr with
    | assignAdd dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignSub dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignMul dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignDiv dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignNeg dest src =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src (by tauto)]
    | assignInv dest src =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src (by tauto)]
    | assignConst dest c =>
      simp only [instrVars, List.mem_singleton] at h
      simp only [satisfiesInstr, h dest (by tauto)]
    | assertEq src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h src1 (by tauto), h src2 (by tauto)]

  /-- Satisfaction of a FlatIR program means satisfying every instruction in it. -/
  def satisfies {F : Type} [Field F] (w : Witness F) (prog : Program F) : Prop :=
    ∀ instr ∈ prog, satisfiesInstr w instr

  /-- FlatIR as an instance of the generic `Language` interface. -/
  instance Language (F : Type) [Field F] : Language VarId F where
    Program := Program F
    satisfies := satisfies
end FlatIR
