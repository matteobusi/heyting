/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Languages.R1CS
import Heyting.Backends.R1CSJSON
import Mathlib.Data.List.Nodup

/-!
# Wire Assignment

Maps each `R1CS.VarId` to a dense, 0-based wire index suitable for use in
binary formats (Circom `.r1cs`, `.wtns`) and the witness JSON array.

## Wire index layout

Wire `0` is `varOne`. Wires `1..k` are the statement wires
`sys.statementVars = publicOutputs ++ publicInputs`, in order, as Circom expects
(public outputs, then public inputs). The remaining allocated wires follow in canonical
order: `var 0 ..`, then `aux 0 ..`, then `auxIsZero 0 ..`, skipping statement wires.

## Verified layout facts

* `encode_statement`: statement wire `i` is encoded as wire `i + 1`.
* `decode_statement`: wire `i + 1` decodes to statement wire `i`.
* `layout_nodup`: no two allocated variables share a wire.
* `decode_encode`: decoding inverts encoding on every allocated variable.

These hold when the statement wires are pairwise distinct (`statement.Nodup`).
The byte-level Circom encoding that uses this layout remains a tested, unproved boundary.
-/

namespace WireAssignment

open R1CS

variable {F : Type} [Field F]

/-- Wire-index namespace sizes and statement wires of an R1CS system. -/
structure Sizes where
  /-- Number of `.var n` slots. -/
  numRegVars : Nat
  /-- Number of `.aux n` slots. -/
  numAuxVars : Nat
  /-- Number of `.auxIsZero n` slots. -/
  numAuxIsZeroVars : Nat
  /-- Statement wires, placed at wires `1..statement.length`. -/
  statement : List VarId := []
  deriving Repr

/-- Allocated non-constant variables in canonical order. -/
def Sizes.baseVars (wa : Sizes) : List VarId :=
  (List.range wa.numRegVars).map .var ++ (List.range wa.numAuxVars).map .aux ++
    (List.range wa.numAuxIsZeroVars).map .auxIsZero

/-- Order of the non-constant wires: statement wires first, then the other base variables. -/
def Sizes.layout (wa : Sizes) : List VarId :=
  wa.statement ++ wa.baseVars.filter (· ∉ wa.statement)

/-- Total number of wires, including the constant-1 wire at index `0`. -/
def Sizes.numWires (wa : Sizes) : Nat :=
  1 + wa.layout.length

/-- One past the largest `.var` index among the statement wires. -/
private def statementRegVars (statement : List VarId) : Nat :=
  statement.foldl (fun a v => match v with | .var n => max a (n + 1) | _ => a) 0

/-- Compute `Sizes` from constraints and statement wires. A statement wire that no
constraint mentions is still allocated. -/
def fromConstraints [Repr F] (constraints : List (R1CS.Constraint F))
    (statement : List VarId := []) : Sizes :=
  { numRegVars := max (R1CSJSON.countRegVars constraints) (statementRegVars statement)
    numAuxVars := R1CSJSON.countAuxVars constraints
    numAuxIsZeroVars := R1CSJSON.countAuxIsZeroVars constraints
    statement }

/-- Compute `Sizes` from an `R1CS.System`. -/
def fromSystem [Repr F] (sys : R1CS.System F) : Sizes :=
  fromConstraints sys.constraints sys.statementVars

/-- Map a `VarId` to its dense wire index: `varOne ↦ 0`, layout position `i ↦ i + 1`.
A variable outside the layout maps to `numWires` (out of range). -/
def encode (wa : Sizes) : VarId → Nat
  | .varOne => 0
  | v => wa.layout.idxOf v + 1

/-- Map a dense wire index back to a `VarId`, or `none` if out of range. -/
def decode (wa : Sizes) (i : Nat) : Option VarId :=
  if i = 0 then some .varOne else wa.layout[i - 1]?

/-! ## Layout theorems -/

private theorem varOne_not_mem_baseVars (wa : Sizes) : VarId.varOne ∉ wa.baseVars := by
  simp [Sizes.baseVars]

theorem baseVars_nodup (wa : Sizes) : wa.baseVars.Nodup := by
  simp only [Sizes.baseVars]
  refine List.Nodup.append (List.Nodup.append ?_ ?_ ?_) ?_ ?_
  · exact (List.nodup_range).map (fun _ _ h => VarId.var.inj h)
  · exact (List.nodup_range).map (fun _ _ h => VarId.aux.inj h)
  · simp [List.Disjoint]
  · exact (List.nodup_range).map (fun _ _ h => VarId.auxIsZero.inj h)
  · simp only [List.Disjoint, List.mem_append, List.mem_map, List.mem_range]
    rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) ⟨_, _, h⟩ <;> cases h

/-- Distinct statement wires give an injective layout. -/
theorem layout_nodup (wa : Sizes) (h : wa.statement.Nodup) : wa.layout.Nodup := by
  refine List.Nodup.append h ((baseVars_nodup wa).filter _) ?_
  intro v hs hb
  simp only [List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 hs

/-- Statement wire `i` is encoded as wire `i + 1`. -/
theorem encode_statement (wa : Sizes) (h : wa.statement.Nodup)
    (hone : VarId.varOne ∉ wa.statement) (i : Nat) (hi : i < wa.statement.length) :
    encode wa wa.statement[i] = i + 1 := by
  have hne : wa.statement[i] ≠ .varOne := fun heq => hone (heq ▸ List.getElem_mem hi)
  have hidx : wa.layout.idxOf wa.statement[i] = i := by
    have hlt : i < wa.layout.length := by simp [Sizes.layout]; omega
    have hget : wa.layout[i] = wa.statement[i] := by
      simp [Sizes.layout, List.getElem_append_left hi]
    rw [← hget]
    exact (layout_nodup wa h).idxOf_getElem i hlt
  cases hv : wa.statement[i] with
  | varOne => exact absurd hv hne
  | var n => simp [encode, ← hv, hidx]
  | aux n => simp [encode, ← hv, hidx]
  | auxIsZero n => simp [encode, ← hv, hidx]

/-- Wire `i + 1` decodes to statement wire `i`. -/
theorem decode_statement (wa : Sizes) (i : Nat) (hi : i < wa.statement.length) :
    decode wa (i + 1) = some wa.statement[i] := by
  simp [decode, Sizes.layout, List.getElem?_append_left hi, hi]

/-- Decoding inverts encoding on every allocated variable. -/
theorem decode_encode (wa : Sizes) (hone : VarId.varOne ∉ wa.statement) (v : VarId)
    (hv : v = .varOne ∨ v ∈ wa.layout) : decode wa (encode wa v) = some v := by
  rcases hv with rfl | hmem
  · simp [encode, decode]
  · have hne : v ≠ .varOne := by
      rintro rfl
      simp only [Sizes.layout, List.mem_append, List.mem_filter] at hmem
      rcases hmem with h | h
      · exact hone h
      · exact varOne_not_mem_baseVars wa h.1
    have henc : encode wa v = wa.layout.idxOf v + 1 := by
      cases v <;> simp_all [encode]
    rw [henc]
    simp [decode, List.getElem?_idxOf hmem]

end WireAssignment
