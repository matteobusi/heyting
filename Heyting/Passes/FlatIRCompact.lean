/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Languages.FlatIR
import Mathlib.Data.List.Basic

/-!
# FlatIR -> FlatIR Variable Compaction

Renames all variables used by a FlatIR program to a dense prefix `0..k-1`,
preserving instruction order and semantics.

Used to eliminate sparse variable ids before lowering to R1CS/binary formats.
-/

namespace FlatIRCompact

open FlatIR

variable {F : Type} [Field F]

/-- All variables mentioned by a program, in first-occurrence order before
    `eraseDups`. -/
def usedVars : FlatIR.Program F → List FlatIR.VarId
  | [] => []
  | instr :: rest => FlatIR.instrVars instr ++ usedVars rest

/-- Dense support list for a program. Variable `v` is renamed to its index in
    this list. -/
def addNew (acc : List FlatIR.VarId) (v : FlatIR.VarId) : List FlatIR.VarId :=
  if v ∈ acc then acc else acc ++ [v]

theorem mem_addNew {x v : FlatIR.VarId} {acc : List FlatIR.VarId} :
    x ∈ addNew acc v ↔ x ∈ acc ∨ x = v := by
  by_cases hv : v ∈ acc
  · constructor
    · intro hx
      exact Or.inl (by simpa [addNew, hv] using hx)
    · intro hx
      rcases hx with hx | rfl
      · simpa [addNew, hv] using hx
      · simp [addNew, hv]
  · simp [addNew, hv, List.mem_append]

/-- Dense support list for a program, built in first-occurrence order. -/
def denseVars (p : FlatIR.Program F) : List FlatIR.VarId :=
  (usedVars p).foldl addNew []

/-- Map one source variable to its dense target id. -/
def compactVar (p : FlatIR.Program F) (v : FlatIR.VarId) : FlatIR.VarId :=
  (denseVars p).idxOf v

/-- Apply variable compaction to every variable in a single instruction. -/
def compactInstr (p : FlatIR.Program F) : FlatIR.Instr F → FlatIR.Instr F
  | .assignAdd d s1 s2 => .assignAdd (compactVar p d) (compactVar p s1) (compactVar p s2)
  | .assignSub d s1 s2 => .assignSub (compactVar p d) (compactVar p s1) (compactVar p s2)
  | .assignMul d s1 s2 => .assignMul (compactVar p d) (compactVar p s1) (compactVar p s2)
  | .assignDiv d s1 s2 => .assignDiv (compactVar p d) (compactVar p s1) (compactVar p s2)
  | .assignNeg d s     => .assignNeg (compactVar p d) (compactVar p s)
  | .assignConst d c   => .assignConst (compactVar p d) c
  | .assertEq s1 s2    => .assertEq (compactVar p s1) (compactVar p s2)

/-- Compile by densely renaming every variable occurrence. -/
def compileProgram (p : FlatIR.Program F) : FlatIR.Program F :=
  p.map (compactInstr p)

omit [Field F] in
theorem mem_usedVars_of_instrVar {p : FlatIR.Program F} {instr : FlatIR.Instr F} {v : FlatIR.VarId}
    (hinstr : instr ∈ p) (hv : v ∈ FlatIR.instrVars instr) :
    v ∈ usedVars p := by
  induction p with
  | nil => cases hinstr
  | cons hd tl ih =>
      simp only [usedVars, List.mem_append, List.mem_cons] at hinstr ⊢
      rcases hinstr with rfl | hinstr
      · exact Or.inl hv
      · exact Or.inr (ih hinstr)

omit [Field F] in
theorem mem_denseVars_of_instrVar {p : FlatIR.Program F} {instr : FlatIR.Instr F} {v : FlatIR.VarId}
    (hinstr : instr ∈ p) (hv : v ∈ FlatIR.instrVars instr) :
    v ∈ denseVars p := by
  have hused : v ∈ usedVars p := mem_usedVars_of_instrVar (p := p) hinstr hv
  have hmem : ∀ {acc xs : List Nat} {x : Nat},
      x ∈ xs.foldl addNew acc ↔ x ∈ acc ∨ x ∈ xs := by
    intro acc xs x
    induction xs generalizing acc with
    | nil => simp
    | cons y ys ih =>
        rw [List.foldl_cons, ih (acc := addNew acc y), mem_addNew]
        simp [List.mem_cons, or_assoc, or_left_comm, or_comm]
  simpa [denseVars] using (hmem (acc := []) (xs := usedVars p) (x := v)).2 (Or.inr hused)


theorem satisfiesInstr_rename_iff {p : FlatIR.Program F} {instr : FlatIR.Instr F}
    {ws wt : FlatIR.Witness F}
    (hvars : ∀ v, v ∈ FlatIR.instrVars instr → wt (compactVar p v) = ws v) :
    FlatIR.satisfiesInstr wt (compactInstr p instr) ↔ FlatIR.satisfiesInstr ws instr := by
  cases instr with
  | assignAdd dest src1 src2 =>
      have hdest := hvars dest (by simp [FlatIR.instrVars])
      have hsrc1 := hvars src1 (by simp [FlatIR.instrVars])
      have hsrc2 := hvars src2 (by simp [FlatIR.instrVars])
      constructor <;> intro h
      · change wt (compactVar p dest) = wt (compactVar p src1) + wt (compactVar p src2) at h
        change ws dest = ws src1 + ws src2
        rw [← hdest, ← hsrc1, ← hsrc2]
        exact h
      · change wt (compactVar p dest) = wt (compactVar p src1) + wt (compactVar p src2)
        change ws dest = ws src1 + ws src2 at h
        rw [hdest, hsrc1, hsrc2]
        exact h
  | assignSub dest src1 src2 =>
      have hdest := hvars dest (by simp [FlatIR.instrVars])
      have hsrc1 := hvars src1 (by simp [FlatIR.instrVars])
      have hsrc2 := hvars src2 (by simp [FlatIR.instrVars])
      constructor <;> intro h
      · change wt (compactVar p dest) = wt (compactVar p src1) - wt (compactVar p src2) at h
        change ws dest = ws src1 - ws src2
        rw [← hdest, ← hsrc1, ← hsrc2]
        exact h
      · change wt (compactVar p dest) = wt (compactVar p src1) - wt (compactVar p src2)
        change ws dest = ws src1 - ws src2 at h
        rw [hdest, hsrc1, hsrc2]
        exact h
  | assignMul dest src1 src2 =>
      have hdest := hvars dest (by simp [FlatIR.instrVars])
      have hsrc1 := hvars src1 (by simp [FlatIR.instrVars])
      have hsrc2 := hvars src2 (by simp [FlatIR.instrVars])
      constructor <;> intro h
      · change wt (compactVar p dest) = wt (compactVar p src1) * wt (compactVar p src2) at h
        change ws dest = ws src1 * ws src2
        rw [← hdest, ← hsrc1, ← hsrc2]
        exact h
      · change wt (compactVar p dest) = wt (compactVar p src1) * wt (compactVar p src2)
        change ws dest = ws src1 * ws src2 at h
        rw [hdest, hsrc1, hsrc2]
        exact h
  | assignDiv dest src1 src2 =>
      have hdest := hvars dest (by simp [FlatIR.instrVars])
      have hsrc1 := hvars src1 (by simp [FlatIR.instrVars])
      have hsrc2 := hvars src2 (by simp [FlatIR.instrVars])
      constructor
      · intro h
        change wt (compactVar p src2) ≠ 0 ∧
            wt (compactVar p dest) = wt (compactVar p src1) * (wt (compactVar p src2))⁻¹ at h
        rcases h with ⟨hneq, heq⟩
        refine ⟨?_, ?_⟩
        · intro hz
          apply hneq
          rw [hsrc2, hz]
        · change ws dest = ws src1 * (ws src2)⁻¹
          rw [← hdest, ← hsrc1, ← hsrc2]
          exact heq
      · intro h
        rcases h with ⟨hneq, heq⟩
        refine ⟨?_, ?_⟩
        · intro hz
          apply hneq
          rw [← hsrc2, hz]
        · change wt (compactVar p dest) = wt (compactVar p src1) * (wt (compactVar p src2))⁻¹
          rw [hdest, hsrc1, hsrc2]
          exact heq
  | assignNeg dest src =>
      have hdest := hvars dest (by simp [FlatIR.instrVars])
      have hsrc := hvars src (by simp [FlatIR.instrVars])
      constructor <;> intro h
      · change wt (compactVar p dest) = -(wt (compactVar p src)) at h
        change ws dest = -(ws src)
        rw [← hdest, ← hsrc]
        exact h
      · change wt (compactVar p dest) = -(wt (compactVar p src))
        change ws dest = -(ws src) at h
        rw [hdest, hsrc]
        exact h
  | assignConst dest c =>
      have hdest := hvars dest (by simp [FlatIR.instrVars])
      constructor <;> intro h
      · change wt (compactVar p dest) = c at h
        change ws dest = c
        rw [← hdest]
        exact h
      · change wt (compactVar p dest) = c
        change ws dest = c at h
        rw [hdest]
        exact h
  | assertEq src1 src2 =>
      have hsrc1 := hvars src1 (by simp [FlatIR.instrVars])
      have hsrc2 := hvars src2 (by simp [FlatIR.instrVars])
      constructor <;> intro h
      · change wt (compactVar p src1) = wt (compactVar p src2) at h
        change ws src1 = ws src2
        rw [← hsrc1, ← hsrc2]
        exact h
      · change wt (compactVar p src1) = wt (compactVar p src2)
        change ws src1 = ws src2 at h
        rw [hsrc1, hsrc2]
        exact h

instance CorrectPass : PresReflPass (FlatIR.Language F) (FlatIR.Language F) where
  compile := compileProgram (F := F)
  witnessRel p ws wt := ∀ v, v ∈ denseVars p → wt (compactVar p v) = ws v
  preservation := by
    intro ws p hsat
    let wt : FlatIR.Witness F := fun v =>
      match (denseVars p)[v]? with
      | some src => ws src
      | none => 0
    refine ⟨wt, ?_, ?_⟩
    · intro v hv
      simp [wt, compactVar, List.getElem?_idxOf hv]
    · intro instr hcomp
      obtain ⟨srcInstr, hinstr, rfl⟩ := List.mem_map.1 hcomp
      have hvars : ∀ v, v ∈ FlatIR.instrVars srcInstr → wt (compactVar p v) = ws v := by
        intro v hv
        have hv' : v ∈ denseVars p := mem_denseVars_of_instrVar (p := p) hinstr hv
        simp [wt, compactVar, List.getElem?_idxOf hv']
      exact (satisfiesInstr_rename_iff (p := p) (instr := srcInstr) (ws := ws) (wt := wt) hvars).2
        (hsat srcInstr hinstr)
  reflection := by
    intro wt p hsat
    let ws : FlatIR.Witness F := fun v =>
      if hv : v ∈ denseVars p then wt (compactVar p v) else 0
    refine ⟨ws, ?_, ?_⟩
    · intro v hv
      simp [ws, hv]
    · intro instr hinstr
      have hsat' : FlatIR.satisfiesInstr wt (compactInstr p instr) := by
        apply hsat
        exact List.mem_map.2 ⟨instr, hinstr, rfl⟩
      have hvars : ∀ v, v ∈ FlatIR.instrVars instr → wt (compactVar p v) = ws v := by
        intro v hv
        have hv' : v ∈ denseVars p := mem_denseVars_of_instrVar (p := p) hinstr hv
        simp [ws, hv']
      exact (satisfiesInstr_rename_iff (p := p) (instr := instr) (ws := ws) (wt := wt) hvars).1
        hsat'

end FlatIRCompact
