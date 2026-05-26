/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.CheckedSemantics
import Heyting.Languages.FlatIR

/-!
# FlatIR Checked Execution

Executable checked semantics for `FlatIR` programs.

This file evaluates each instruction under a concrete witness, returns either a
successful checked trace or the first failing instruction, and proves that this
checked execution agrees with the declarative `FlatIR.satisfies` semantics.
-/

namespace FlatIRChecked

open CheckedSemantics

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Checked execution -/

/-- Checked-execution steps are just FlatIR instructions themselves. -/
abbrev CheckedStep (F : Type) := FlatIR.Instr F

/-- Boolean checker for a single FlatIR instruction under a witness. -/
def checkStep (w : FlatIR.Witness F) (instr : FlatIR.Instr F) : Bool :=
  match instr with
  | .assignAdd dest src1 src2 => decide (w dest = w src1 + w src2)
  | .assignSub dest src1 src2 => decide (w dest = w src1 - w src2)
  | .assignMul dest src1 src2 => decide (w dest = w src1 * w src2)
  | .assignDiv dest src1 src2 => decide (w src2 ≠ 0 ∧ w dest = w src1 * (w src2)⁻¹)
  | .assignNeg dest src       => decide (w dest = -(w src))
  | .assignConst dest c       => decide (w dest = c)
  | .assertEq src1 src2       => decide (w src1 = w src2)

/-- Boolean checker agrees with declarative instruction satisfaction. -/
theorem checkStep_true_iff_satisfiesInstr (w : FlatIR.Witness F)
    (instr : FlatIR.Instr F) :
    checkStep w instr = true ↔ FlatIR.satisfiesInstr w instr := by
  cases instr <;> simp [checkStep, FlatIR.satisfiesInstr]

/-- Deterministic checked execution over a whole FlatIR program. -/
def evalChecked (w : FlatIR.Witness F) (prog : FlatIR.Program F) :
    Result (CheckedStep F) :=
  match prog with
  | [] => .success []
  | instr :: rest =>
    if checkStep w instr then
      match evalChecked w rest with
      | .success trace => .success (instr :: trace)
      | .failure checkedPrefix failed => .failure (instr :: checkedPrefix) failed
    else
      .failure [] instr

/-- Predicate that checked execution succeeds on every instruction in the program. -/
def checkedSuccess (w : FlatIR.Witness F) (prog : FlatIR.Program F) : Prop :=
  evalChecked w prog = .success prog

/-- Checked execution succeeds exactly when the declarative semantics holds. -/
theorem evalChecked_success_iff_satisfies (w : FlatIR.Witness F) (prog : FlatIR.Program F) :
    evalChecked w prog = .success prog ↔ FlatIR.satisfies w prog := by
  induction prog with
  | nil =>
    simp [evalChecked, FlatIR.satisfies]
  | cons instr rest ih =>
    constructor
    · intro h
      have hCheck : checkStep w instr = true := by
        by_cases hs : checkStep w instr
        · exact hs
        · simp [evalChecked, hs] at h
      have hInstr : FlatIR.satisfiesInstr w instr :=
        (checkStep_true_iff_satisfiesInstr w instr).1 hCheck
      have hRestEq : evalChecked w rest = .success rest := by
        cases hRest : evalChecked w rest with
        | success trace =>
          have hCons : Result.success (instr :: trace) = Result.success (instr :: rest) := by
            simpa [evalChecked, hCheck, hRest] using h
          have hTrace : trace = rest := by
            injection hCons with hEq
            exact List.cons.inj hEq |>.2
          simp [hTrace]
        | failure checkedPrefix failed =>
          have : False := by
            simp [evalChecked, hCheck, hRest] at h
          exact False.elim this
      have hRestSat : FlatIR.satisfies w rest := ih.mp hRestEq
      intro instr' hin
      rcases List.mem_cons.mp hin with rfl | hinRest
      · exact hInstr
      · exact hRestSat instr' hinRest
    · intro hSat
      have hInstr : FlatIR.satisfiesInstr w instr := hSat instr (by simp)
      have hCheck : checkStep w instr = true :=
        (checkStep_true_iff_satisfiesInstr w instr).2 hInstr
      have hRestSat : FlatIR.satisfies w rest := by
        intro instr' hin
        exact hSat instr' (by simp [hin])
      have hRestEq : evalChecked w rest = .success rest := ih.mpr hRestSat
      simp [evalChecked, hCheck, hRestEq]

/-- Convenience corollary: declarative satisfaction implies checked success. -/
theorem checkedSuccess_iff_satisfies (w : FlatIR.Witness F) (prog : FlatIR.Program F) :
    checkedSuccess w prog ↔ FlatIR.satisfies w prog := by
  exact evalChecked_success_iff_satisfies w prog

/-- Package `FlatIR.satisfies -> checkedSuccess` direction as a theorem. -/
theorem checkedSuccess_of_satisfies (w : FlatIR.Witness F) (prog : FlatIR.Program F)
    (h : FlatIR.satisfies w prog) : checkedSuccess w prog :=
  (checkedSuccess_iff_satisfies w prog).2 h

/-- Package `checkedSuccess -> FlatIR.satisfies` direction as a theorem. -/
theorem satisfies_of_checkedSuccess (w : FlatIR.Witness F) (prog : FlatIR.Program F)
    (h : checkedSuccess w prog) : FlatIR.satisfies w prog :=
  (checkedSuccess_iff_satisfies w prog).1 h

end FlatIRChecked
