/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.Felt
import Heyting.Dialects.ConstrainEq
import Heyting.Languages.FlatIR
import Heyting.Passes.FlatIRToR1CS

/-!
# R1CS-like instruction dialect

Single-dialect, SSA instruction form immediately above the existing FlatIR/R1CS
backend. Arithmetic instructions update the semantic environment; equality
instructions constrain it. Every operation has a direct `FlatIR.Instr`
encoding and therefore reuses the verified FlatIR-to-R1CS compiler.
-/

namespace Dialect.R1CSLike

open Dialect

inductive Op (γ : OpCtx) (F : Type) where
  | assign (op : Felt.Op γ F)
  | assertEq (src1 src2 : LocalVar)
  deriving Repr, DecidableEq

def dest : Op γ F → Option LocalVar
  | .assign op => Felt.dest op
  | .assertEq _ _ => none

def reads : Op γ F → List LocalVar
  | .assign op => Felt.reads op
  | .assertEq a b => [a, b]

def cap : Op γ F → Capability
  | .assign _ => .pure
  | .assertEq _ _ => .constraint

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .assign op => .assign (Felt.mapVars ρ op)
  | .assertEq a b => .assertEq (ρ a) (ρ b)

def sig : OpSig where
  Op := Op
  dest := dest
  reads := reads
  mapVars := mapVars
  cap := cap
  mapVars_id := by
    intro γ F op
    cases op with
    | assign felt => cases felt <;> rfl
    | assertEq => rfl
  mapVars_comp := by
    intro γ F ρ σ op
    cases op with
    | assign felt => cases felt <;> rfl
    | assertEq => rfl
  dest_mapVars := by
    intro γ F ρ op
    cases op with
    | assign felt => cases felt <;> rfl
    | assertEq => rfl
  reads_mapVars := by
    intro γ F ρ op
    cases op with
    | assign felt => cases felt <;> simp [mapVars, reads, Felt.mapVars, Felt.reads]
    | assertEq => rfl
  cap_mapVars := by intro γ F ρ op; cases op <;> rfl

def sem (F : Type) [Field F] (Δ : DialectSet := [sig]) : DialectSem Δ sig F where
  constrainStep := fun _ctx op env =>
    match op with
    | .assign felt => (Felt.applyOp felt env, True)
    | .assertEq a b => (env, env a = env b)
  computeStep := fun _ctx op env =>
    match op with
    | .assign felt => some (Felt.applyOp felt env)
    | .assertEq _ _ => some env
  constrainStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h
    cases op with
    | assign felt =>
      refine ⟨Iff.rfl, ?_⟩
      intro d hd
      have hd' : d = Felt.destVar felt := by
        change Felt.dest felt = some d at hd
        rw [Felt.dest_eq] at hd
        exact (Option.some.inj hd).symm
      subst d
      simp only
      rw [Felt.applyOp_at_dest, Felt.applyOp_at_dest]
      exact Felt.evalVal_reads_congr felt env₁ env₂ (by simpa [reads] using h)
    | assertEq a b =>
      change ∀ v ∈ [a, b], env₁ v = env₂ v at h
      have ha := h a (by simp)
      have hb := h b (by simp)
      constructor
      · change (env₁ a = env₁ b) ↔ (env₂ a = env₂ b)
        rw [ha, hb]
      · intro d hd
        change none = some d at hd
        cases hd
  constrainStep_frame := by
    intro n γ ctx op env v hv
    cases op with
    | assign felt =>
      exact Felt.applyOp_at_other felt env v (by
        intro h
        subst v
        exact hv (Felt.dest_eq felt))
    | assertEq a b => rfl
  computeStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h d hd
    cases op with
    | assign felt =>
      have hd' : d = Felt.destVar felt := by
        simp only [sig, dest, Felt.dest_eq] at hd
        exact (Option.some.inj hd).symm
      subst d
      simp only [Option.map]
      rw [Felt.applyOp_at_dest, Felt.applyOp_at_dest]
      exact congrArg some (Felt.evalVal_reads_congr felt env₁ env₂
        (by simpa [reads] using h))
    | assertEq a b => simp [sig, dest] at hd
  computeStep_status_congr := by
    intro n γ ctx op env₁ env₂ h
    cases op <;> rfl
  computeStep_frame := by
    intro n γ ctx op env env' v hsome hv
    cases op with
    | assign felt =>
      have hout : env' = Felt.applyOp felt env := by simpa using hsome.symm
      rw [hout]
      exact Felt.applyOp_at_other felt env v (by
        intro h
        subst v
        exact hv (Felt.dest_eq felt))
    | assertEq a b =>
      have hout : env' = env := Option.some.inj hsome.symm
      subst env'
      rfl

/-- Direct adapter to FlatIR instruction consumed by verified R1CS compiler. -/
def toFlatInstr : Op γ F → FlatIR.Instr F
  | .assign (.add d a b) => .assignAdd d a b
  | .assign (.sub d a b) => .assignSub d a b
  | .assign (.mul d a b) => .assignMul d a b
  | .assign (.div d a b) => .assignDiv d a b
  | .assign (.neg d a) => .assignNeg d a
  | .assign (.inv d a) => .assignInv d a
  | .assign (.const d c) => .assignConst d c
  | .assertEq a b => .assertEq a b

abbrev Set : DialectSet := [sig]

private def ix : Fin Set.length := ⟨0, by simp [Set]⟩

private theorem fin_eq_ix (d : Fin Set.length) : d = ix := by
  ext
  exact Nat.lt_one_iff.mp d.isLt

/-- Erase dialect packaging to a FlatIR program. -/
def toFlatProgram {γ : OpCtx} : List (Stmt Set γ F) → FlatIR.Program F
  | [] => []
  | .op d op :: rest =>
      (by
        have hd : d = ix := fin_eq_ix d
        subst d
        exact toFlatInstr op) :: toFlatProgram rest

/-- Reuse the verified FlatIR backend for a dialect body. -/
def toR1CS [Field F] {γ : OpCtx} (body : List (Stmt Set γ F))
    (numPublicInputs : Nat := 0) : R1CS.System F :=
  FlatIRToR1CS.compileProgram F (toFlatProgram body) numPublicInputs

/-- The backend adapter preserves every satisfying flat witness. -/
theorem toR1CS_preservation [Field F] {γ : OpCtx}
    (body : List (Stmt Set γ F)) (w : FlatIR.Witness F)
    (h : FlatIR.satisfies w (toFlatProgram body)) :
    ∃ wt : R1CS.Witness F,
      (∀ v, wt (.var v) = w v) ∧
      R1CS.satisfies wt (toR1CS body) := by
  exact (FlatIRToR1CS.CorrectPass (F := F)).preservation w
    (toFlatProgram body) h

/-- The backend adapter reflects every satisfying R1CS witness. -/
theorem toR1CS_reflection [Field F] {γ : OpCtx}
    (body : List (Stmt Set γ F)) (wt : R1CS.Witness F)
    (h : R1CS.satisfies wt (toR1CS body)) :
    ∃ w : FlatIR.Witness F,
      (∀ v, wt (.var v) = w v) ∧
      FlatIR.satisfies w (toFlatProgram body) := by
  exact (FlatIRToR1CS.CorrectPass (F := F)).reflection wt
    (toFlatProgram body) h

end Dialect.R1CSLike
