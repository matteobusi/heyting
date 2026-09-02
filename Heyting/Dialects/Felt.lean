/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Semantics

/-!
# Felt Arithmetic Dialect

Pure field-element operations: add, sub, mul, div, neg, inv, const.
All ops are `.pure`, always write exactly one dest, and use total field
arithmetic (`x/0 = 0`, `0⁻¹ = 0`). Backend lowering separately exposes the
nonzero side condition required by R1CS division.
-/

namespace Dialect.Felt

open Dialect

inductive Op (γ : OpCtx) (F : Type) : Type where
  | add   (dest src1 src2 : LocalVar) : Op γ F
  | sub   (dest src1 src2 : LocalVar) : Op γ F
  | mul   (dest src1 src2 : LocalVar) : Op γ F
  | div   (dest src1 src2 : LocalVar) : Op γ F
  | neg   (dest src : LocalVar)       : Op γ F
  | inv   (dest src : LocalVar)       : Op γ F
  | const (dest : LocalVar) (c : F)   : Op γ F
  deriving Repr, DecidableEq

def dest : Op γ F → Option LocalVar
  | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ => some d
  | .neg d _   | .inv d _   | .const d _ => some d

def reads : Op γ F → List LocalVar
  | .add _ s1 s2 | .sub _ s1 s2 | .mul _ s1 s2 | .div _ s1 s2 => [s1, s2]
  | .neg _ s     | .inv _ s => [s]
  | .const _ _ => []

def cap : Op γ F → Capability := fun _ => .pure

def destVar : Op γ F → LocalVar
  | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ => d
  | .neg d _   | .inv d _   | .const d _ => d

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .add d s1 s2 => .add (ρ d) (ρ s1) (ρ s2)
  | .sub d s1 s2 => .sub (ρ d) (ρ s1) (ρ s2)
  | .mul d s1 s2 => .mul (ρ d) (ρ s1) (ρ s2)
  | .div d s1 s2 => .div (ρ d) (ρ s1) (ρ s2)
  | .neg d s     => .neg (ρ d) (ρ s)
  | .inv d s     => .inv (ρ d) (ρ s)
  | .const d c   => .const (ρ d) c

theorem dest_eq (op : Op γ F) : dest op = some (destVar op) := by
  cases op <;> rfl

def evalVal [Field F] (op : Op γ F) (env : LocalVar → F) : F :=
  match op with
  | .add _ s1 s2 => env s1 + env s2
  | .sub _ s1 s2 => env s1 - env s2
  | .mul _ s1 s2 => env s1 * env s2
  | .div _ s1 s2 => env s1 / env s2
  | .neg _ s     => -env s
  | .inv _ s     => (env s)⁻¹
  | .const _ c   => c

-- Direct if-expression avoids Function.update naming issues.
def applyOp [Field F] (op : Op γ F) (env : LocalVar → F) : LocalVar → F :=
  fun v => if v = destVar op then evalVal op env else env v

/-- Validity condition required by the R1CS encoding. Unlike field division,
the backend's division instruction is intentionally partial at zero. -/
def backendValid [Field F] (op : Op γ F) (env : LocalVar → F) : Prop :=
  match op with
  | .div _ _ src2 => env src2 ≠ 0
  | _ => True

/-- Executable form of `backendValid`. Keeping operation match outside
`decide` lets instance synthesis see equality as only nontrivial case. -/
def backendValidBool [Field F] [DecidableEq F]
    (op : Op γ F) (env : LocalVar → F) : Bool :=
  match op with
  | .div _ _ src2 => decide (env src2 ≠ 0)
  | _ => true

theorem backendValidBool_eq_true [Field F] [DecidableEq F]
    (op : Op γ F) (env : LocalVar → F) :
    backendValidBool op env = true ↔ backendValid op env := by
  cases op <;> simp [backendValidBool, backendValid]

theorem backendValidBool_mapVars [Field F] [DecidableEq F]
    (rename : LocalVar → LocalVar) (op : Op γ F)
    (source target : LocalVar → F)
    (hagrees : ∀ v ∈ reads op, target (rename v) = source v) :
    backendValidBool (mapVars rename op) target = backendValidBool op source := by
  cases op with
  | div _ _ denominator =>
      simp only [mapVars, backendValidBool]
      rw [hagrees denominator (by simp [reads])]
  | add | sub | mul | neg | inv | const => rfl

theorem backendValid_mapVars [Field F]
    (rename : LocalVar → LocalVar) (op : Op γ F)
    (source target : LocalVar → F)
    (hagrees : ∀ v ∈ reads op, target (rename v) = source v) :
    backendValid (mapVars rename op) target ↔ backendValid op source := by
  cases op with
  | div _ _ denominator =>
      simp only [mapVars, backendValid]
      rw [hagrees denominator (by simp [reads])]
  | add | sub | mul | neg | inv | const => simp [mapVars, backendValid]

theorem backendValid_reads_congr [Field F] (op : Op γ F) (env₁ env₂ : LocalVar → F)
    (h : ∀ v ∈ reads op, env₁ v = env₂ v) :
    backendValid op env₁ ↔ backendValid op env₂ := by
  cases op with
  | div _ _ s2 => simp only [backendValid]; rw [h s2 (by simp [reads])]
  | add | sub | mul | neg | inv | const => simp [backendValid]

theorem applyOp_at_dest [Field F] (op : Op γ F) (env : LocalVar → F) :
    applyOp op env (destVar op) = evalVal op env := by simp [applyOp]

theorem applyOp_at_other [Field F] (op : Op γ F) (env : LocalVar → F) (v : LocalVar)
    (hv : v ≠ destVar op) : applyOp op env v = env v := by simp [applyOp, if_neg hv]

theorem evalVal_reads_congr [Field F] (op : Op γ F) (env₁ env₂ : LocalVar → F)
    (h : ∀ v ∈ reads op, env₁ v = env₂ v) :
    evalVal op env₁ = evalVal op env₂ := by
  cases op with
  | add _ s1 s2 | sub _ s1 s2 | mul _ s1 s2 | div _ s1 s2 =>
    simp only [evalVal]
    have h1 : env₁ s1 = env₂ s1 := h s1 (by simp [reads])
    have h2 : env₁ s2 = env₂ s2 := h s2 (by simp [reads])
    rw [h1, h2]
  | neg _ s | inv _ s =>
    simp only [evalVal]
    rw [h s (by simp [reads])]
  | const _ c => rfl

def sig : OpSig := {
  Op      := Op
  dest    := dest
  reads   := reads
  mapVars := mapVars
  cap     := cap
  mapVars_id    := by intro γ F op; cases op <;> simp [mapVars]
  mapVars_comp  := by intro γ F ρ σ op; cases op <;> simp [mapVars]
  dest_mapVars  := by intro γ F ρ op; cases op <;> simp [mapVars, dest]
  reads_mapVars := by intro γ F ρ op; cases op <;> simp [mapVars, reads]
  cap_mapVars   := by intro γ F ρ op; cases op <;> simp [cap]
}

-- sig.dest = Felt.dest definitionally; used to lift hypotheses in sem proofs.
private theorem sig_dest_eq (op : Op γ F) : sig.dest op = some (destVar op) := dest_eq op

def sem (F : Type) [Field F] (Δ : DialectSet := [sig]) : DialectSem Δ sig F := {
  constrainStep := fun _ctx op env => (applyOp op env, True)
  computeStep   := fun _ctx op env => some (applyOp op env)

  constrainStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h
    refine ⟨Iff.rfl, fun d hd => ?_⟩
    rw [sig_dest_eq] at hd
    have hd' : d = destVar op := (Option.some.inj hd).symm
    rw [hd']
    change applyOp op env₁ (destVar op) = applyOp op env₂ (destVar op)
    rw [applyOp_at_dest, applyOp_at_dest]
    exact evalVal_reads_congr op env₁ env₂ h

  constrainStep_frame := by
    intro n γ ctx op env v hv
    rw [sig_dest_eq] at hv
    exact applyOp_at_other op env v (fun h => hv (congrArg some h.symm))

  computeStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h d hd
    rw [sig_dest_eq] at hd
    have hd' : d = destVar op := (Option.some.inj hd).symm
    -- computeStep op env = some (applyOp op env) definitionally
    change (some (applyOp op env₁)).map (· d) = (some (applyOp op env₂)).map (· d)
    simp only [Option.map]
    rw [hd']
    simp only [applyOp_at_dest]
    exact congrArg some (evalVal_reads_congr op env₁ env₂ h)

  computeStep_status_congr := by
    intro n γ ctx op env₁ env₂ h
    rfl

  computeStep_frame := by
    intro n γ ctx op env env' v hsome hv
    -- computeStep op env = some (applyOp op env) definitionally
    change some (applyOp op env) = some env' at hsome
    have heq : env' = applyOp op env := (Option.some.inj hsome).symm
    rw [sig_dest_eq] at hv
    rw [heq]
    exact applyOp_at_other op env v (fun h => hv (congrArg some h.symm))
}

end Dialect.Felt
