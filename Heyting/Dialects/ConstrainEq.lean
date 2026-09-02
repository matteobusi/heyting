/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Semantics

/-!
# Constrain-Eq Dialect

Single op `eq src1 src2` — emits `env src1 = env src2`.

- Capability `.constraint` — only in `@constrain` bodies.
- No dest — does not write any variable.
- Constrain: emits `env s1 = env s2`, env unchanged.
- Compute: no-op (`some env`); `wf_caps` prevents this case.
-/

namespace Dialect.ConstrainEq

open Dialect

inductive Op (γ : OpCtx) (F : Type) : Type where
  | eq (src1 src2 : LocalVar) : Op γ F
  deriving Repr, DecidableEq

def dest : Op γ F → Option LocalVar
  | .eq _ _ => none

def reads : Op γ F → List LocalVar
  | .eq s1 s2 => [s1, s2]

def cap : Op γ F → Capability
  | _ => .constraint

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .eq s1 s2 => .eq (ρ s1) (ρ s2)

def sig : OpSig where
  Op      := Op
  dest    := dest
  reads   := reads
  mapVars := mapVars
  cap     := cap
  mapVars_id    := by intro γ F op; cases op; simp [mapVars]
  mapVars_comp  := by intro γ F ρ σ op; cases op; simp [mapVars]
  dest_mapVars  := by intro γ F ρ op; cases op; simp [dest]
  reads_mapVars := by intro γ F ρ op; cases op; simp [mapVars, reads]
  cap_mapVars   := by intro γ F ρ op; cases op; simp [cap]

-- sig.dest (.eq _ _) = none definitionally.
private theorem sig_dest_none (s1 s2 : LocalVar) (γ : OpCtx) (F : Type) :
    sig.dest (Op.eq (γ := γ) (F := F) s1 s2) = none := rfl

def sem (F : Type) [Field F] (Δ : DialectSet := [sig]) : DialectSem Δ sig F := {
  -- constrainStep: emit env s1 = env s2, return env unchanged.
  constrainStep := fun _ctx op env =>
    match op with
    | .eq s1 s2 => (env, env s1 = env s2)

  -- computeStep: no-op (wf_caps ensures this is never reached in valid programs).
  computeStep := fun _ctx op env =>
    match op with
    | .eq _ _ => some env

  constrainStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h
    cases op with
    | eq s1 s2 =>
      have h1 : env₁ s1 = env₂ s1 := h s1 (by simp [sig, reads])
      have h2 : env₁ s2 = env₂ s2 := h s2 (by simp [sig, reads])
      constructor
      · -- goal: (env₁ s1 = env₁ s2) ↔ (env₂ s1 = env₂ s2)  (by definitional reduction)
        change (env₁ s1 = env₁ s2) ↔ (env₂ s1 = env₂ s2)
        rw [h1, h2]
      · -- sig.dest (.eq s1 s2) = none, so premise is false
        intro d hd
        rw [sig_dest_none s1 s2 γ F] at hd
        cases hd

  constrainStep_frame := by
    intro n γ ctx op env v _hv
    cases op
    -- constrainStep (.eq s1 s2) env = (env, ...) so .1 = env
    rfl

  computeStep_reads_congr := by
    intro n γ ctx op env₁ env₂ _h d hd
    cases op
    -- sig.dest (.eq s1 s2) = none, premise false
    rw [sig_dest_none _ _ γ F] at hd
    cases hd

  computeStep_status_congr := by
    intro n γ ctx op env₁ env₂ _h
    cases op
    rfl

  computeStep_frame := by
    intro n γ ctx op env env' v hsome _hv
    cases op
    -- computeStep (.eq s1 s2) env = some env definitionally
    change some env = some env' at hsome
    have heq : env' = env := (Option.some.inj hsome).symm
    simp [heq]
}

end Dialect.ConstrainEq
