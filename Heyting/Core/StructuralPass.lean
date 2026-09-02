/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Core.Module

/-!
# Static structural-erasure passes

Structural dialects can change the semantic state carried by a compiler stage:
object erasure, for example, relates object paths and witness storage to flat
target variables. `Language` intentionally remains the witness-specialized
framework used by leaf and backend passes. This file adds the smallest static
module layer needed around it:

- one concrete `State` type per `ModuleStage`;
- partial, explicit `StructuralPass` values;
- preservation/reflection conditional on successful lowering;
- ordinary explicit composition through a typed intermediate stage;
- adapters for witness-backed stages and `PresReflPass`.

There is no effect registry, heterogeneous state list, dynamic cast, or
automatic pass selection here.
-/

namespace Dialect

variable {F : Type} [Field F]
variable {n : Nat}

/-- A dialect-module language with one statically selected semantic state. -/
structure ModuleStage (Δ : DialectSet) (n : Nat) (F : Type) where
  State : Type
  satisfies : State → Module Δ n F → Prop

namespace ModuleStage

/-- A witness-backed module stage, suitable for the existing `Language` API. -/
def ofWitness (V : Type) (satisfies : Witness V F → Module Δ n F → Prop) :
    ModuleStage Δ n F where
  State := Witness V F
  satisfies := satisfies

/-- The ordinary `Language` corresponding to a witness-backed module stage. -/
def language (V : Type) (satisfies : Witness V F → Module Δ n F → Prop) :
    Language V F where
  Program := Module Δ n F
  satisfies := satisfies

end ModuleStage

/-- A partial, semantics-certified transformation between two static module
stages. Correctness is required whenever `lower` succeeds. -/
structure StructuralPass {Δs Δt : DialectSet}
    (source : ModuleStage Δs n F) (target : ModuleStage Δt n F) where
  lower : Module Δs n F → Except String (Module Δt n F)
  stateRel : Module Δs n F → Module Δt n F →
    source.State → target.State → Prop
  preservation : ∀ (m : Module Δs n F) (out : Module Δt n F)
      (sourceState : source.State),
    lower m = .ok out → source.satisfies sourceState m →
      ∃ targetState, stateRel m out sourceState targetState ∧
        target.satisfies targetState out
  reflection : ∀ (m : Module Δs n F) (out : Module Δt n F)
      (targetState : target.State),
    lower m = .ok out → target.satisfies targetState out →
      ∃ sourceState, stateRel m out sourceState targetState ∧
        source.satisfies sourceState m

/-- Specialization documenting that the source set consists of one structural
dialect followed by untouched residual dialects. -/
abbrev EraseDialect (removed : OpSig) (residual : DialectSet)
    (source : ModuleStage (removed :: residual) n F)
    (target : ModuleStage residual n F) :=
  StructuralPass source target

namespace StructuralPass

/-- Identity structural pass. -/
def identity (stage : ModuleStage Δ n F) : StructuralPass stage stage where
  lower m := .ok m
  stateRel _ _ sourceState targetState := sourceState = targetState
  preservation := by
    intro m out sourceState hlower hsatisfies
    simp only [Except.ok.injEq] at hlower
    subst out
    exact ⟨sourceState, rfl, hsatisfies⟩
  reflection := by
    intro m out targetState hlower hsatisfies
    simp only [Except.ok.injEq] at hlower
    subst out
    exact ⟨targetState, rfl, hsatisfies⟩

/-- Explicit composition. The intermediate module and state are retained in
the composed relation, matching `PresReflPass.compose`'s existential witness. -/
def compose {Δ₀ Δ₁ Δ₂ : DialectSet}
    {stage₀ : ModuleStage Δ₀ n F} {stage₁ : ModuleStage Δ₁ n F}
    {stage₂ : ModuleStage Δ₂ n F}
    (pass₁ : StructuralPass stage₀ stage₁)
    (pass₂ : StructuralPass stage₁ stage₂) :
    StructuralPass stage₀ stage₂ where
  lower m := pass₁.lower m >>= pass₂.lower
  stateRel m out state₀ state₂ :=
    ∃ (mid : Module Δ₁ n F) (state₁ : stage₁.State),
      pass₁.lower m = .ok mid ∧
      pass₁.stateRel m mid state₀ state₁ ∧
      pass₂.stateRel mid out state₁ state₂
  preservation := by
    intro m out state₀ hlower hsatisfies
    cases h₁ : pass₁.lower m with
    | error error =>
      rw [h₁] at hlower
      cases hlower
    | ok mid =>
      have h₂ : pass₂.lower mid = .ok out := by simpa [h₁] using hlower
      obtain ⟨state₁, hrel₁, hsat₁⟩ :=
        pass₁.preservation m mid state₀ h₁ hsatisfies
      obtain ⟨state₂, hrel₂, hsat₂⟩ :=
        pass₂.preservation mid out state₁ h₂ hsat₁
      exact ⟨state₂, ⟨mid, state₁, rfl, hrel₁, hrel₂⟩, hsat₂⟩
  reflection := by
    intro m out state₂ hlower hsatisfies
    cases h₁ : pass₁.lower m with
    | error error =>
      rw [h₁] at hlower
      cases hlower
    | ok mid =>
      have h₂ : pass₂.lower mid = .ok out := by simpa [h₁] using hlower
      obtain ⟨state₁, hrel₂, hsat₁⟩ :=
        pass₂.reflection mid out state₂ h₂ hsatisfies
      obtain ⟨state₀, hrel₁, hsat₀⟩ :=
        pass₁.reflection m mid state₁ h₁ hsat₁
      exact ⟨state₀, ⟨mid, state₁, rfl, hrel₁, hrel₂⟩, hsat₀⟩

/-- Lift an existing total witness pass into the structural layer. -/
def ofPresReflPass {Δs Δt : DialectSet} {Vs Vt : Type}
    {sourceSat : Witness Vs F → Module Δs n F → Prop}
    {targetSat : Witness Vt F → Module Δt n F → Prop}
    (pass : PresReflPass
      (ModuleStage.language Vs sourceSat)
      (ModuleStage.language Vt targetSat)) :
    StructuralPass
      (ModuleStage.ofWitness Vs sourceSat)
      (ModuleStage.ofWitness Vt targetSat) where
  lower m := .ok (pass.compile m)
  stateRel m _ sourceState targetState := pass.witnessRel m sourceState targetState
  preservation := by
    intro m out sourceState hlower hsatisfies
    simp only [Except.ok.injEq] at hlower
    subst out
    exact pass.preservation sourceState m hsatisfies
  reflection := by
    intro m out targetState hlower hsatisfies
    simp only [Except.ok.injEq] at hlower
    subst out
    exact pass.reflection targetState m hsatisfies

/-- Constructive evidence that a partial structural pass succeeds everywhere. -/
structure TotalStructural {Δs Δt : DialectSet}
    {source : ModuleStage Δs n F} {target : ModuleStage Δt n F}
    (pass : StructuralPass source target) where
  run : ∀ m, { out // pass.lower m = .ok out }

/-- Recover an ordinary `PresReflPass` from a total witness-backed structural
pass. This is the bridge back to the established leaf/backend framework. -/
def toPresReflPass {Δs Δt : DialectSet} {Vs Vt : Type}
    {sourceSat : Witness Vs F → Module Δs n F → Prop}
    {targetSat : Witness Vt F → Module Δt n F → Prop}
    (pass : StructuralPass
      (ModuleStage.ofWitness Vs sourceSat)
      (ModuleStage.ofWitness Vt targetSat))
    (total : TotalStructural pass) :
    PresReflPass
      (ModuleStage.language Vs sourceSat)
      (ModuleStage.language Vt targetSat) where
  compile m := (total.run m).val
  witnessRel m sourceState targetState :=
    pass.stateRel m (total.run m).val sourceState targetState
  preservation := by
    intro sourceState m hsatisfies
    exact pass.preservation m (total.run m).val sourceState
      (total.run m).property hsatisfies
  reflection := by
    intro targetState m hsatisfies
    exact pass.reflection m (total.run m).val targetState
      (total.run m).property hsatisfies

@[simp] theorem ofPresReflPass_compose_lower
    {Δ₀ Δ₁ Δ₂ : DialectSet} {V₀ V₁ V₂ : Type}
    {sat₀ : Witness V₀ F → Module Δ₀ n F → Prop}
    {sat₁ : Witness V₁ F → Module Δ₁ n F → Prop}
    {sat₂ : Witness V₂ F → Module Δ₂ n F → Prop}
    (pass₁ : PresReflPass
      (ModuleStage.language V₀ sat₀) (ModuleStage.language V₁ sat₁))
    (pass₂ : PresReflPass
      (ModuleStage.language V₁ sat₁) (ModuleStage.language V₂ sat₂))
    (m : Module Δ₀ n F) :
    (ofPresReflPass (PresReflPass.compose pass₁ pass₂)).lower m =
      ((ofPresReflPass pass₁).compose (ofPresReflPass pass₂)).lower m := by
  rfl

theorem ofPresReflPass_compose_stateRel_iff
    {Δ₀ Δ₁ Δ₂ : DialectSet} {V₀ V₁ V₂ : Type}
    {sat₀ : Witness V₀ F → Module Δ₀ n F → Prop}
    {sat₁ : Witness V₁ F → Module Δ₁ n F → Prop}
    {sat₂ : Witness V₂ F → Module Δ₂ n F → Prop}
    (pass₁ : PresReflPass
      (ModuleStage.language V₀ sat₀) (ModuleStage.language V₁ sat₁))
    (pass₂ : PresReflPass
      (ModuleStage.language V₁ sat₁) (ModuleStage.language V₂ sat₂))
    (m : Module Δ₀ n F) (state₀ : Witness V₀ F)
    (state₂ : Witness V₂ F) :
    (ofPresReflPass (PresReflPass.compose pass₁ pass₂)).stateRel
        m (pass₂.compile (pass₁.compile m)) state₀ state₂ ↔
      ((ofPresReflPass pass₁).compose (ofPresReflPass pass₂)).stateRel
        m (pass₂.compile (pass₁.compile m)) state₀ state₂ := by
  simp only [ofPresReflPass, compose, PresReflPass.compose]
  constructor
  · rintro ⟨state₁, hrel₁, hrel₂⟩
    exact ⟨pass₁.compile m, state₁, rfl, hrel₁, hrel₂⟩
  · rintro ⟨mid, state₁, hmid, hrel₁, hrel₂⟩
    simp only [Except.ok.injEq] at hmid
    subst mid
    exact ⟨state₁, hrel₁, hrel₂⟩

end StructuralPass

/-! ## Small reusable structural-state relations -/

variable {State : Type}

/-- A statically typed view of the field-valued local component of a richer
semantic state. Extra state remains abstract and pass-specific. -/
structure LocalStateView (State : Type) (F : Type) where
  read : State → LocalVar → F

/-- Target locals renamed by `ρ` agree with source locals. -/
def StateAgreesUnder (view : LocalStateView State F)
    (ρ : LocalVar → LocalVar) (source target : State) : Prop :=
  ∀ v, view.read target (ρ v) = view.read source v

/-- A transition preserves all field locals except its declared destination. -/
def PreservesLocalsOutside (view : LocalStateView State F)
    (dest : Option LocalVar) (before after : State) : Prop :=
  ∀ v, dest ≠ some v → view.read after v = view.read before v

omit [Field F] in
theorem StateAgreesUnder.id (view : LocalStateView State F) (state : State) :
    StateAgreesUnder view id state state := by
  intro v
  rfl

omit [Field F] in
theorem StateAgreesUnder.comp
    (view : LocalStateView State F) (ρ σ : LocalVar → LocalVar)
    {state₀ state₁ state₂ : State}
    (h₁ : StateAgreesUnder view ρ state₀ state₁)
    (h₂ : StateAgreesUnder view σ state₁ state₂) :
    StateAgreesUnder view (σ ∘ ρ) state₀ state₂ := by
  intro v
  rw [Function.comp_apply, h₂, h₁]

omit [Field F] in
theorem PreservesLocalsOutside.trans
    (view : LocalStateView State F) (dest : Option LocalVar)
    {state₀ state₁ state₂ : State}
    (h₁ : PreservesLocalsOutside view dest state₀ state₁)
    (h₂ : PreservesLocalsOutside view dest state₁ state₂) :
    PreservesLocalsOutside view dest state₀ state₂ := by
  intro v hv
  rw [h₂ v hv, h₁ v hv]

end Dialect
