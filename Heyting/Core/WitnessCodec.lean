/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass

/-!
# Constructive witness codecs and compilation artifacts

`PresReflPass` records existential equisatisfiability.  The CLI needs a
stronger, constructive object: the exact target program and the exact witness
codec for that program must be produced together.

Artifacts operate only on canonical language witnesses. Transient interpreter
state (locals, call frames, allocation counters, oracle cursors) is projected
away before transport starts, so readback can be exact.
-/

namespace WitnessCodec

variable {Vs Vm Vt Fs Fm Ft : Type}
variable [Field Fs] [Field Fm] [Field Ft]
variable {S : Language Vs Fs} {M : Language Vm Fm} {T : Language Vt Ft}

/-- A compiled target program together with its constructive witness mapping
and pointwise correctness laws. -/
structure CompilationArtifact
    (S : Language Vs Fs) (T : Language Vt Ft) (source : S.Program) where
  target : T.Program
  forward : Witness Vs Fs → Except String (Witness Vt Ft)
  readback : Witness Vt Ft → Witness Vs Fs
  witnessRel : Witness Vs Fs → Witness Vt Ft → Prop
  forward_rel : ∀ ws wt, forward ws = .ok wt → witnessRel ws wt
  satisfies_iff : ∀ ws wt, forward ws = .ok wt →
    (S.satisfies ws source ↔ T.satisfies wt target)
  readback_forward : ∀ ws wt, forward ws = .ok wt → readback wt = ws

namespace CompilationArtifact

/-- Identity artifact. -/
def identity (source : S.Program) : CompilationArtifact S S source where
  target := source
  forward ws := .ok ws
  readback := id
  witnessRel ws wt := ws = wt
  forward_rel := by
    intro ws wt h
    exact Except.ok.inj h
  satisfies_iff := by
    intro ws wt h
    have hwt : ws = wt := Except.ok.inj h
    subst wt
    rfl
  readback_forward := by
    intro ws wt h
    have hwt : ws = wt := Except.ok.inj h
    subst wt
    rfl

/-- Compose proof-carrying artifacts. The executable forward maps are composed
with `Except.bind`; readback composes in the opposite direction. -/
def compose {source : S.Program}
    (first : CompilationArtifact S M source)
    (second : CompilationArtifact M T first.target) :
    CompilationArtifact S T source where
  target := second.target
  forward ws := first.forward ws >>= second.forward
  readback wt := first.readback (second.readback wt)
  witnessRel ws wt := ∃ wm, first.witnessRel ws wm ∧ second.witnessRel wm wt
  forward_rel := by
    intro ws wt h
    cases hfirst : first.forward ws with
    | error error =>
      rw [hfirst] at h
      cases h
    | ok wm =>
      have hsecond : second.forward wm = .ok wt := by
        simpa [hfirst] using h
      exact ⟨wm, first.forward_rel ws wm hfirst,
        second.forward_rel wm wt hsecond⟩
  satisfies_iff := by
    intro ws wt h
    cases hfirst : first.forward ws with
    | error error =>
      rw [hfirst] at h
      cases h
    | ok wm =>
      have hsecond : second.forward wm = .ok wt := by
        simpa [hfirst] using h
      exact (first.satisfies_iff ws wm hfirst).trans
        (second.satisfies_iff wm wt hsecond)
  readback_forward := by
    intro ws wt h
    cases hfirst : first.forward ws with
    | error error =>
      rw [hfirst] at h
      cases h
    | ok wm =>
      have hsecond : second.forward wm = .ok wt := by
        simpa [hfirst] using h
      rw [second.readback_forward wm wt hsecond]
      exact first.readback_forward ws wm hfirst

@[simp] theorem identity_forward (source : S.Program) (ws : Witness Vs Fs) :
    (identity source).forward ws = .ok ws := rfl

@[simp] theorem identity_readback (source : S.Program) (ws : Witness Vs Fs) :
    (identity source).readback ws = ws := rfl

end CompilationArtifact

/-- A pass whose compilation result constructively transports witnesses and
proves pointwise correctness for every successful transport. -/
structure WitnessTransportingPass
    (S : Language Vs Fs) (T : Language Vt Ft) where
  compileArtifact : (source : S.Program) → Except String (CompilationArtifact S T source)

/-- Constructive evidence that artifact compilation and forward transport are
total. This is deliberately separate from existential `PresReflPass`. -/
structure TotalTransport
    (pass : WitnessTransportingPass S T) where
  compile : ∀ source, { artifact // pass.compileArtifact source = .ok artifact }
  forward : ∀ source (ws : Witness Vs Fs),
    { wt // (compile source).val.forward ws = .ok wt }

/-- A transporting pass with exact source-witness readback. Every artifact
already carries the round-trip law; this alias names the stronger API role. -/
abbrev RoundTripPass
    (S : Language Vs Fs) (T : Language Vt Ft) := WitnessTransportingPass S T

end WitnessCodec
