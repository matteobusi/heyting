/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Language

/-!
# Compiler Pass Interfaces

Shared pass interfaces for Heyting's correctness framework.

`Pass` records executable compilation plus witness relation. `PreservingPass`
and `ReflectingPass` package completeness and soundness directions, and
`PresReflPass` combines both into the main correctness notion used by proved
passes in this repository.
-/

/--
A compiler pass between two languages, consisting of a program translation and
a relation between source and target witnesses.
-/
class Pass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) where
  /-- Compile a source program into a target program. -/
  compile : S.Program → T.Program
  /-- Relate a source witness and a target witness for a given source program. -/
  witnessRel : S.Program → Witness Vs Fs → Witness Vt Ft → Prop


/--
A pass that preserves satisfiability: every satisfying source witness can be
transported to a related satisfying target witness.
-/
class PreservingPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  /--
  Preservation / completeness: compilation does not add spurious constraints.
  -/
  preservation :
    ∀ (ws : Witness Vs Fs) (p : S.Program), S.satisfies ws p →
      ∃ (wt : Witness Vt Ft), witnessRel p ws wt ∧ T.satisfies wt (compile p)

/--
A pass that reflects satisfiability: every satisfying target witness comes from
a related satisfying source witness.
-/
class ReflectingPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  /--
  Reflection / soundness: compilation does not lose constraints.

  The target witness is arbitrary; it need not be produced by a witness generator.
  -/
  reflection :
    ∀ (wt : Witness Vt Ft) (p : S.Program), T.satisfies wt (compile p) →
      ∃ ws, witnessRel p ws wt ∧ S.satisfies ws p

/-- A pass that satisfies both preservation and reflection. -/
class PresReflPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T, PreservingPass S T, ReflectingPass S T

/-! ## Composition of ReflectingPass instances -/

/-- Compose reflection through a shared intermediate language.

Proof sketch: reflect the target witness through the second pass, then reflect
the resulting intermediate witness through the first pass. The intermediate
witness establishes the existentially composed relation. -/
def ReflectingPass.compose
  {Vs Vm Vt : Type} {Fs Fm Ft : Type}
  [Field Fs] [Field Fm] [Field Ft]
  {S : Language Vs Fs} {M : Language Vm Fm} {T : Language Vt Ft}
  (pass1 : ReflectingPass S M) (pass2 : ReflectingPass M T) :
  ReflectingPass S T where
  compile := pass2.compile ∘ pass1.compile
  witnessRel p ws wt :=
    ∃ wm, pass1.witnessRel p ws wm ∧ pass2.witnessRel (pass1.compile p) wm wt
  reflection := by
    intro wt p hs
    obtain ⟨wm, hwrel2, hsat2⟩ := pass2.reflection wt (pass1.compile p) hs
    obtain ⟨ws, hwrel1, hsat1⟩ := pass1.reflection wm p hsat2
    exact ⟨ws, ⟨wm, hwrel1, hwrel2⟩, hsat1⟩

/-! ## Composition of PresReflPass instances -/

/-- Compose preservation and reflection through the same intermediate language.

The witness relation existentially quantifies an intermediate witness related
by both passes. The intermediate satisfaction predicate must agree exactly.

Proof sketch: preservation applies the two local preservation laws in execution
order; reflection applies the reflection laws in reverse order. In each case,
retain the intermediate witness to prove the composed relation.
-/
def PresReflPass.compose
  {Vs Vm Vt : Type} {Fs Fm Ft : Type}
  [Field Fs] [Field Fm] [Field Ft]
  {S : Language Vs Fs} {M : Language Vm Fm} {T : Language Vt Ft}
  (pass1 : PresReflPass S M) (pass2 : PresReflPass M T) :
  PresReflPass S T where
  compile := pass2.compile ∘ pass1.compile
  witnessRel p ws wt :=
    ∃ wm, pass1.witnessRel p ws wm ∧ pass2.witnessRel (pass1.compile p) wm wt
  preservation := by
    intro ws p hs
    obtain ⟨wm, hwrel1, hsat1⟩ := pass1.preservation ws p hs
    obtain ⟨wt, hwrel2, hsat2⟩ := pass2.preservation wm (pass1.compile p) hsat1
    exact ⟨wt, ⟨wm, hwrel1, hwrel2⟩, hsat2⟩
  reflection := by
    intro wt p hs
    obtain ⟨wm, hwrel2, hsat2⟩ := pass2.reflection wt (pass1.compile p) hs
    obtain ⟨ws, hwrel1, hsat1⟩ := pass1.reflection wm p hsat2
    exact ⟨ws, ⟨wm, hwrel1, hwrel2⟩, hsat1⟩
