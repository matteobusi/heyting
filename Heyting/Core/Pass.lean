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

  This is CC~ (trace-relating compiler correctness) from Abate et al. (ESOP
  2020), equivalent here to TPσ and TPτ.
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

/-! ## Composition of PresReflPass instances -/

/-- Compose two PresReflPass instances to get a PresReflPass for the composition.
    
    Given `S --[pass1]--> M --[pass2]--> T`, produces `S --[compose]--> T`.
    
    The composed witness relation chains through the intermediate witness:
    `witnessRel_comp p ws wt := ∃ wm, witnessRel1 p ws wm ∧ witnessRel2 (compile1 p) wm wt`
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
    -- Apply pass1 preservation
    obtain ⟨wm, hwrel1, hsat1⟩ := pass1.preservation ws p hs
    -- Apply pass2 preservation
    obtain ⟨wt, hwrel2, hsat2⟩ := pass2.preservation wm (pass1.compile p) hsat1
    -- Combine
    exact ⟨wt, ⟨wm, hwrel1, hwrel2⟩, hsat2⟩
  reflection := by
    intro wt p hs
    -- Apply pass2 reflection
    obtain ⟨wm, hwrel2, hsat2⟩ := pass2.reflection wt (pass1.compile p) hs
    -- Apply pass1 reflection
    obtain ⟨ws, hwrel1, hsat1⟩ := pass1.reflection wm p hsat2
    -- Combine
    exact ⟨ws, ⟨wm, hwrel1, hwrel2⟩, hsat1⟩
