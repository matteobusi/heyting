import Heyting.Core.Language

class Pass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) where
  compile : S.Program → T.Program
  witnessRel : S.Program → Witness Vs Fs → Witness Vt Ft → Prop


class PreservingPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  -- Preservation (completeness): the compiler doesn't add spurious constraints.
  -- If ws satisfies the source, there exists a related wt satisfying the target.
  -- This is an additional guarantee beyond CC~.
  preservation :
    ∀ (ws : Witness Vs Fs) (p : S.Program), S.satisfies ws p →
      ∃ (wt : Witness Vt Ft), witnessRel p ws wt ∧ T.satisfies wt (compile p)

class ReflectingPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  -- Reflection (soundness): the compiler doesn't lose constraints.
  -- If wt satisfies the target, there exists a related ws satisfying the source.
  -- This is CC~ (trace-relating compiler correctness) from Abate et al. (ESOP 2020),
  -- and is equivalent to TPσ and TPτ (proved in TrinitaryCC.lean).
  reflection :
    ∀ (wt : Witness Vt Ft) (p : S.Program), T.satisfies wt (compile p) →
      ∃ ws, witnessRel p ws wt ∧ S.satisfies ws p

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
