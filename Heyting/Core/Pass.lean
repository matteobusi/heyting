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
