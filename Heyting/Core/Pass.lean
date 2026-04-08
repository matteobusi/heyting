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
  -- Preservation: compiler doesn't add extra constraints
  -- If ws satisfies the source, it exists wt that satisfies the target
  preservation :
    ∀ (ws : Witness Vs Fs) (p : S.Program), S.satisfies ws p →
      ∃ (wt : Witness Vt Ft), witnessRel p ws wt ∧ T.satisfies wt (compile p)

class ReflectingPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  -- Reflection: compiler doesn't remove constraints.
  -- This is "classical" compiler correctness:
  -- If wt satisfies the target, it exists ws that satisfies the source
  reflection :
    ∀ (wt : Witness Vt Ft) (p : S.Program), T.satisfies wt (compile p) →
      ∃ ws, witnessRel p ws wt ∧ S.satisfies ws p

class PresReflPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T, PreservingPass S T, ReflectingPass S T
