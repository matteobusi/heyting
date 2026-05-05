import Heyting.Core.CheckedSemantics
import Heyting.Languages.FlatIRChecked
import Heyting.Passes.MemberlessIRToFlatIR

namespace MemberlessIRToFlatIRChecked

open CheckedSemantics

variable {F : Type} [Field F] {n : Nat}

abbrev MainIdx (n : Nat) : Fin (n + 1) := Fin.last n

abbrev SourceStep (n : Nat) (F : Type) := MemberlessIR.Stmt (n + 1) (MainIdx n) F

abbrev TargetStep (F : Type) := FlatIR.Instr F

def sourceCheckedTrace (m : MemberlessIR.Module (n + 1) F) : List (SourceStep n F) :=
  (m (MainIdx n)).body

def targetCheckedTrace (m : MemberlessIR.Module (n + 1) F) : List (TargetStep F) :=
  MemberlessIRToFlatIR.compile m

def stepRel (_m : MemberlessIR.Module (n + 1) F) : SourceStep n F → TargetStep F → Prop
  | .feltAdd _ _ _, .assignAdd _ _ _ => True
  | .feltSub _ _ _, .assignSub _ _ _ => True
  | .feltMul _ _ _, .assignMul _ _ _ => True
  | .feltDiv _ _ _, .assignDiv _ _ _ => True
  | .feltNeg _ _, .assignNeg _ _ => True
  | .feltConst _ _, .assignConst _ _ => True
  | .constrainEq _ _, .assertEq _ _ => True
  | _, _ => False

def checkedTraceRel (m : MemberlessIR.Module (n + 1) F) : Prop :=
  BiTraceStutter (stepRel m) (sourceCheckedTrace m) (targetCheckedTrace m)

def forwardSimulationStatement (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F) : Prop :=
  MemberlessIR.satisfies mw m → checkedTraceRel m

def backwardSimulationStatement (m : MemberlessIR.Module (n + 1) F)
    (wt : FlatIR.Witness F) : Prop :=
  FlatIRChecked.checkedSuccess wt (MemberlessIRToFlatIR.compile m) →
    ∃ mw, MemberlessIRToFlatIR.witnessRel m mw wt

omit [Field F] in
theorem checkedTraceRel_nil :
    BiTraceStutter (R := fun (_ : SourceStep n F) (_ : TargetStep F) => True) [] [] :=
  ⟨TraceStutter.nil, TraceStutter.nil⟩

omit [Field F] in
theorem stepRel_feltAdd_assignAdd (m : MemberlessIR.Module (n + 1) F)
    (dest src1 src2 d t1 t2 : Nat) :
    stepRel m (.feltAdd dest src1 src2) (.assignAdd d t1 t2) := by
  simp [stepRel]

end MemberlessIRToFlatIRChecked
