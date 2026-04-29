import Heyting.Languages.StructInlineIR
import Heyting.Passes.StructIRToStructInlineIR
import Heyting.Passes.StructInlineIRToMemberlessIR

open StructInlineIR

example (n : Nat) {F : Type} [Field F] :
    Language StructIR.VarId F := by
  letI := StructInlineIR.Language n F
  infer_instance

example {n : Nat} {F : Type} (s : ConstrainStmt n F) : True := by
  cases s with
  | feltAdd _ _ _ => trivial
  | feltSub _ _ _ => trivial
  | feltMul _ _ _ => trivial
  | feltDiv _ _ _ => trivial
  | feltNeg _ _ => trivial
  | feltConst _ _ => trivial
  | readMember _ _ _ => trivial
  | constrainEq _ _ => trivial

example {n : Nat} {F : Type} [Field F]
    (m : StructIR.Module (n + 1) F) (w : StructIR.Witness F) :
    StructIRToStructInlineIR.witnessRel m w w := by
  simp [StructIRToStructInlineIR.witnessRel]

example {n : Nat} {F : Type} [Field F]
    (m : StructInlineIR.Module (n + 1) F)
    (w : StructInlineIR.Witness F) :
    StructInlineIRToMemberlessIR.witnessRel m w
      (StructInlineIRToMemberlessIR.compileWitness m w) := by
  intro k
  rfl
