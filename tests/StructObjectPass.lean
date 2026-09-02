import Heyting.Dialects.StructObjectPass
import Mathlib.Algebra.Field.Rat

namespace Dialect.StructObjectPass.Tests

open Dialect

abbrev F := ℚ
def ctx : OpCtx := ⟨1, 0, 1⟩
def member0 : Fin ctx.numMembers := ⟨0, by simp [ctx]⟩

def sourceBody : List (Stmt SourceSet ctx F) := [
  .op ⟨0, by simp [SourceSet, ObjectResidualSemantics.Set]⟩
    (.readMember 2 0 member0),
  .op ⟨2, by simp [SourceSet, ObjectResidualSemantics.Set]⟩ (.eq 2 1)]

def span := witnessSpan StaticState.initial.objects 0 sourceBody
def lowered := lowerBody 2 span StaticState.initial sourceBody

#guard span == encodedMember [] 0 + 1
#guard lowered.1.length == 1

-- The read destination is replaced by its encoded witness parameter.
def loweredConstraintReadsWitness : Bool :=
  match lowered.1 with
  | [.op ⟨1, _⟩ (.eq a b)] => a == witnessLocal 2 [] 0 && b == 1
  | _ => false

#guard loweredConstraintReadsWitness

#check encodeTargetState_rel
#check decodeSourceState_rel
#check structuralPass
#check callThenObjectPass

end Dialect.StructObjectPass.Tests
