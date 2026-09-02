import Heyting.Dialects.StructObject
import Mathlib.Algebra.Field.Rat

namespace Dialect.StructObject.Tests

open Dialect

abbrev F := ℚ
def ctx : OpCtx := ⟨1, 0, 1⟩
def member0 : Fin ctx.numMembers := ⟨0, by simp [ctx]⟩

def initial : State F where
  values := fun v => if v = 0 then 9 else 0
  objects := fun _ => []
  witness := fun key => if key = ([], 0) then 7 else 0
  nextPath := 0

def allocated := apply (.newStruct 1 : Op ctx F) initial
#guard allocated.objects 1 == []
#guard allocated.nextPath == 1

def read := apply (.readMember 2 1 member0 : Op ctx F) allocated
#guard read.values 2 == 7
#guard read.objects 2 == [0]

def written := apply (.writeMember 1 member0 0 : Op ctx F) allocated
#guard written.witness ([], 0) == 9

end Dialect.StructObject.Tests
