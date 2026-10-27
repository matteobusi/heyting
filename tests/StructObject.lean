import Heyting.Dialects.StructObject
import Mathlib.Algebra.Field.Rat

namespace Dialect.StructObject.Tests

open Dialect

abbrev F := ℚ
def ctx : OpCtx := ⟨1, 0, 1⟩

def initial : State F where
  values := fun v => if v = 0 then 9 else 0
  objects := fun _ => []
  witness := fun key => if key = ([0], 0) then 7 else 0
  nextPath := 0

-- Every allocation is a fresh singleton root.
def allocated := apply (.newStruct 1 : Op ctx F) initial
#guard allocated.objects 1 == [0]
#guard allocated.nextPath == 1

def read := apply (.readMember 2 1 0 : Op ctx F) allocated
#guard read.values 2 == 7
#guard read.objects 2 == [0, 0]

def written := apply (.writeMember 1 0 0 : Op ctx F) allocated
#guard written.witness ([0], 0) == 9

/-- A parent at `[1]` stores the child at `[0]` in its member 3: the child's subtree is copied
below `[1, 3]`, so the member tree, not allocation order, locates the sub-component. -/
def parent := apply (.newStruct 3 : Op ctx F) allocated
#guard parent.objects 3 == [1]

def stored := apply (.writeObject 3 3 1 : Op ctx F) parent
#guard stored.witness ([1, 3], 0) == 7
#guard stored.witness ([0], 0) == 7
#guard stored.witness ([1], 3) == 0

/-- Reading `@3` of the parent, then member `0`, gives the child's stored value
(`read_through_writeObject`). -/
def throughParent :=
  apply (.readMember 5 4 0 : Op ctx F) (apply (.readMember 4 3 3 : Op ctx F) stored)
#guard throughParent.values 5 == 7
#guard throughParent.objects 5 == [1, 3, 0]

end Dialect.StructObject.Tests
