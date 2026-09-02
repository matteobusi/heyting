import Heyting.Dialects.TypedSourceSemantics
import Mathlib.Algebra.Field.Rat

namespace Dialect.TypedSourceSemantics.Tests

open Dialect

abbrev F := ℚ

def pos : LLZK.Pos := { line := 1, col := 1 }
def feltParam (name : String) : LLZK.ParamDecl := { name, ty := .felt }
def objectParam (name typeName : String) : LLZK.ParamDecl :=
  { name, ty := .structTy typeName }

def constrain (params : List LLZK.ParamDecl) (body : List LLZK.Stmt) :
    LLZK.FuncDef where
  name := "constrain"
  params
  returnType := none
  body := body ++ [.funcReturn pos none]
  pos

def member : LLZK.MemberDecl where
  name := "value"
  ty := .felt
  isPublic := true
  pos

/-- Root calls Leaf directly; Leaf reads the root object and checks it against
the positional input. -/
def nestedObjectCall : LLZK.Module where
  structs := [
    {
      name := "Root"
      members := [member]
      funcs := [constrain [objectParam "self" "Root", feltParam "x"] [
        .call pos none "Leaf::constrain" ["self", "x"]]]
      pos
    },
    {
      name := "Leaf"
      members := [member]
      funcs := [constrain [objectParam "self" "Leaf", feltParam "x"] [
        .readMember pos "actual" "self" "value",
        .feltConst pos "one" 1,
        .feltAdd pos "expected" "x" "one",
        .constrainEq pos "actual" "expected"]]
      pos
    }]
  freeFuncs := []
  pos

def directResult (input object : F) : Option Bool :=
  match LLZK.DialectLowering.lowerFull (F := F) nestedObjectCall with
  | .error _ => none
  | .ok ⟨k, module⟩ =>
    let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    some (checkAt module entry [input] [object])

#guard directResult 6 7 == some true
#guard directResult 7 7 == some false

def oracleCtx : OpCtx := ⟨1, 0, 0⟩
def oracleStmt : Stmt ResidualSet oracleCtx F :=
  .op ⟨1, by simp [ResidualSet]⟩ (.next 0)

def emptyState : State F := initialState 0 0 [] []

example : (evalLeaf oracleStmt emptyState).2 = false := by
  simp [evalLeaf, oracleStmt]

end Dialect.TypedSourceSemantics.Tests
