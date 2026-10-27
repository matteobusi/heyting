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

/-- Root calls the constraints of its Leaf member; Leaf reads its own member and checks it
against the positional input. -/
def nestedObjectCall : LLZK.Module where
  structs := [
    {
      name := "Root"
      members := [{ name := "leaf", ty := .structTy "Leaf", isPublic := false, pos }]
      funcs := [constrain [objectParam "self" "Root", feltParam "x"] [
        .readMember pos "leaf" "self" "leaf",
        .call pos none "Leaf::constrain" ["leaf", "x"]]]
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
    -- `leaf.value` is coordinate `([0], 0)`, encoded as witness slot 2.
    some (checkAt module entry [input] [0, 0, object])

#guard directResult 6 7 == some true
#guard directResult 7 7 == some false

def oracleCtx : OpCtx := ⟨1, 0, 0⟩
def oracleStmt : Stmt ResidualSet oracleCtx F :=
  .op ⟨1, by simp [ResidualSet]⟩ (.next 0)

def emptyState : State F := initialState 0 0 [] []

example : (evalLeaf oracleStmt emptyState).2 = false := by
  simp [evalLeaf, oracleStmt]

end Dialect.TypedSourceSemantics.Tests
