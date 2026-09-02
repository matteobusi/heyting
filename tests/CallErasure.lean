import Heyting.Passes.DialectPipeline
import Heyting.Dialects.ObjectCallSemantics
import Mathlib.Algebra.Field.Rat

namespace Dialect.CallErasure.Tests

open Dialect

abbrev F := ℚ

def pos : LLZK.Pos := { line := 1, col := 1 }
def feltParam (name : String) : LLZK.ParamDecl := { name := name, ty := .felt }
def objectParam (name typeName : String) : LLZK.ParamDecl :=
  { name := name, ty := .structTy typeName }

def constrain (params : List LLZK.ParamDecl) (body : List LLZK.Stmt) : LLZK.FuncDef where
  name := "constrain"
  params := params
  returnType := none
  body := body ++ [.funcReturn pos none]
  pos := pos

def member : LLZK.MemberDecl where
  name := "value"
  ty := .felt
  isPublic := true
  pos := pos

/-- Root → Middle → Leaf, where the leaf body contains StructObject.readMember.
All layouts have one member, so the member index transports into each caller
context. -/
def nestedObjectCalls : LLZK.Module where
  structs := [
    {
      name := "Root"
      members := [member]
      funcs := [constrain [objectParam "self" "Root", feltParam "x"] [
        .call pos none "Middle::constrain" ["self", "x"]]]
      pos := pos
    },
    {
      name := "Middle"
      members := [member]
      funcs := [constrain [objectParam "self" "Middle", feltParam "x"] [
        .call pos none "Leaf::constrain" ["self", "x"]]]
      pos := pos
    },
    {
      name := "Leaf"
      members := [member]
      funcs := [constrain [objectParam "self" "Leaf", feltParam "x"] [
        .readMember pos "actual" "self" "value",
        .constrainEq pos "actual" "x"]]
      pos := pos
    }]
  freeFuncs := []
  pos := pos

def erasedRootShape : Option (Nat × Nat × Nat) :=
  match LLZK.DialectLowering.lower (F := F) nestedObjectCalls with
  | .error _ => none
  | .ok ⟨k, m⟩ =>
    let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    match eraseConstrainFunc (objectFeltConstrainSyntax (F := F)) m entry with
    | none => none
    | some (body, _) =>
      match body with
      | [.op first _, .op second _] => some (2, first.val, second.val)
      | body => some (body.length, 99, 99)

-- Both calls disappear; the residual StructObject and ConstrainEq ops remain.
#guard erasedRootShape == some (2, 0, 2)

def nestedObjectCallObservations : Option (Bool × Bool) :=
  match LLZK.DialectLowering.lower (F := F) nestedObjectCalls with
  | .error _ => none
  | .ok ⟨k, m⟩ =>
    let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    match eraseConstrainFunc (objectFeltConstrainSyntax (F := F)) m entry with
    | none => none
    | some (body, _) =>
      let initial := TypedSourceSemantics.initialState
        (m.structs entry).constrain.numParams
        (m.structs entry).compute.numParams [] []
      some (TypedSourceSemantics.checkProjectedAt m entry [] [],
        (ObjectCallSemantics.evalTargetBody body initial).2)

-- Direct nested-call execution equals hygienically expanded execution.
#guard nestedObjectCallObservations == some (true, true)

def backendCompilesObjects : Bool :=
  match Pipeline.compileAST (F := F) nestedObjectCalls with
  | .error _ => false
  | .ok _ => true

-- The executable composes Call and StructObject erasure.
#guard backendCompilesObjects

def objectCtx : OpCtx := ⟨1, 0, 1⟩
def objectMember : Fin objectCtx.numMembers := ⟨0, by simp [objectCtx]⟩

def objectInitial : StructObject.State F where
  values := fun v => if v = 0 then 7 else 0
  objects := fun _ => []
  witness := fun key => if key = ([], 0) then 7 else 0
  nextPath := 0

def objectResidualBody : List (Stmt ObjectResidualSemantics.Set objectCtx F) := [
  .op ⟨0, by simp [ObjectResidualSemantics.Set]⟩
    (.readMember 1 0 objectMember),
  .op ⟨2, by simp [ObjectResidualSemantics.Set]⟩ (.eq 1 0)]

example : (ObjectResidualSemantics.evalBody objectResidualBody objectInitial).2 := by
  norm_num [ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
    objectResidualBody, objectInitial, StructObject.apply, StructObject.ValueEnv.update]

#check ObjectResidualSemantics.eraseCallPass
#check CallErasure.eraseModule_struct
#check ObjectCallSemantics.eraseBodyInto_constrain_simulation
#check ObjectCallSemantics.eraseConstrainFunc_checkProjectedAt_eq
#check ObjectCallSemantics.structuralPrefix_check_eq
#check ObjectCallSemantics.structuralPrefix_satisfies_iff

noncomputable def composedObjectCallPass (n : Nat) :=
  (ObjectResidualSemantics.eraseCallPass n F).compose
    (StructuralPass.identity (ObjectResidualSemantics.stage n F))

end Dialect.CallErasure.Tests
