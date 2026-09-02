import Heyting.Passes.DialectPipeline
import Heyting.Legacy.Pipeline
import Mathlib.Algebra.Field.Rat

namespace LLZK.DialectLowering.Tests

abbrev F := ℚ

def pos : Pos := { line := 1, col := 1 }
def feltParam (name : String) : ParamDecl := { name := name, ty := .felt }

def constrain (params : List ParamDecl) (body : List LLZK.Stmt) : LLZK.FuncDef where
  name := "constrain"
  params := params
  returnType := none
  body := body ++ [.funcReturn pos none]
  pos := pos

def oneStruct : LLZK.Module where
  structs := [{
    name := "Main"
    members := []
    funcs := [constrain [feltParam "a", feltParam "b"] [
      .feltAdd pos "sum" "a" "b",
      .feltConst pos "five" 5,
      .constrainEq pos "sum" "five"]]
    pos := pos
  }]
  freeFuncs := []
  pos := pos

def dialectCount (ast : LLZK.Module) : Option Nat :=
  (Dialect.Pipeline.compileAST (F := F) ast).toOption.map (·.constraints.length)

def legacyCount (ast : LLZK.Module) : Option Nat :=
  match LLZK.Lowering.LLZK.lower (F := F) ast with
  | .error _ => none
  | .ok ⟨_, m⟩ =>
    some (Legacy.Pipeline.compileProgram (F := F) m).constraints.length

def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard dialectCount oneStruct == some 3
-- The legacy StructIR route adds two main-parameter binding constraints.
#guard legacyCount oneStruct == some 5

def calledModule : LLZK.Module where
  structs := [
    {
      name := "Root"
      members := []
      funcs := [constrain [feltParam "x"] [
        .call pos none "Leaf::constrain" ["x"]]]
      pos := pos
    },
    {
      name := "Leaf"
      members := []
      funcs := [constrain [feltParam "x"] [
        .feltConst pos "one" 1,
        .constrainEq pos "x" "one"]]
      pos := pos
    }]
  freeFuncs := []
  pos := pos

-- The root is topologically sorted last and its call is erased by inlining.
#guard dialectCount calledModule == some 2
-- Legacy call/object plumbing contributes two additional constraints.
#guard legacyCount calledModule == some 4

def unsupportedStructOp : LLZK.Module where
  structs := [{
    name := "Main"
    members := []
    funcs := [constrain [] [.structNew pos "self" "Main"]]
    pos := pos
  }]
  freeFuncs := []
  pos := pos

#guard failed (Dialect.Pipeline.compileAST (F := F) unsupportedStructOp)

def objectModule : LLZK.Module where
  structs := [{
    name := "ObjectMain"
    members := [{
      name := "value"
      ty := .felt
      isPublic := true
      pos := pos
    }]
    funcs := [{
      name := "compute"
      params := [feltParam "x"]
      returnType := some (.structTy "ObjectMain")
      body := [
        .structNew pos "self" "ObjectMain",
        .writeMember pos "self" "value" "x",
        .funcReturn pos (some "self")]
      pos := pos
    }, constrain [
      { name := "self", ty := .structTy "ObjectMain" }, feltParam "x"] [
        .readMember pos "actual" "self" "value",
        .constrainEq pos "actual" "x"]]
    pos := pos
  }]
  freeFuncs := []
  pos := pos

def objectBodyLengths : Option (Nat × Nat) :=
  match lower (F := F) objectModule with
  | .error _ => none
  | .ok ⟨k, m⟩ =>
    let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    some ((m.structs entry).compute.body.length,
      (m.structs entry).constrain.body.length)

-- Struct operations now survive the primary typed frontend boundary.
#guard objectBodyLengths == some (2, 2)
-- The executable backend projection rejects them at its explicit boundary.
#guard failed (lowerCallCompatible (F := F) objectModule)

def malformedCall : LLZK.Module where
  structs := calledModule.structs.map fun sd =>
    if sd.name == "Root" then
      { sd with funcs := [constrain [feltParam "x"] [
          .call pos none "Leaf::constrain" []]] }
    else sd
  freeFuncs := []
  pos := pos

-- The AST becomes a typed source module, but call erasure rejects bad arity.
#guard failed (Dialect.Pipeline.compileAST (F := F) malformedCall)

end LLZK.DialectLowering.Tests
