import Std.Data.HashMap
import Heyting.Parser.Main
import Heyting.Languages.StructIR

/-!
# LLZK AST → StructIR Lowering

Unverified lowering pass from the LLZK untyped AST (`LLZK.Module`) to the
dependently-typed `StructIR.Module`. This is a pure `Except String` function
— no proofs, no `sorry`, no `native_decide`.

## Design decisions

- Topological sort: Kahn's algorithm (BFS-based, iterative with fuel)
- `feltInv dest src` → two stmts: `feltConst tmp 1` + `feltDiv dest tmp src`
- `nondet dest` in compute → `feltConst dest 0` (placeholder)
- `funcReturn` in compute → sets `returnVar`; in constrain → skip
- `noDupReads` discharged via decidable `List.Nodup` check at runtime
-/

namespace LLZK.Lowering

open Std StructIR

/-! ## Qualified name parsing -/

/-- Split a qualified call target like `"IsZero::constrain"` into `("IsZero", "constrain")`.
    For bare names like `"constrain"`, returns `("", "constrain")`. -/
def parseCallTarget (target : String) : String × String :=
  match target.splitOn "::" with
  | [] => ("", "")
  | [bare] => ("", bare)
  | parts =>
    let structName := "::".intercalate parts.dropLast
    let funcName := parts.getLast!
    (structName, funcName)

/-! ## Dependency collection -/

private def collectMemberDeps (ty : LLZK.Ty) : List String :=
  match ty with
  | .structTy name => [name]
  | _ => []

private def collectStmtDeps (stmt : LLZK.Stmt) : List String :=
  match stmt with
  | .call _ _ target _ =>
    let (structName, _) := parseCallTarget target
    if structName.isEmpty then [] else [structName]
  | _ => []

private def collectStructDeps (sd : LLZK.StructDef) : List String :=
  let memberDeps := sd.members.flatMap (fun m => collectMemberDeps m.ty)
  let stmtDeps := sd.funcs.flatMap (fun f => f.body.flatMap collectStmtDeps)
  (memberDeps ++ stmtDeps).eraseDups

/-! ## Topological sort -/

/-- Topological sort using Kahn's algorithm (BFS). Returns structs in dependency
    order: leaves first, root last. Cross-module references (deps not in the module)
    are silently ignored. -/
partial def topoSort (structs : List LLZK.StructDef) :
    Except String (List LLZK.StructDef) := do
  if structs.isEmpty then return []
  -- Build name → struct map
  let nameMap : HashMap String LLZK.StructDef :=
    structs.foldl (fun m sd => m.insert sd.name sd) ∅
  -- Build indegree map and adjacency list (dep → list of dependents)
  let mut indegree : HashMap String Nat :=
    structs.foldl (fun m sd => m.insert sd.name 0) ∅
  let mut dependents : HashMap String (List String) :=
    structs.foldl (fun m sd => m.insert sd.name []) ∅
  for sd in structs do
    let deps := collectStructDeps sd
    for dep in deps do
      if nameMap.contains dep then
        -- sd depends on dep → dep's removal decrements sd's indegree
        indegree := indegree.insert sd.name ((indegree.getD sd.name 0) + 1)
        dependents := dependents.insert dep ((dependents.getD dep []) ++ [sd.name])
  -- Collect zero-indegree nodes
  let mut queue : List String := structs.filterMap fun sd =>
    if indegree.getD sd.name 0 == 0 then some sd.name else none
  let mut sorted : List LLZK.StructDef := []
  let mut visited : Nat := 0
  while !queue.isEmpty do
    match queue with
    | [] => break
    | name :: rest =>
      queue := rest
      visited := visited + 1
      match nameMap.get? name with
      | none => throw s!"internal error: struct {name} not found"
      | some sd =>
        sorted := sorted ++ [sd]
        let deps := dependents.getD name []
        for dep in deps do
          let newDeg := (indegree.getD dep 0) - 1
          indegree := indegree.insert dep newDeg
          if newDeg == 0 then
            queue := queue ++ [dep]
  if visited < structs.length then
    let remaining := structs.filterMap fun sd =>
      if !sorted.any (fun s => s.name == sd.name) then some sd.name else none
    throw s!"cyclic struct dependencies: {", ".intercalate remaining}"
  return sorted

/-! ## Index assignment -/

/-- Build name → index map from topologically sorted struct list. -/
def buildStructIndex (sorted : List LLZK.StructDef) : HashMap String Nat :=
  sorted.zipIdx.foldl (fun m (p : LLZK.StructDef × Nat) => m.insert p.1.name p.2) ∅

/-! ## Member type resolution -/

/-- Lower an LLZK type to a StructIR member type.
    `n` = total number of structs in module. -/
def lowerMemberType (n : Nat) (structIndex : HashMap String Nat) (ty : LLZK.Ty) :
    Except String (StructIR.MemberType n) :=
  match ty with
  | .felt => return .felt
  | .structTy name =>
    match structIndex.get? name with
    | none => throw s!"unknown struct type: {name}"
    | some j =>
      if h : j < n then
        return .substruct ⟨j, h⟩
      else
        throw s!"struct type {name} has index {j} ≥ n={n}"
  | .other name => throw s!"unsupported member type: {name}"

/-- Lower a list of LLZK member decls. -/
def lowerMembers (n : Nat) (structIndex : HashMap String Nat)
    (decls : List LLZK.MemberDecl) : Except String (List (StructIR.MemberDecl n)) :=
  decls.mapM fun m => do
    let ty ← lowerMemberType n structIndex m.ty
    return { name := m.name, type := ty }

/-- Build member name → index map. -/
def buildMemberIndex (members : List LLZK.MemberDecl) : HashMap String Nat :=
  members.zipIdx.foldl (fun m (p : LLZK.MemberDecl × Nat) => m.insert p.1.name p.2) ∅

end LLZK.Lowering
