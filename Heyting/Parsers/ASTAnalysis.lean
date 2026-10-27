/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashMap
import Heyting.Parsers.AST

/-!
# LLZK AST analysis

Shared, dialect-agnostic analysis used before typed dialect lowering. This module
contains no compiler IR and carries no semantic correctness claim.
-/

namespace LLZK.ASTAnalysis

open Std

/-- Split `"Struct::function"` into struct and function names. -/
def parseCallTarget (target : String) : String × String :=
  match target.splitOn "::" with
  | [] => ("", "")
  | [bare] => ("", bare)
  | parts => ("::".intercalate parts.dropLast, parts.getLast!)

private def collectMemberDeps : LLZK.Ty → List String
  | .structTy name => [name]
  | _ => []

private def collectStmtDeps (currentStruct : String) : LLZK.Stmt → List String
  | .call _ _ target _ =>
      let (structName, _) := parseCallTarget target
      if structName.isEmpty || structName == currentStruct then [] else [structName]
  | _ => []

private def collectStructDeps (sd : LLZK.StructDef) : List String :=
  let memberDeps := sd.members.flatMap (fun member => collectMemberDeps member.ty)
  let stmtDeps := sd.funcs.flatMap (fun fn => fn.body.flatMap (collectStmtDeps sd.name))
  (memberDeps ++ stmtDeps).eraseDups

/-- Reject duplicate struct names rather than resolving them to one definition. -/
def checkUniqueStructs (structs : List LLZK.StructDef) : Except String Unit := do
  let names := structs.map (·.name)
  if let some dup := names.find? (fun name => names.count name > 1) then
    throw s!"duplicate struct definition: @{dup}"

/-- Topologically sort structs so every in-module dependency precedes its user.
Duplicate struct names are rejected. -/
partial def topoSort (structs : List LLZK.StructDef) :
    Except String (List LLZK.StructDef) := do
  if structs.isEmpty then return []
  checkUniqueStructs structs
  let nameMap : HashMap String LLZK.StructDef :=
    structs.foldl (fun result sd => result.insert sd.name sd) ∅
  let mut indegree : HashMap String Nat :=
    structs.foldl (fun result sd => result.insert sd.name 0) ∅
  let mut dependents : HashMap String (List String) :=
    structs.foldl (fun result sd => result.insert sd.name []) ∅
  for sd in structs do
    for dep in collectStructDeps sd do
      if nameMap.contains dep then
        indegree := indegree.insert sd.name ((indegree.getD sd.name 0) + 1)
        dependents := dependents.insert dep ((dependents.getD dep []) ++ [sd.name])
  let mut queue := structs.filterMap fun sd =>
    if indegree.getD sd.name 0 == 0 then some sd.name else none
  let mut sorted : List LLZK.StructDef := []
  let mut visited := 0
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
            for dependent in dependents.getD name [] do
              let newDegree := (indegree.getD dependent 0) - 1
              indegree := indegree.insert dependent newDegree
              if newDegree == 0 then queue := queue ++ [dependent]
  if visited < structs.length then
    let remaining := structs.filterMap fun sd =>
      if !sorted.any (fun candidate => candidate.name == sd.name) then some sd.name else none
    throw s!"cyclic struct dependencies: {", ".intercalate remaining}"
  return sorted

/-- Build struct-name to topological-index map. -/
def buildStructIndex (sorted : List LLZK.StructDef) : HashMap String Nat :=
  sorted.zipIdx.foldl
    (fun result (entry : LLZK.StructDef × Nat) => result.insert entry.1.name entry.2) ∅

/-- SSA name defined by a statement, if any. -/
def stmtDest : LLZK.Stmt → Option String
  | .feltAdd _ dest _ _ | .feltSub _ dest _ _ | .feltMul _ dest _ _
  | .feltDiv _ dest _ _ | .feltNeg _ dest _ | .feltInv _ dest _
  | .feltConst _ dest _ | .structNew _ dest _ | .readMember _ dest _ _
  | .call _ (some dest) _ _ | .nondet _ dest => some dest
  | .writeMember .. | .constrainEq .. | .funcReturn .. | .call _ none _ _ => none

/-- Assign dense local indices to parameters and statement destinations.
A name defined twice (two parameters, or a parameter and a statement, or two statements)
is rejected: SSA forbids it, and a map would silently keep only the last definition. -/
def buildSSAMap (params : List LLZK.ParamDecl) (body : List LLZK.Stmt) :
    Except String (HashMap String Nat) := do
  let names := params.map (·.name) ++ body.filterMap stmtDest
  let mut result : HashMap String Nat := ∅
  for (name, index) in names.zipIdx do
    if result.contains name then
      throw s!"SSA value %{name} is defined more than once"
    result := result.insert name index
  pure result

/-- Structs that no other struct depends on. -/
def rootStructs (structs : List LLZK.StructDef) : List String :=
  let used := structs.flatMap fun sd => (collectStructDeps sd).filter (· != sd.name)
  (structs.map (·.name)).filter fun name => !used.contains name

/-- Select the entry struct: the root `llzk.main` attribute when present (as in upstream
LLZK), otherwise the unique struct that no other struct uses. Several candidates are an
error rather than an arbitrary choice. -/
def selectEntry (m : LLZK.Module) : Except String String := do
  checkUniqueStructs m.structs
  match m.main with
  | some name =>
    unless m.structs.any (·.name == name) do
      throw s!"llzk.main names unknown struct @{name}"
    pure name
  | none =>
    match rootStructs m.structs with
    | [name] => pure name
    | [] => throw "no entry struct: every struct is used by another struct"
    | names => throw s!"ambiguous entry struct: candidates {names.map (s!"@{·}")}; \
add `llzk.main = !struct.type<@Name>` to the root module"

/-- Restrict a module to the selected entry struct and the structs it uses, directly or
transitively. Removed structs cannot affect the entry circuit. Free functions are kept, so
lowering still rejects them. After the
restriction the entry is the only root, so `topoSort` places it last, which is the entry
position used by lowering and witness execution. -/
partial def restrictToEntry (m : LLZK.Module) : Except String LLZK.Module := do
  let entry ← selectEntry m
  let byName : HashMap String LLZK.StructDef :=
    m.structs.foldl (fun t sd => t.insert sd.name sd) ∅
  let rec visit (pending : List String) (seen : List String) : List String :=
    match pending with
    | [] => seen
    | name :: rest =>
      if seen.contains name then visit rest seen
      else
        let deps := (byName.get? name).map collectStructDeps |>.getD []
        visit (deps ++ rest) (name :: seen)
  let reachable := visit [entry] []
  let structs := m.structs.filter (reachable.contains ·.name)
  let sorted ← topoSort structs
  unless sorted.getLast?.map (·.name) == some entry do
    throw s!"entry struct @{entry} is used by another struct it uses"
  pure { m with structs, main := some entry }

end LLZK.ASTAnalysis
