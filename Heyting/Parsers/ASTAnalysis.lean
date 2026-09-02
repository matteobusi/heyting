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

/-- Topologically sort structs so every in-module dependency precedes its user. -/
partial def topoSort (structs : List LLZK.StructDef) :
    Except String (List LLZK.StructDef) := do
  if structs.isEmpty then return []
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

/-- Assign dense local indices to parameters and statement destinations. -/
def buildSSAMap (params : List LLZK.ParamDecl) (body : List LLZK.Stmt) :
    HashMap String Nat :=
  let initial : HashMap String Nat × Nat :=
    params.foldl
      (fun (result, next) param => (result.insert param.name next, next + 1)) (∅, 0)
  body.foldl (fun (result, next) stmt =>
    match stmt with
    | .feltAdd _ dest _ _ | .feltSub _ dest _ _ | .feltMul _ dest _ _
    | .feltDiv _ dest _ _ | .feltNeg _ dest _ | .feltInv _ dest _
    | .feltConst _ dest _ | .structNew _ dest _ | .readMember _ dest _ _
    | .call _ (some dest) _ _ | .nondet _ dest => (result.insert dest next, next + 1)
    | .writeMember .. | .constrainEq .. | .funcReturn .. | .call _ none _ _
    | .skipped .. => (result, next)) initial |>.1

end LLZK.ASTAnalysis
