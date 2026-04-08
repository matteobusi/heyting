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

/-! ## SSA → LocalVar mapping -/

/-- Assign monotonic `Nat` indices to SSA names.
    Params get indices 0, 1, 2, … in order.
    Assignment destinations in the body get the next available index.
    `feltInv` reserves TWO consecutive indices (one for the hidden temp var, one for the dest). -/
def buildSSAMap (params : List LLZK.ParamDecl) (body : List LLZK.Stmt) :
    HashMap String Nat :=
  let initMap : HashMap String Nat × Nat :=
    params.foldl (fun (m, next) p => (m.insert p.name next, next + 1)) (∅, 0)
  let (map, _) := body.foldl (fun (m, next) stmt =>
    match stmt with
    | .feltAdd _ dest _ _   => (m.insert dest next, next + 1)
    | .feltSub _ dest _ _   => (m.insert dest next, next + 1)
    | .feltMul _ dest _ _   => (m.insert dest next, next + 1)
    | .feltDiv _ dest _ _   => (m.insert dest next, next + 1)
    | .feltNeg _ dest _     => (m.insert dest next, next + 1)
    | .feltConst _ dest _   => (m.insert dest next, next + 1)
    | .structNew _ dest _   => (m.insert dest next, next + 1)
    | .readMember _ dest _ _ => (m.insert dest next, next + 1)
    | .call _ (some dest) _ _ => (m.insert dest next, next + 1)
    | .nondet _ dest        => (m.insert dest next, next + 1)
    | .feltInv _ dest _ =>
      -- Reserve `next` for the hidden const-1 temp, `next+1` for dest
      (m.insert dest (next + 1), next + 2)
    | .writeMember _ _ _ _  => (m, next)
    | .constrainEq _ _ _    => (m, next)
    | .funcReturn _ _       => (m, next)
    | .call _ none _ _      => (m, next)
    | .skipped _ _          => (m, next)
  ) initMap
  map

/-- Look up an SSA name in the map; returns an error message if not found. -/
private def lookupSSA (ssaMap : HashMap String Nat) (name : String) :
    Except String Nat :=
  match ssaMap.get? name with
  | some n => return n
  | none   => throw s!"undefined SSA variable: %{name}"

/-! ## Constrain body lowering -/

/-- Lower a list of LLZK statements to a `ConstrainStmt` list.

    Parameters:
    - `n`           : total number of structs in the module
    - `i`           : index of the *current* struct (must be `< n`)
    - `hi`          : proof that `i < n`
    - `structIndex` : struct name → module index
    - `memberIndex` : member name → member index
    - `ssaMap`      : SSA name → `LocalVar`
    - `numMembers`  : number of members for the current struct -/
def lowerConstrainBody {F : Type} [IntCast F] (n i : Nat) (hi : i < n)
    (structIndex memberIndex : HashMap String Nat)
    (ssaMap : HashMap String Nat) (numMembers : Nat)
    (stmts : List LLZK.Stmt) :
    Except String (List (StructIR.ConstrainStmt n ⟨i, hi⟩ F numMembers)) := do
  let maxVar := ssaMap.toList.foldl (fun acc (_, v) => max acc v) 0
  let mut nextVar : Nat := maxVar + 1
  let mut result : List (StructIR.ConstrainStmt n ⟨i, hi⟩ F numMembers) := []
  for stmt in stmts do
    match stmt with
    | .feltAdd _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltAdd d s1 s2]
    | .feltSub _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltSub d s1 s2]
    | .feltMul _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltMul d s1 s2]
    | .feltDiv _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltDiv d s1 s2]
    | .feltNeg _ dest src =>
      let d ← lookupSSA ssaMap dest
      let s ← lookupSSA ssaMap src
      result := result ++ [.feltNeg d s]
    | .feltConst _ dest value =>
      let d ← lookupSSA ssaMap dest
      result := result ++ [.feltConst d (Int.cast value : F)]
    | .feltInv _ dest src =>
      -- Lower to: feltConst tmp 1, feltDiv dest tmp src
      let tmp := nextVar
      nextVar := nextVar + 1
      let d ← lookupSSA ssaMap dest
      let s ← lookupSSA ssaMap src
      result := result ++ [
        .feltConst tmp (Int.cast (1 : Int) : F),
        .feltDiv d tmp s
      ]
    | .readMember _ dest self member =>
      let d  ← lookupSSA ssaMap dest
      let sv ← lookupSSA ssaMap self
      match memberIndex.get? member with
      | none => throw s!"unknown member: @{member}"
      | some mIdx =>
        if hm : mIdx < numMembers then
          result := result ++ [.readMember d sv ⟨mIdx, hm⟩]
        else
          throw s!"member index {mIdx} ≥ numMembers={numMembers}"
    | .constrainEq _ src1 src2 =>
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.constrainEq s1 s2]
    | .call _ none target args =>
      -- Void call in constrain body
      let (structName, _) := parseCallTarget target
      if structName.isEmpty then
        throw s!"bare call target in constrain body: {target}"
      match structIndex.get? structName with
      | none => throw s!"unknown callee struct: {structName}"
      | some j =>
        if hj : j < i then
          let argVars ← args.mapM (lookupSSA ssaMap)
          result := result ++ [.call ⟨j, hj⟩ argVars]
        else
          throw s!"call to {structName} (index {j}) is not < caller index {i}"
    | .call _ (some _) target args =>
      -- Call with dest in constrain: dest unused, lower as void call
      let (structName, _) := parseCallTarget target
      if structName.isEmpty then
        throw s!"bare call target in constrain body: {target}"
      match structIndex.get? structName with
      | none => throw s!"unknown callee struct: {structName}"
      | some j =>
        if hj : j < i then
          let argVars ← args.mapM (lookupSSA ssaMap)
          result := result ++ [.call ⟨j, hj⟩ argVars]
        else
          throw s!"call to {structName} (index {j}) is not < caller index {i}"
    | .funcReturn _ none => pure ()  -- void return: skip
    | .funcReturn _ (some _) => throw "constrain function must not return a value"
    | .nondet _ _ => throw "nondet is not valid in constrain body"
    -- compute-only ops: silently skip
    | .structNew _ _ _    => pure ()
    | .writeMember _ _ _ _ => pure ()
    | .skipped _ _        => pure ()
  return result

/-! ## Compute body lowering -/

/-- Lower LLZK statements to a `ComputeStmt` list.
    Returns `(stmts, returnVar)`.

    Parameters: same as `lowerConstrainBody`. -/
def lowerComputeBody {F : Type} [IntCast F] (n i : Nat) (hi : i < n)
    (structIndex memberIndex : HashMap String Nat)
    (ssaMap : HashMap String Nat) (numMembers : Nat)
    (stmts : List LLZK.Stmt) :
    Except String (List (StructIR.ComputeStmt n ⟨i, hi⟩ F numMembers) × Nat) := do
  let maxVar := ssaMap.toList.foldl (fun acc (_, v) => max acc v) 0
  let mut nextVar : Nat := maxVar + 1
  let mut returnVar : Nat := 0
  let mut result : List (StructIR.ComputeStmt n ⟨i, hi⟩ F numMembers) := []
  for stmt in stmts do
    match stmt with
    | .feltAdd _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltAdd d s1 s2]
    | .feltSub _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltSub d s1 s2]
    | .feltMul _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltMul d s1 s2]
    | .feltDiv _ dest src1 src2 =>
      let d  ← lookupSSA ssaMap dest
      let s1 ← lookupSSA ssaMap src1
      let s2 ← lookupSSA ssaMap src2
      result := result ++ [.feltDiv d s1 s2]
    | .feltNeg _ dest src =>
      let d ← lookupSSA ssaMap dest
      let s ← lookupSSA ssaMap src
      result := result ++ [.feltNeg d s]
    | .feltConst _ dest value =>
      let d ← lookupSSA ssaMap dest
      result := result ++ [.feltConst d (Int.cast value : F)]
    | .feltInv _ dest src =>
      -- Lower to: feltConst tmp 1, feltDiv dest tmp src
      let tmp := nextVar
      nextVar := nextVar + 1
      let d ← lookupSSA ssaMap dest
      let s ← lookupSSA ssaMap src
      result := result ++ [
        .feltConst tmp (Int.cast (1 : Int) : F),
        .feltDiv d tmp s
      ]
    | .readMember _ dest self member =>
      let d  ← lookupSSA ssaMap dest
      let sv ← lookupSSA ssaMap self
      match memberIndex.get? member with
      | none => throw s!"unknown member: @{member}"
      | some mIdx =>
        if hm : mIdx < numMembers then
          result := result ++ [.readMember d sv ⟨mIdx, hm⟩]
        else
          throw s!"member index {mIdx} ≥ numMembers={numMembers}"
    | .writeMember _ self member src =>
      let sv ← lookupSSA ssaMap self
      let s  ← lookupSSA ssaMap src
      match memberIndex.get? member with
      | none => throw s!"unknown member: @{member}"
      | some mIdx =>
        if hm : mIdx < numMembers then
          result := result ++ [.writeMember sv ⟨mIdx, hm⟩ s]
        else
          throw s!"member index {mIdx} ≥ numMembers={numMembers}"
    | .structNew _ dest _ =>
      let d ← lookupSSA ssaMap dest
      result := result ++ [.newStruct d]
    | .call _ (some dest) target args =>
      let (structName, _) := parseCallTarget target
      if structName.isEmpty then
        throw s!"bare call target in compute body: {target}"
      match structIndex.get? structName with
      | none => throw s!"unknown callee struct: {structName}"
      | some j =>
        if hj : j < i then
          let d       ← lookupSSA ssaMap dest
          let argVars ← args.mapM (lookupSSA ssaMap)
          result := result ++ [.call d ⟨j, hj⟩ argVars]
        else
          throw s!"call to {structName} (index {j}) is not < caller index {i}"
    | .call _ none target args =>
      -- Void compute call: use dest=0 as dummy
      let (structName, _) := parseCallTarget target
      if structName.isEmpty then
        throw s!"bare call target in compute body: {target}"
      match structIndex.get? structName with
      | none => throw s!"unknown callee struct: {structName}"
      | some j =>
        if hj : j < i then
          let argVars ← args.mapM (lookupSSA ssaMap)
          result := result ++ [.call 0 ⟨j, hj⟩ argVars]
        else
          throw s!"call to {structName} (index {j}) is not < caller index {i}"
    | .nondet _ dest =>
      -- Placeholder: lower nondet to feltConst dest 0
      let d ← lookupSSA ssaMap dest
      result := result ++ [.feltConst d (Int.cast (0 : Int) : F)]
    | .funcReturn _ (some v) =>
      match ssaMap.get? v with
      | some rv => returnVar := rv
      | none    => throw s!"funcReturn: undefined SSA variable: %{v}"
    | .funcReturn _ none => throw "compute function must return a value"
    | .constrainEq _ _ _ => pure ()  -- constrain-only, skip
    | .skipped _ _       => pure ()  -- skip silently
  return (result, returnVar)

/-! ## Single-struct lowering -/

/-- Lower a single LLZK struct to a StructIR StructDef at index `⟨i, hi⟩`
    in a module of `n` structs. -/
def lowerStruct {F : Type} [Field F] [IntCast F] (n i : Nat) (hi : i < n)
    (structIndex : HashMap String Nat)
    (sd : LLZK.StructDef) :
    Except String (StructIR.StructDef n ⟨i, hi⟩ F) := do
  -- 1. Lower members
  let members ← lowerMembers n structIndex sd.members
  let memberIndex := buildMemberIndex sd.members
  -- 2. Find @constrain and @compute functions
  let constrainFunc := sd.funcs.find? (fun f => f.name == "constrain")
  let computeFunc   := sd.funcs.find? (fun f => f.name == "compute")
  -- 3. Lower constrain body
  let constrainBody : List (StructIR.ConstrainStmt n ⟨i, hi⟩ F members.length) ←
    match constrainFunc with
    | none => pure []
    | some f =>
      let ssaMap := buildSSAMap f.params f.body
      lowerConstrainBody n i hi structIndex memberIndex ssaMap members.length f.body
  let constrainNumParams : Nat :=
    match constrainFunc with
    | none => 1
    | some f => f.params.length
  -- 4. Lower compute body
  let computeBodyRet : List (StructIR.ComputeStmt n ⟨i, hi⟩ F members.length) × Nat ←
    match computeFunc with
    | none => pure ([], 0)
    | some f =>
      let ssaMap := buildSSAMap f.params f.body
      lowerComputeBody n i hi structIndex memberIndex ssaMap members.length f.body
  let computeBody := computeBodyRet.1
  let computeReturnVar := computeBodyRet.2
  let computeNumParams : Nat :=
    match computeFunc with
    | none => 1
    | some f => f.params.length
  -- 5. Assemble StructDef
  return {
    name := sd.name
    members := members
    compute := {
      numParams := computeNumParams
      body := computeBody
      returnVar := computeReturnVar
    }
    constrain := {
      numParams := constrainNumParams
      body := constrainBody
    }
  }

/-! ## Dependent struct function builder -/

/-- Recursively lower structs `[0..k)`, building a partial lookup function
    `∀ (j : Fin n), j.val < k → StructDef n j F`.
    The inductive step adds struct at index `k-1`. -/
private def lowerStructsRec {F : Type} [Field F] [IntCast F]
    (n : Nat) (sorted : List LLZK.StructDef) (structIndex : HashMap String Nat)
    (k : Nat) (hk : k ≤ n) :
    Except String (∀ (j : Fin n), j.val < k → StructIR.StructDef n j F) := do
  match k with
  | 0 => return fun _ h => absurd h (Nat.not_lt_zero _)
  | k' + 1 =>
    let prev ← lowerStructsRec n sorted structIndex k' (Nat.le_of_succ_le hk)
    let hk' : k' < n := hk
    match sorted[k']? with
    | none => throw s!"internal: sorted[{k'}] missing (sorted.length={sorted.length})"
    | some sd =>
      let sdef ← lowerStruct n k' hk' structIndex sd
      return fun j hj =>
        if hjk' : j.val < k' then
          prev j hjk'
        else
          have hjeq : j.val = k' := by omega
          have hjfin : j = ⟨k', hk'⟩ := Fin.ext hjeq
          hjfin ▸ sdef

/-- Build the full dependent function `(j : Fin n) → StructDef n j F`
    by lowering all `n` structs from `sorted`. -/
private def buildStructsFn {F : Type} [Field F] [IntCast F]
    (n : Nat) (sorted : List LLZK.StructDef) (structIndex : HashMap String Nat) :
    Except String ((j : Fin n) → StructIR.StructDef n j F) := do
  let f ← lowerStructsRec n sorted structIndex n le_rfl
  return fun j => f j j.isLt

/-! ## Top-level lowering entry point -/

/-- Top-level lowering: LLZK.Module → StructIR.Module.

    Returns `Σ n, StructIR.Module (n+1) F` since the number of structs
    is determined at runtime from the input module.

    Steps:
    1. Topological sort (leaves first, root = main last)
    2. Lower each struct to `StructIR.StructDef`
    3. Assemble `StructIR.Module` with `noDupReads` check via `decide` -/
def LLZK.lower {F : Type} [Field F] [DecidableEq F] [IntCast F]
    (m : LLZK.Module) : Except String (Σ n, StructIR.Module (n + 1) F) := do
  if m.structs.isEmpty then
    throw "empty module: nothing to lower"
  -- 1. Topological sort
  let sorted ← LLZK.Lowering.topoSort m.structs
  -- Guard: topoSort preserves non-emptiness; capture as a Prop
  if h : sorted.length = 0 then
    throw "internal: topoSort returned empty list for non-empty module"
  else
  let n := sorted.length
  have hn : 0 < n := Nat.pos_of_ne_zero h
  -- 2. Build struct index (name → topo-sort position)
  let structIndex := LLZK.Lowering.buildStructIndex sorted
  -- 3. Lower all structs into the dependent function
  let structsFn ← LLZK.Lowering.buildStructsFn n sorted structIndex
  -- 4. Check noDupReads at the top-level (main = last struct, index n-1)
  let mainIdx : Fin n := ⟨n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
  let initObjEnv : StructIR.ObjEnv := StructIR.ObjEnv.update (fun _ => []) 0 []
  let positions :=
    StructIR.readPositions structsFn mainIdx initObjEnv (structsFn mainIdx).constrain.body
  if hnodup : positions.Nodup then
    -- 5. Assemble the Module
    let module : StructIR.Module n F := {
      structs := structsFn
      -- proof irrelevance: both hn and hn' prove 0 < n, so mainIdx is the same Fin value
      noDupReads := fun _ => hnodup
    }
    -- Package as Σ m, Module (m+1) F where m = n-1
    have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    return ⟨n - 1, hn1 ▸ module⟩
  else
    throw "duplicate reads in constrain body — struct members must be read at most once"

end LLZK.Lowering
