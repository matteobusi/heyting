/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashMap
import Heyting.Parsers.ASTAnalysis
import Heyting.Dialects.CallPass
import Heyting.Dialects.StructObject
import Heyting.Dialects.Oracle

/-!
# LLZK AST to dialect module lowering

Typed frontend boundary for the dialect-native pipeline:

```text
LLZK.Module → Dialect.Module [Call, StructObject, Felt, ConstrainEq]
```

Witness lowering uses a dedicated Oracle dialect.  The constraint projection
explicitly erases oracle reads to zero because compute bodies do not contribute
constraints; dialect witness execution consumes the preserved oracle stream.
Functions are accepted only after executable capability and SSA checks provide
the proofs required by `Dialect.FuncDef`. A separate call-compatible lowering
temporarily rejects object operations for the current backend path.
-/

namespace LLZK.DialectLowering

open Std Dialect
open Dialect.CallPass

/-- Object-aware frontend set. This is now the primary typed AST boundary. -/
abbrev SourceSet : DialectSet :=
  [Call.sig, StructObject.sig, Felt.sig, ConstrainEq.sig]

/-- Compute-side source set retaining witness-only oracle operations. -/
abbrev WitnessSourceSet : DialectSet :=
  [Call.sig, StructObject.sig, Oracle.sig, Felt.sig, ConstrainEq.sig]

/-- Backend-compatible subset retained while struct-object erasure is pending. -/
abbrev CallCompatibleSet := CallPass.SourceSet

def callIx : Fin SourceSet.length := ⟨0, by simp [SourceSet]⟩
def structIx : Fin SourceSet.length := ⟨1, by simp [SourceSet]⟩
def feltIx : Fin SourceSet.length := ⟨2, by simp [SourceSet]⟩
def constrainEqIx : Fin SourceSet.length := ⟨3, by simp [SourceSet]⟩

/-- Embeddings used by the common AST traversal. Struct operations may be
rejected by a compatibility builder without duplicating frontend logic. -/
structure Builder (Δ : DialectSet) where
  call : ∀ {γ : OpCtx} {F : Type}, Call.Op γ F → Dialect.Stmt Δ γ F
  felt : ∀ {γ : OpCtx} {F : Type}, Felt.Op γ F → Dialect.Stmt Δ γ F
  constrainEq : ∀ {γ : OpCtx} {F : Type},
    ConstrainEq.Op γ F → Dialect.Stmt Δ γ F
  structObject : ∀ {γ : OpCtx} {F : Type},
    StructObject.Op γ F → Except String (Dialect.Stmt Δ γ F)
  oracle : ∀ {γ : OpCtx} {F : Type} [OfNat F 0],
    Oracle.Op γ F → Dialect.Stmt Δ γ F

def fullBuilder : Builder SourceSet where
  call op := .op callIx op
  felt op := .op feltIx op
  constrainEq op := .op constrainEqIx op
  structObject op := .ok (.op structIx op)
  oracle op := match op with
    | .next dest => .op feltIx (.const dest 0)

def witnessBuilder : Builder WitnessSourceSet where
  call op := .op ⟨0, by simp [WitnessSourceSet]⟩ op
  structObject op := .ok (.op ⟨1, by simp [WitnessSourceSet]⟩ op)
  oracle op := .op ⟨2, by simp [WitnessSourceSet]⟩ op
  felt op := .op ⟨3, by simp [WitnessSourceSet]⟩ op
  constrainEq op := .op ⟨4, by simp [WitnessSourceSet]⟩ op

def callCompatibleBuilder : Builder CallCompatibleSet where
  call op := .op callSourceIx op
  felt op := .op feltSourceIx op
  constrainEq op := .op constrSourceIx op
  structObject _ := .error
    "struct-object erasure is not implemented for the backend-compatible source set"
  oracle op := match op with
    | .next dest => .op feltSourceIx (.const dest 0)

private def lookupSSA (ssaMap : HashMap String Nat) (name : String) :
    Except String Nat :=
  match ssaMap.get? name with
  | some n => .ok n
  | none => .error s!"undefined SSA variable: %{name}"

private def buildMemberIndex (decls : List LLZK.MemberDecl) : HashMap String Nat :=
  decls.zipIdx.foldl
    (fun result (entry : LLZK.MemberDecl × Nat) =>
      result.insert entry.1.name entry.2) ∅

private def lookupMember (memberIndex : HashMap String Nat) (numMembers : Nat)
    (name : String) : Except String (Fin numMembers) := do
  let index ← match memberIndex.get? name with
    | some index => pure index
    | none => throw s!"unknown member: @{name}"
  if h : index < numMembers then pure ⟨index, h⟩
  else throw s!"member index {index} ≥ numMembers={numMembers}"

def lowerMemberType (n : Nat) (structIndex : HashMap String Nat)
    (ty : LLZK.Ty) : Except String (Dialect.MemberType n) :=
  match ty with
  | .felt => .ok .felt
  | .structTy name =>
    match structIndex.get? name with
    | none => .error s!"unknown struct type: {name}"
    | some j =>
      if h : j < n then .ok (.substruct ⟨j, h⟩)
      else .error s!"struct type {name} has index {j} ≥ n={n}"
  | .other name => .error s!"unsupported member type: {name}"

def lowerMembers (n : Nat) (structIndex : HashMap String Nat)
    (decls : List LLZK.MemberDecl) :
    Except String (List (Dialect.MemberDecl n)) :=
  decls.mapM fun member => do
    let ty ← lowerMemberType n structIndex member.ty
    pure { name := member.name, type := ty, isPublic := member.isPublic }

private def requireCallTarget (kind : String) (target : String) :
    Except String String := do
  let (structName, functionName) := LLZK.ASTAnalysis.parseCallTarget target
  if structName.isEmpty then
    throw s!"bare call target in {kind} body: {target}"
  if functionName != kind then
    throw s!"{kind} body cannot call @{target}; expected @{structName}::@{kind}"
  pure structName

def lowerComputeBody {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [IntCast F] [OfNat F 0]
    (n i : Nat) (structIndex : HashMap String Nat)
    (memberIndex ssaMap : HashMap String Nat) (numMembers : Nat)
    (stmts : List LLZK.Stmt) :
    Except String
      (List (Dialect.Stmt Δ ⟨n, i, numMembers⟩ F) × Option LocalVar) := do
  let mut result : List (Dialect.Stmt Δ ⟨n, i, numMembers⟩ F) := []
  let mut returnVar : Option LocalVar := none
  for stmt in stmts do
    match stmt with
    | .feltAdd _ dest a b =>
      result := result ++ [builder.felt
        (.add (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltSub _ dest a b =>
      result := result ++ [builder.felt
        (.sub (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltMul _ dest a b =>
      result := result ++ [builder.felt
        (.mul (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltDiv _ dest a b =>
      result := result ++ [builder.felt
        (.div (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltNeg _ dest src =>
      result := result ++ [builder.felt
        (.neg (← lookupSSA ssaMap dest) (← lookupSSA ssaMap src))]
    | .feltInv _ dest src =>
      result := result ++ [builder.felt
        (.inv (← lookupSSA ssaMap dest) (← lookupSSA ssaMap src))]
    | .feltConst _ dest value =>
      result := result ++ [builder.felt
        (.const (← lookupSSA ssaMap dest) (Int.cast value : F))]
    | .call _ dest target args =>
      let structName ← requireCallTarget "compute" target
      let j ← match structIndex.get? structName with
        | some j => pure j
        | none => throw s!"unknown callee struct: {structName}"
      if hj : j < i then
        let destVar ← dest.mapM (lookupSSA ssaMap)
        let argVars ← args.mapM (lookupSSA ssaMap)
        result := result ++ [builder.call (.call destVar ⟨j, hj⟩ 0 argVars)]
      else
        throw s!"call to {structName} (index {j}) is not < caller index {i}"
    | .funcReturn _ value =>
      returnVar ← value.mapM (lookupSSA ssaMap)
    | .constrainEq _ _ _ =>
      throw "constrain.eq is not valid in compute body"
    | .structNew _ dest _ =>
      result := result ++ [← builder.structObject
        (.newStruct (← lookupSSA ssaMap dest))]
    | .readMember _ dest self member =>
      result := result ++ [← builder.structObject
        (.readMember (← lookupSSA ssaMap dest) (← lookupSSA ssaMap self)
          (← lookupMember memberIndex numMembers member))]
    | .writeMember _ self member src =>
      result := result ++ [← builder.structObject
        (.writeMember (← lookupSSA ssaMap self)
          (← lookupMember memberIndex numMembers member)
          (← lookupSSA ssaMap src))]
    | .nondet _ dest =>
      result := result ++ [builder.oracle (F := F)
        (.next (← lookupSSA ssaMap dest))]
    | .skipped _ opName =>
      throw s!"unsupported parsed operation in compute body: {opName}"
  pure (result, returnVar)

def lowerConstrainBody {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [IntCast F]
    (n i : Nat) (structIndex : HashMap String Nat)
    (memberIndex ssaMap : HashMap String Nat) (numMembers : Nat)
    (stmts : List LLZK.Stmt) :
    Except String (List (Dialect.Stmt Δ ⟨n, i, numMembers⟩ F)) := do
  let mut result : List (Dialect.Stmt Δ ⟨n, i, numMembers⟩ F) := []
  for stmt in stmts do
    match stmt with
    | .feltAdd _ dest a b =>
      result := result ++ [builder.felt
        (.add (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltSub _ dest a b =>
      result := result ++ [builder.felt
        (.sub (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltMul _ dest a b =>
      result := result ++ [builder.felt
        (.mul (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltDiv _ dest a b =>
      result := result ++ [builder.felt
        (.div (← lookupSSA ssaMap dest) (← lookupSSA ssaMap a)
          (← lookupSSA ssaMap b))]
    | .feltNeg _ dest src =>
      result := result ++ [builder.felt
        (.neg (← lookupSSA ssaMap dest) (← lookupSSA ssaMap src))]
    | .feltInv _ dest src =>
      result := result ++ [builder.felt
        (.inv (← lookupSSA ssaMap dest) (← lookupSSA ssaMap src))]
    | .feltConst _ dest value =>
      result := result ++ [builder.felt
        (.const (← lookupSSA ssaMap dest) (Int.cast value : F))]
    | .constrainEq _ a b =>
      result := result ++ [builder.constrainEq
        (.eq (← lookupSSA ssaMap a) (← lookupSSA ssaMap b))]
    | .call _ none target args =>
      let structName ← requireCallTarget "constrain" target
      let j ← match structIndex.get? structName with
        | some j => pure j
        | none => throw s!"unknown callee struct: {structName}"
      if hj : j < i then
        let argVars ← args.mapM (lookupSSA ssaMap)
        result := result ++ [builder.call (.call none ⟨j, hj⟩ 0 argVars)]
      else
        throw s!"call to {structName} (index {j}) is not < caller index {i}"
    | .call _ (some _) _ _ =>
      throw "constraint calls must not have a destination"
    | .funcReturn _ none => pure ()
    | .funcReturn _ (some _) =>
      throw "constrain function must not return a value"
    | .readMember _ dest self member =>
      result := result ++ [← builder.structObject
        (.readMember (← lookupSSA ssaMap dest) (← lookupSSA ssaMap self)
          (← lookupMember memberIndex numMembers member))]
    | .structNew _ _ _ | .writeMember _ _ _ _ =>
      throw "struct allocation and writes are not valid in constrain body"
    | .nondet _ _ =>
      throw "llzk.nondet is not valid in constrain body"
    | .skipped _ opName =>
      throw s!"unsupported parsed operation in constrain body: {opName}"
  pure result

def certifyFunc {Δ : DialectSet} {F : Type}
    {n i numMembers : Nat} {kind : Capability}
    (label : String) (numParams : Nat)
    (body : List (Dialect.Stmt Δ ⟨n, i, numMembers⟩ F))
    (returnVar : Option LocalVar) :
    Except String (Dialect.FuncDef Δ n i F kind numMembers) :=
  if hcaps : capsLE kind body = true then
    if hssa : isSSA (fun v => decide (v < numParams)) body = true then
      .ok {
        numParams := numParams
        body := body
        returnVar := returnVar
        wf_caps := hcaps
        wf_ssa := hssa
      }
    else .error s!"{label} body fails SSA check"
  else .error s!"{label} body contains operations with invalid capabilities"

def lowerStruct {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F]
    (n i : Nat) (hi : i < n) (structIndex : HashMap String Nat)
    (sd : LLZK.StructDef) :
    Except String (Dialect.StructDef Δ n ⟨i, hi⟩ F) := do
  let members ← lowerMembers n structIndex sd.members
  let memberIndex := buildMemberIndex sd.members
  let computeAst := sd.funcs.find? (fun f => f.name == "compute")
  let constrainAst := sd.funcs.find? (fun f => f.name == "constrain")
  let computeNumParams := computeAst.map (·.params.length) |>.getD 1
  let constrainNumParams := constrainAst.map (·.params.length) |>.getD 1
  let computeRaw : List (Dialect.Stmt Δ ⟨n, i, members.length⟩ F) ×
      Option LocalVar ← match computeAst with
    | none => pure ([], none)
    | some fn =>
      lowerComputeBody (F := F) builder n i structIndex memberIndex
        (LLZK.ASTAnalysis.buildSSAMap fn.params fn.body) members.length fn.body
  let constrainRaw : List (Dialect.Stmt Δ ⟨n, i, members.length⟩ F) ←
    match constrainAst with
    | none => pure []
    | some fn =>
      lowerConstrainBody builder n i structIndex memberIndex
        (LLZK.ASTAnalysis.buildSSAMap fn.params fn.body) members.length fn.body
  let compute ← certifyFunc (kind := .witness) s!"{sd.name}::compute"
    computeNumParams computeRaw.1 computeRaw.2
  let constrain ← certifyFunc (kind := .constraint) s!"{sd.name}::constrain"
    constrainNumParams constrainRaw none
  pure {
    name := sd.name
    members := members
    compute := compute
    constrain := constrain
  }

private def lowerStructsRec {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F]
    (n : Nat) (sorted : List LLZK.StructDef)
    (structIndex : HashMap String Nat) (k : Nat) (hk : k ≤ n) :
    Except String
      (∀ j : Fin n, j.val < k → Dialect.StructDef Δ n j F) := do
  match k with
  | 0 => pure fun _ h => absurd h (Nat.not_lt_zero _)
  | k' + 1 =>
    let previous ← lowerStructsRec builder n sorted structIndex k'
      (Nat.le_of_succ_le hk)
    let hk' : k' < n := hk
    match sorted[k']? with
    | none => throw s!"internal: sorted[{k'}] missing (length={sorted.length})"
    | some ast =>
      let current ← lowerStruct builder n k' hk' structIndex ast
      pure fun j hj =>
        if hjk : j.val < k' then previous j hjk
        else
          have hval : j.val = k' := by omega
          have heq : j = ⟨k', hk'⟩ := Fin.ext hval
          heq ▸ current

private def buildStructsFn {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F]
    (n : Nat) (sorted : List LLZK.StructDef)
    (structIndex : HashMap String Nat) :
    Except String ((j : Fin n) → Dialect.StructDef Δ n j F) := do
  let lowered ← lowerStructsRec builder n sorted structIndex n le_rfl
  pure fun j => lowered j j.isLt

/-- Common top-level typed lowering parameterized by dialect embeddings. -/
def lowerWith {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module Δ (k + 1) F) := do
  if !m.freeFuncs.isEmpty then
    throw "module-level free functions parsed but not lowered yet"
  if m.structs.isEmpty then
    throw "empty module: nothing to lower"
  let sorted ← LLZK.ASTAnalysis.topoSort m.structs
  if hzero : sorted.length = 0 then
    throw "internal: topoSort returned an empty module"
  else
    let n := sorted.length
    have hn : 0 < n := Nat.pos_of_ne_zero hzero
    let structIndex := LLZK.ASTAnalysis.buildStructIndex sorted
    let structs ← buildStructsFn builder n sorted structIndex
    let result : Dialect.Module Δ n F := { structs := structs }
    have hshape : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    pure ⟨n - 1, hshape ▸ result⟩

/-- Primary object-aware AST boundary. -/
def lower {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module SourceSet (k + 1) F) :=
  lowerWith fullBuilder m

/-- Typed compute-side lowering preserving nondeterministic reads as Oracle
operations. -/
def lowerWitness {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module WitnessSourceSet (k + 1) F) :=
  lowerWith witnessBuilder m

/-- Full typed frontend boundary used by the primary pipeline. -/
def lowerFull {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module WitnessSourceSet (k + 1) F) :=
  lowerWitness (F := F) m

/-- Temporary executable projection used by the current constraint backend.
It traverses the same AST but rejects struct-object instructions precisely. -/
def lowerCallCompatible {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module CallCompatibleSet (k + 1) F) :=
  lowerWith callCompatibleBuilder m

end LLZK.DialectLowering
