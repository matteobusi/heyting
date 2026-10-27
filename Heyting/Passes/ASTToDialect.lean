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
LLZK.Module → Dialect.Module [Call, StructObject, Oracle, Felt, ConstrainEq]
```

`lowerFull` retains Oracle reads for witness execution. `lower` offers an Oracle-free
projection for constraint-only clients; the main pipeline uses explicit `OracleErasure`
after full typed lowering instead.
Functions are accepted only after executable capability and SSA checks provide
the proofs required by `Dialect.FuncDef`. These intrinsic certificates establish
well-formedness of the result, not fidelity to the untyped AST or upstream LLZK semantics.
Parsing, symbol/member resolution, and this translation remain unverified.

Before translation, `checkFunc` gives every SSA value a type (`!felt.type` or a struct
type) and rejects ill-typed programs instead of lowering them with a guessed meaning:
felt operations and `constrain.eq` need felt operands; `struct.readm`/`struct.writem`
resolve the member in the struct type of the object operand, not in the enclosing struct;
reads of another struct's members need `{llzk.pub}` (as in upstream LLZK); writes and
`struct.new` only target the enclosing struct; call arguments, results, member writes,
and returns must match the declared types.
-/

namespace LLZK.DialectLowering

open Std Dialect
open Dialect.CallPass

/-- Object-aware constraint projection without Oracle syntax. -/
abbrev SourceSet : DialectSet :=
  [Call.sig, StructObject.sig, Felt.sig, ConstrainEq.sig]

/-- Compute-side source set retaining witness-only oracle operations. -/
abbrev WitnessSourceSet : DialectSet :=
  [Call.sig, StructObject.sig, Oracle.sig, Felt.sig, ConstrainEq.sig]

def callIx : Fin SourceSet.length := ⟨0, by simp [SourceSet]⟩
def structIx : Fin SourceSet.length := ⟨1, by simp [SourceSet]⟩
def feltIx : Fin SourceSet.length := ⟨2, by simp [SourceSet]⟩
def constrainEqIx : Fin SourceSet.length := ⟨3, by simp [SourceSet]⟩

/-- Dialect embeddings shared by the full and Oracle-free AST traversals. -/
structure Builder (Δ : DialectSet) where
  call : ∀ {γ : OpCtx} {F : Type}, Call.Op γ F → Dialect.Stmt Δ γ F
  felt : ∀ {γ : OpCtx} {F : Type}, Felt.Op γ F → Dialect.Stmt Δ γ F
  constrainEq : ∀ {γ : OpCtx} {F : Type},
    ConstrainEq.Op γ F → Dialect.Stmt Δ γ F
  structObject : ∀ {γ : OpCtx} {F : Type},
    StructObject.Op γ F → Dialect.Stmt Δ γ F
  oracle : ∀ {γ : OpCtx} {F : Type} [OfNat F 0],
    Oracle.Op γ F → Dialect.Stmt Δ γ F

def fullBuilder : Builder SourceSet where
  call op := .op callIx op
  felt op := .op feltIx op
  constrainEq op := .op constrainEqIx op
  structObject op := .op structIx op
  oracle op := match op with
    | .next dest => .op feltIx (.const dest 0)

def witnessBuilder : Builder WitnessSourceSet where
  call op := .op ⟨0, by simp [WitnessSourceSet]⟩ op
  structObject op := .op ⟨1, by simp [WitnessSourceSet]⟩ op
  oracle op := .op ⟨2, by simp [WitnessSourceSet]⟩ op
  felt op := .op ⟨3, by simp [WitnessSourceSet]⟩ op
  constrainEq op := .op ⟨4, by simp [WitnessSourceSet]⟩ op

private def lookupSSA (ssaMap : HashMap String Nat) (name : String) :
    Except String Nat :=
  match ssaMap.get? name with
  | some n => .ok n
  | none => .error s!"undefined SSA variable: %{name}"

/-- AST struct table indexed by absolute struct name. -/
abbrev StructTable := HashMap String LLZK.StructDef

/-- Value types of the supported subset. -/
private def valueTypeName : LLZK.Ty → String
  | .felt => "!felt.type"
  | .structTy name => s!"!struct.type<@{name}>"
  | .other name => s!"!{name}"

private def sameType : LLZK.Ty → LLZK.Ty → Bool
  | .felt, .felt => true
  | .structTy a, .structTy b => a == b
  | _, _ => false

/-- Require a parameter or result type in the subset: `!felt.type` or a known struct. -/
private def checkValueType (table : StructTable) (what : String) :
    LLZK.Ty → Except String Unit
  | .felt => pure ()
  | .structTy name =>
    if table.contains name then pure () else throw s!"{what}: unknown struct type @{name}"
  | .other name => throw s!"{what}: unsupported type !{name}"

/-- Look up the struct a value of type `ty` refers to. -/
private def objectStruct (table : StructTable) (what : String) :
    LLZK.Ty → Except String LLZK.StructDef
  | .structTy name => match table.get? name with
    | some sd => pure sd
    | none => throw s!"{what}: unknown struct type @{name}"
  | ty => throw s!"{what}: expected a struct value, got {valueTypeName ty}"

/-- Resolve `obj[@member]` in the struct type of `obj`. Returns the member index and type.
`requirePublic` enforces the upstream rule that a struct reads only the public members of
another struct. -/
private def resolveMember (table : StructTable) (current : String) (objTy : LLZK.Ty)
    (member : String) (requirePublic : Bool) : Except String (Nat × LLZK.Ty) := do
  let sd ← objectStruct table s!"member @{member}" objTy
  match sd.members.zipIdx.find? (·.1.name == member) with
  | none => throw s!"unknown member: @{member} in struct @{sd.name}"
  | some (decl, index) =>
    if requirePublic && sd.name != current && !decl.isPublic then
      throw s!"struct @{current} reads private member @{member} of struct @{sd.name}; \
only {"{"}llzk.pub} members of other structs are readable"
    pure (index, decl.ty)

/-- Signature of `@kind` of struct `name`: parameter types and result type. A struct
without `@compute` has the implicit compute signature used by `lowerStruct`. -/
private def calleeSignature (table : StructTable) (structName kind : String) :
    Except String (List LLZK.Ty × Option LLZK.Ty) := do
  let sd ← match table.get? structName with
    | some sd => pure sd
    | none => throw s!"unknown callee struct: {structName}"
  match sd.funcs.find? (·.name == kind) with
  | some fn => pure (fn.params.map (·.ty), fn.returnType)
  | none => throw s!"callee @{structName} has no @{kind} function"

/-- Type-check one function body and return the type of every SSA value.
See the module documentation for the rules. -/
def checkFunc (table : StructTable) (current : String) (kind : String)
    (fn : LLZK.FuncDef) : Except String (HashMap String LLZK.Ty) := do
  let label := s!"@{current}::@{kind}"
  let mut env : HashMap String LLZK.Ty := ∅
  for param in fn.params do
    checkValueType table s!"{label} parameter %{param.name}" param.ty
    env := env.insert param.name param.ty
  if let some ty := fn.returnType then
    checkValueType table s!"{label} result" ty
  let typeOf (env : HashMap String LLZK.Ty) (name : String) : Except String LLZK.Ty :=
    match env.get? name with
    | some ty => pure ty
    | none => throw s!"{label}: undefined SSA variable: %{name}"
  let requireFelt (env : HashMap String LLZK.Ty) (pos : LLZK.Pos) (names : List String) :
      Except String Unit :=
    names.forM fun name => do
      let ty ← typeOf env name
      unless sameType ty .felt do
        throw s!"{pos}: {label}: %{name} has type {valueTypeName ty}, expected !felt.type"
  for stmt in fn.body do
    match stmt with
    | .feltAdd pos dest a b | .feltSub pos dest a b | .feltMul pos dest a b
    | .feltDiv pos dest a b =>
      requireFelt env pos [a, b]; env := env.insert dest .felt
    | .feltNeg pos dest a | .feltInv pos dest a =>
      requireFelt env pos [a]; env := env.insert dest .felt
    | .feltConst _ dest _ | .nondet _ dest => env := env.insert dest .felt
    | .constrainEq pos a b => requireFelt env pos [a, b]
    | .structNew pos dest name =>
      unless name == current do
        throw s!"{pos}: {label}: struct.new of @{name}; only the enclosing struct \
@{current} can be created"
      env := env.insert dest (.structTy name)
    | .readMember pos dest obj member =>
      let (_, ty) ← resolveMember table current (← typeOf env obj) member true
        |>.mapError (s!"{pos}: {label}: " ++ ·)
      env := env.insert dest ty
    | .writeMember pos obj member src =>
      let objTy ← typeOf env obj
      unless sameType objTy (.structTy current) do
        throw s!"{pos}: {label}: struct.writem on {valueTypeName objTy}; only members of \
the enclosing struct @{current} can be written"
      let (_, memberTy) ← resolveMember table current objTy member false
        |>.mapError (s!"{pos}: {label}: " ++ ·)
      let srcTy ← typeOf env src
      unless sameType srcTy memberTy do
        throw s!"{pos}: {label}: member @{member} has type {valueTypeName memberTy}, \
written value %{src} has type {valueTypeName srcTy}"
    | .call pos dest target args =>
      let (structName, fnName) := LLZK.ASTAnalysis.parseCallTarget target
      let (paramTys, resultTy) ← calleeSignature table structName fnName
        |>.mapError (s!"{pos}: {label}: " ++ ·)
      unless paramTys.length == args.length do
        throw s!"{pos}: {label}: @{target} expects {paramTys.length} arguments, \
got {args.length}"
      for (arg, paramTy) in args.zip paramTys do
        let argTy ← typeOf env arg
        unless sameType argTy paramTy do
          throw s!"{pos}: {label}: argument %{arg} of @{target} has type \
{valueTypeName argTy}, expected {valueTypeName paramTy}"
      if let some d := dest then
        match resultTy with
        | some ty => env := env.insert d ty
        | none => throw s!"{pos}: {label}: @{target} returns no value"
    | .funcReturn pos value =>
      match value, fn.returnType with
      | none, _ => pure ()
      | some v, some ty =>
        let vTy ← typeOf env v
        unless sameType vTy ty do
          throw s!"{pos}: {label}: returns %{v} of type {valueTypeName vTy}, \
declared result type is {valueTypeName ty}"
      | some _, none => throw s!"{pos}: {label}: returns a value but declares no result"
  pure env

/-- Member index and declared type of `obj[@member]`, resolved in the struct type of `obj`
(dialect member indices are relative to the object's struct). -/
private def lookupMember (table : StructTable) (current : String)
    (types : HashMap String LLZK.Ty) (obj member : String) :
    Except String (Nat × LLZK.Ty) := do
  let objTy ← match types.get? obj with
    | some ty => pure ty
    | none => throw s!"undefined SSA variable: %{obj}"
  resolveMember table current objTy member true

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
    Except String (List (Dialect.MemberDecl n)) := do
  let names := decls.map (·.name)
  if names.eraseDups.length != names.length then
    throw s!"duplicate member names: {names}"
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
    (table : StructTable) (current : String) (types : HashMap String LLZK.Ty)
    (ssaMap : HashMap String Nat) (numMembers : Nat)
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
      result := result ++ [builder.structObject
        (.newStruct (← lookupSSA ssaMap dest))]
    | .readMember _ dest self member =>
      result := result ++ [builder.structObject
        (.readMember (← lookupSSA ssaMap dest) (← lookupSSA ssaMap self)
          (← lookupMember table current types self member).1)]
    | .writeMember _ self member src =>
      -- A struct-typed member stores a sub-component (`writeObject` copies its subtree);
      -- a felt member stores a value.
      let (index, memberTy) ← lookupMember table current types self member
      let selfVar ← lookupSSA ssaMap self
      let srcVar ← lookupSSA ssaMap src
      result := result ++ [builder.structObject (match memberTy with
        | .structTy _ => .writeObject selfVar index srcVar
        | _ => .writeMember selfVar index srcVar)]
    | .nondet _ dest =>
      result := result ++ [builder.oracle (F := F)
        (.next (← lookupSSA ssaMap dest))]
  pure (result, returnVar)

def lowerConstrainBody {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [IntCast F]
    (n i : Nat) (structIndex : HashMap String Nat)
    (table : StructTable) (current : String) (types : HashMap String LLZK.Ty)
    (ssaMap : HashMap String Nat) (numMembers : Nat)
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
      result := result ++ [builder.structObject
        (.readMember (← lookupSSA ssaMap dest) (← lookupSSA ssaMap self)
          (← lookupMember table current types self member).1)]
    | .structNew _ _ _ | .writeMember _ _ _ _ =>
      throw "struct allocation and writes are not valid in constrain body"
    | .nondet _ _ =>
      throw "llzk.nondet is not valid in constrain body"
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

/-- Public-input flags of a struct: `{llzk.pub}` on each `@compute` parameter. The same
inputs are the trailing `@constrain` parameters (after the reserved prefix, such as `%self`),
and both functions must mark them identically. Reserved-prefix parameters cannot be public.
A struct without `@compute` takes its single implicit input from its last `@constrain`
parameter. -/
def inputPublicity (sd : LLZK.StructDef) (compute? : Option LLZK.FuncDef)
    (constrain : LLZK.FuncDef) : Except String (List Bool) := do
  let computeFlags := match compute? with
    | some fn => fn.params.map (·.isPublic)
    | none => [constrain.params.getLast?.map (·.isPublic) |>.getD false]
  let constrainFlags := constrain.params.map (·.isPublic)
  if constrainFlags.length < computeFlags.length then
    -- The layout certificate rejects this later with a precise message.
    return computeFlags
  let offset := constrainFlags.length - computeFlags.length
  if (constrainFlags.take offset).any id then
    throw s!"struct @{sd.name}: @constrain parameters before the inputs (such as %self) \
cannot be {"{"}llzk.pub}"
  unless constrainFlags.drop offset == computeFlags do
    throw s!"struct @{sd.name}: {"{"}llzk.pub} on @compute parameters {computeFlags} differs \
from the matching @constrain parameters {constrainFlags.drop offset}"
  pure computeFlags

def lowerStruct {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F]
    (n i : Nat) (hi : i < n) (structIndex : HashMap String Nat) (table : StructTable)
    (sd : LLZK.StructDef) :
    Except String (Dialect.StructDef Δ n ⟨i, hi⟩ F) := do
  let members ← lowerMembers n structIndex sd.members
  for fn in sd.funcs do
    unless fn.name == "compute" || fn.name == "constrain" do
      throw s!"struct @{sd.name}: unsupported function @{fn.name}; only @compute and \
@constrain are supported"
    if (sd.funcs.filter (·.name == fn.name)).length > 1 then
      throw s!"struct @{sd.name}: duplicate function @{fn.name}"
  let computeAst := sd.funcs.find? (fun f => f.name == "compute")
  -- A missing @constrain would silently yield an unconstrained circuit. A missing
  -- @compute is allowed: constraint-only structs simply have no witness program.
  let constrainFn ← match sd.funcs.find? (fun f => f.name == "constrain") with
    | some fn => pure fn
    | none => throw s!"struct {sd.name} has no @constrain function"
  let inputIsPublic ← inputPublicity sd computeAst constrainFn
  -- The witness of a struct is the object its @compute returns; a struct with members must
  -- return its own type, as in upstream LLZK, or the member values would be unobservable.
  if let some fn := computeAst then
    unless sd.members.isEmpty do
      unless (match fn.returnType with | some (.structTy t) => t == sd.name | _ => false) do
        throw s!"struct @{sd.name}: @compute must return !struct.type<@{sd.name}> because the \
struct has members"
  let computeNumParams := computeAst.map (·.params.length) |>.getD 1
  let constrainNumParams := constrainFn.params.length
  let computeRaw : List (Dialect.Stmt Δ ⟨n, i, members.length⟩ F) ×
      Option LocalVar ← match computeAst with
    | none => pure ([], none)
    | some fn =>
      let types ← checkFunc table sd.name "compute" fn
      lowerComputeBody (F := F) builder n i structIndex table sd.name types
        (← LLZK.ASTAnalysis.buildSSAMap fn.params fn.body) members.length fn.body
  let constrainTypes ← checkFunc table sd.name "constrain" constrainFn
  let constrainRaw : List (Dialect.Stmt Δ ⟨n, i, members.length⟩ F) ←
    lowerConstrainBody builder n i structIndex table sd.name constrainTypes
      (← LLZK.ASTAnalysis.buildSSAMap constrainFn.params constrainFn.body) members.length
      constrainFn.body
  let compute ← certifyFunc (kind := .witness) s!"{sd.name}::compute"
    computeNumParams computeRaw.1 computeRaw.2
  let constrain ← certifyFunc (kind := .constraint) s!"{sd.name}::constrain"
    constrainNumParams constrainRaw none
  pure {
    name := sd.name
    members := members
    compute := compute
    constrain := constrain
    inputIsPublic := inputIsPublic
  }

private def lowerStructsRec {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F]
    (n : Nat) (sorted : List LLZK.StructDef)
    (structIndex : HashMap String Nat) (table : StructTable) (k : Nat) (hk : k ≤ n) :
    Except String
      (∀ j : Fin n, j.val < k → Dialect.StructDef Δ n j F) := do
  match k with
  | 0 => pure fun _ h => absurd h (Nat.not_lt_zero _)
  | k' + 1 =>
    let previous ← lowerStructsRec builder n sorted structIndex table k'
      (Nat.le_of_succ_le hk)
    let hk' : k' < n := hk
    match sorted[k']? with
    | none => throw s!"internal: sorted[{k'}] missing (length={sorted.length})"
    | some ast =>
      let current ← lowerStruct builder n k' hk' structIndex table ast
      pure fun j hj =>
        if hjk : j.val < k' then previous j hjk
        else
          have hval : j.val = k' := by omega
          have heq : j = ⟨k', hk'⟩ := Fin.ext hval
          heq ▸ current

private def buildStructsFn {Δ : DialectSet} (builder : Builder Δ)
    {F : Type} [Field F] [IntCast F]
    (n : Nat) (sorted : List LLZK.StructDef)
    (structIndex : HashMap String Nat) (table : StructTable) :
    Except String ((j : Fin n) → Dialect.StructDef Δ n j F) := do
  let lowered ← lowerStructsRec builder n sorted structIndex table n le_rfl
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
    let table : StructTable := sorted.foldl (fun t sd => t.insert sd.name sd) ∅
    let structs ← buildStructsFn builder n sorted structIndex table
    let result : Dialect.Module Δ n F := { structs := structs }
    have hshape : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    pure ⟨n - 1, hshape ▸ result⟩

/-- Primary object-aware AST boundary. -/
def lower {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module SourceSet (k + 1) F) :=
  lowerWith fullBuilder m

/-- Full typed frontend boundary used by the primary pipeline. -/
def lowerFull {F : Type} [Field F] [IntCast F] (m : LLZK.Module) :
    Except String (Σ k, Dialect.Module WitnessSourceSet (k + 1) F) :=
  lowerWith witnessBuilder m

end LLZK.DialectLowering
