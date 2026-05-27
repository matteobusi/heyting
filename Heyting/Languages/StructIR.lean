/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Language
import Heyting.Core.ComputingLanguage
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

/-!
# StructIR — Structured Intermediate Representation

A higher-level IR capturing LLZK's `struct`, `function`, and `felt` dialects.

## Design: Intrinsic well-formedness

Structs are indexed `0..n-1` in topological (dependency) order: leaves first,
main last. A struct at index `i` can only call structs at indices `j < i`,
enforced by the type `Fin i` in call statements. This makes:
- Cyclic calls unrepresentable
- Missing struct references unrepresentable
- Termination of semantic evaluation automatic (structural recursion on index)

Members within a struct are indexed by `Fin`, so missing member references are
also unrepresentable.
-/

namespace StructIR

/-- Local variables in StructIR bodies are numbered by natural numbers. -/
abbrev LocalVar := Nat

/-! ## Core types -/

/-- Type of a struct member: either a field element or a nested sub-struct. -/
inductive MemberType (n : Nat) where
  | felt : MemberType n
  | substruct : Fin n → MemberType n
  deriving Repr

/-- Declaration of a single struct member. -/
structure MemberDecl (n : Nat) where
  name     : String
  type     : MemberType n
  isPublic : Bool     -- true iff `{llzk.pub}` was present on this member
  deriving Repr

/-! ## Statement syntax -/

/--
Statements in `@constrain` bodies.

The index parameter `i` enforces that calls may only target structs `j < i`.
-/
-- Statements in @constrain (constraint-generating function)
-- Parameterized by `i`: the index of the struct this function belongs to.
-- Calls can only target structs `j < i`.
inductive ConstrainStmt (n : Nat) (i : Fin n) (F : Type) (numMembers : Nat)
    where
  | feltAdd (dest : LocalVar) (src1 src2 : LocalVar)
  | feltSub (dest : LocalVar) (src1 src2 : LocalVar)
  | feltMul (dest : LocalVar) (src1 src2 : LocalVar)
  | feltDiv (dest : LocalVar) (src1 src2 : LocalVar)
  | feltNeg (dest : LocalVar) (src : LocalVar)
  /-- Field inverse: `dest = src⁻¹` with `inv(0) = 0`. -/
  | feltInv (dest : LocalVar) (src : LocalVar)
  | feltConst (dest : LocalVar) (c : F)
  | readMember (dest : LocalVar) (self : LocalVar) (member : Fin numMembers)
  | constrainEq (src1 src2 : LocalVar)
  | call (target : Fin i) (args : List LocalVar)
  deriving Repr

/-- Destination variable written by a constrain statement, if any. -/
def ConstrainStmt.dest {n i F numMembers} : ConstrainStmt n i F numMembers → Option LocalVar
  | .feltAdd d _ _ => some d
  | .feltSub d _ _ => some d
  | .feltMul d _ _ => some d
  | .feltDiv d _ _ => some d
  | .feltNeg d _ => some d
  | .feltInv d _ => some d
  | .feltConst d _ => some d
  | .readMember d _ _ => some d
  | .constrainEq _ _ => none
  | .call _ _ => none

/-- Variables read by a constrain statement. -/
def ConstrainStmt.reads {n i F numMembers} : ConstrainStmt n i F numMembers → List LocalVar
  | .feltAdd _ s1 s2 => [s1, s2]
  | .feltSub _ s1 s2 => [s1, s2]
  | .feltMul _ s1 s2 => [s1, s2]
  | .feltDiv _ s1 s2 => [s1, s2]
  | .feltNeg _ s => [s]
  | .feltInv _ s => [s]
  | .feltConst _ _ => []
  | .readMember _ self _ => [self]
  | .constrainEq s1 s2 => [s1, s2]
  | .call _ args => args

/--
SSA checker for constrain bodies, parameterized by the set of initially-defined
locals.
-/
def isSSA {n i F numMembers} :
    (LocalVar → Bool) → List (ConstrainStmt n i F numMembers) → Bool
  | _, [] => true
  | init, s :: sl =>
    s.reads.all init &&
    match s.dest with
    | some d => !init d && isSSA (fun x => init x || x == d) sl
    | none => isSSA init sl

/-- Statements in `@compute` bodies. -/
inductive ComputeStmt (n : Nat) (i : Fin n) (F : Type) (numMembers : Nat)
    where
  | feltAdd (dest : LocalVar) (src1 src2 : LocalVar)
  | feltSub (dest : LocalVar) (src1 src2 : LocalVar)
  | feltMul (dest : LocalVar) (src1 src2 : LocalVar)
  | feltDiv (dest : LocalVar) (src1 src2 : LocalVar)
  | feltNeg (dest : LocalVar) (src : LocalVar)
  /-- Field inverse: `dest = src⁻¹` with `inv(0) = 0`. -/
  | feltInv (dest : LocalVar) (src : LocalVar)
  | feltConst (dest : LocalVar) (c : F)
  | readMember (dest : LocalVar) (self : LocalVar) (member : Fin numMembers)
  | writeMember (self : LocalVar) (member : Fin numMembers) (src : LocalVar)
  | newStruct (dest : LocalVar)
  | call (dest : LocalVar) (target : Fin i) (args : List LocalVar)
  deriving Repr

/-- A `@constrain` function body for a struct. -/
structure ConstrainFunc (n : Nat) (i : Fin n) (F : Type) (numMembers : Nat)
    where
  numParams : Nat   -- first param (0) is always %self
  body : List (ConstrainStmt n i F numMembers)
  deriving Repr

/-- A `@compute` function body together with its return local. -/
structure ComputeFunc (n : Nat) (i : Fin n) (F : Type) (numMembers : Nat)
    where
  numParams : Nat
  body : List (ComputeStmt n i F numMembers)
  returnVar : LocalVar
  deriving Repr

/-! ## Struct and Module definitions

A `StructDef` at index `i` in a module of `n` structs knows its own index.
Its statements can only reference structs `j < i`.
-/

/-- Definition of a StructIR struct: members plus compute/constrain bodies. -/
structure StructDef (n : Nat) (i : Fin n) (F : Type) where
  name : String
  members : List (MemberDecl n)
  compute : ComputeFunc n i F members.length
  constrain : ConstrainFunc n i F members.length
  deriving Repr

/-- Remove all occurrences of local variable `v` from a list. -/
def dropVar (v : LocalVar) (vars : List LocalVar) : List LocalVar :=
  vars.filter fun x => x != v

/-- Pick call-site locals that correspond to the given callee parameter indices. -/
def collectNeededArgs (args neededParams : List LocalVar) : List LocalVar :=
  neededParams.filterMap fun p => args[p]?

/-- Check that all callee parameters in `neededParams` are supplied by `args`. -/
def neededArgsAvailable (args neededParams : List LocalVar) : Bool :=
  neededParams.all fun p => (args[p]?).isSome

/--
Backward object-channel safety analysis.

Returns `(safe, needs)` where:
- `safe = true` means no object-path use flows through a value-only write, and
  every object-needed callee parameter is supplied by call site.
- `needs` lists locals whose `objEnv` must already be meaningful on entry.
-/
def objectInfo {F : Type} (structs : (i : Fin n) → StructDef n i F)
    (i : Fin n) (stmts : List (ConstrainStmt n i F (structs i).members.length)) :
    Bool × List LocalVar :=
  match stmts with
  | [] => (true, [])
  | stmt :: rest =>
    let restInfo := objectInfo structs i rest
    let safeRest := restInfo.1
    let needsRest := restInfo.2
    match stmt with
    | .feltAdd dest _ _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .feltSub dest _ _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .feltMul dest _ _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .feltDiv dest _ _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .feltNeg dest _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .feltInv dest _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .feltConst dest _ =>
      (safeRest && !(needsRest.contains dest), dropVar dest needsRest)
    | .readMember dest self _ =>
      (safeRest, self :: dropVar dest needsRest)
    | .constrainEq _ _ =>
      (safeRest, needsRest)
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeInfo := objectInfo structs j (structs j).constrain.body
      let safeCallee := calleeInfo.1
      let calleeNeeds := calleeInfo.2
      (safeRest && safeCallee && neededArgsAvailable args calleeNeeds,
        collectNeededArgs args calleeNeeds ++ needsRest)
termination_by (i, stmts.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Object-channel safety for constrain body with entry object-ready set `init`. -/
def objectSafe {F : Type} (structs : (i : Fin n) → StructDef n i F)
    (i : Fin n) (init : LocalVar → Bool)
    (stmts : List (ConstrainStmt n i F (structs i).members.length)) : Bool :=
  let info := objectInfo structs i stmts
  info.1 && info.2.all init

/-! ## Paths, environments, and module structure -/

/-- Instance path: sequence of member indices tracing through the struct hierarchy. -/
abbrev InstancePath := List Nat

/-- Variable identifier for the `Language` typeclass: a pair `(path, memberIndex)`. -/
abbrev VarId := InstancePath × Nat

/-- Object environment: maps each local variable to the instance path it refers to. -/
abbrev ObjEnv := LocalVar → InstancePath

def ObjEnv.update (env : ObjEnv) (v : LocalVar) (path : InstancePath) :
    ObjEnv :=
  fun w => if w == v then path else env w

/-!
### Read positions

`readPositions` collects all `(path, member)` pairs accessed by `readMember`
statements during a constrain body traversal. It mirrors the recursion
structure of `evalConstrainBody` / `compileConstrainBody`.

Used to define the `NoDuplicateReads` well-formedness condition on modules.
-/

/-- Collect all `(path, memberIdx)` pairs read during constrain body traversal.
Takes `structs` directly rather than a `Module` so this can be used inside the `Module`
definition. -/
def readPositions {F : Type} (structs : (i : Fin n) → StructDef n i F)
    (i : Fin n) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (structs i).members.length)) :
    List VarId :=
  match stmts with
  | [] => []
  | stmt :: rest =>
    match stmt with
    | .readMember dest self member =>
      let path := objEnv self
      [(path, member.val)] ++
        readPositions structs i (objEnv.update dest (path ++ [member.val])) rest
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      readPositions structs j calleeObjEnv (structs j).constrain.body ++
        readPositions structs i objEnv rest
    | _ => readPositions structs i objEnv rest
  termination_by (i, stmts.length)
  decreasing_by
    all_goals first
    | apply Prod.Lex.left; exact target.isLt
    | apply Prod.Lex.right; simp

/-!
### Module

A `Module` is a length-indexed vector of struct definitions.
We use a dependent function `Fin n → StructDef n i F` to represent it.

The main struct is always the last one (index `n-1`), which is the root
of the dependency DAG.

**WARNING — NoDuplicateReads**: The `noDupReads` field requires that each
`(path, member)` pair is read at most once across the entire constrain
evaluation tree. Programs violating this condition cannot be
represented as a `Module`.
-/

/-- A length-`n` vector of struct definitions, with the main struct at index `n-1`.
Carries well-formedness proofs: no `(path, member)` is read twice (`noDupReads`),
all constrain bodies are SSA (`all_ssa`), and all object-channel uses are safe (`all_objSafe`). -/
structure Module (n : Nat) (F : Type) where
  structs : (i : Fin n) → StructDef n i F
  noDupReads : ∀ (hn : 0 < n),
    let mainIdx : Fin n := ⟨n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
    let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
    (readPositions structs mainIdx initObjEnv
      (structs mainIdx).constrain.body).Nodup
  all_ssa : ∀ (i : Fin n),
    isSSA (fun v => v < (structs i).constrain.numParams)
      (structs i).constrain.body = true
  all_objSafe : ∀ (i : Fin n),
    objectSafe structs i
      (fun v => v < (structs i).constrain.numParams)
      (structs i).constrain.body = true

/-- The main struct: highest-index struct (root of the dependency DAG). -/
def Module.main {n : Nat} (m : Module (n + 1) F) :
    StructDef (n + 1) ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩ F :=
  m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩

/-! ## Witness and Semantics -/

/-- A witness maps every `(path, memberIdx)` coordinate to a field element. -/
abbrev Witness (F : Type) := VarId → F

/-- Local variable environment: maps each local variable index to its current value. -/
abbrev LocalEnv (F : Type) := LocalVar → F

def LocalEnv.update (env : LocalEnv F) (v : LocalVar) (val : F) :
    LocalEnv F :=
  fun w => if w == v then val else env w

/-!
## Constraint Evaluation

Evaluation recurses on struct index — when struct `i` calls struct `j < i`,
the recursive call is structurally smaller. No fuel needed.
-/

variable {F : Type} [Field F] {n : Nat}

-- Forward declaration: evaluate @constrain for struct at index `i`
-- Given the module, witness, local env, object env, and the statement list

-- Evaluate a constrain body for struct `i`, producing the conjunction of
-- all constraints
def evalConstrainBody (m : Module n F) (w : Witness F)
    (i : Fin n) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    Prop :=
  match stmts with
  | [] => True
  | stmt :: rest =>
    let (env', objEnv', prop) := match stmt with
      | .feltAdd dest src1 src2 =>
        (env.update dest (env src1 + env src2), objEnv, True)
      | .feltSub dest src1 src2 =>
        (env.update dest (env src1 - env src2), objEnv, True)
      | .feltMul dest src1 src2 =>
        (env.update dest (env src1 * env src2), objEnv, True)
      | .feltDiv dest src1 src2 =>
        (env.update dest (env src1 * (env src2)⁻¹), objEnv, env src2 ≠ 0)
      | .feltNeg dest src =>
        (env.update dest (-(env src)), objEnv, True)
      | .feltInv dest src =>
        (env.update dest ((env src)⁻¹), objEnv, True)
      | .feltConst dest c =>
        (env.update dest c, objEnv, True)
      | .readMember dest self member =>
        let path := objEnv self
        (env.update dest (w (path, member.val)),
         objEnv.update dest (path ++ [member.val]), True)
      | .constrainEq src1 src2 =>
        (env, objEnv, env src1 = env src2)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let sd := m.structs j
        -- Build callee environments from args (param 0 = arg 0, etc.)
        let calleeEnv : LocalEnv F := fun param =>
          match args[param]? with
          | some arg => env arg
          | none => 0
        let calleeObjEnv : ObjEnv := fun param =>
          match args[param]? with
          | some arg => objEnv arg
          | none => []
        let callProp := evalConstrainBody m w j
          calleeEnv calleeObjEnv sd.constrain.body
        (env, objEnv, callProp)
    prop ∧ evalConstrainBody m w i env' objEnv' rest
termination_by (i, stmts.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Canonical witness coordinate for the `p`-th constrain parameter of a main
    struct with `numMembers` members.

    Members live at `([], m)` for `m < numMembers`. Sub-structs live at deeper
    paths `(m :: ...)`. Params live at single-segment paths
    `([numMembers + p], 0)`, which cannot collide with any member coord
    (different path length / different head index) and cannot be read by any
    `readMember` (which always produces coords of the form `(path, m)` with
    `m < numMembers'` for the corresponding sub-struct's member count). -/
def paramCoord (numMembers p : Nat) : VarId :=
  ([numMembers + p], 0)

/-- Top-level satisfaction predicate for `@Main::@constrain`.

The initial environment seeds params `p < numParams` to `w (paramCoord numMembers p)` and
non-param locals to `0`. The initial object env binds `%self` (local `0`) to the root path `[]`. -/
def satisfies (w : Witness F) {n : Nat} (m : Module (n + 1) F) : Prop :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef := m.structs mainIdx
  let numParams := mainDef.constrain.numParams
  let numMembers := mainDef.members.length
  let env : LocalEnv F := fun k =>
    if k < numParams then w (paramCoord numMembers k) else 0
  let objEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
  evalConstrainBody m w mainIdx env objEnv mainDef.constrain.body

instance Language (n : Nat) (F : Type) [Field F] :
    Language VarId F where
  Program := Module (n + 1) F
  satisfies := fun w m => satisfies w m

/-!
## Compute Interpreter

`evalComputeBody` interprets a `ComputeFunc` body to produce a witness.
It mirrors the structure of `evalConstrainBody` and uses the same
termination measure `(i, stmts.length)`.

### Interpreter state

- `env`      — values of local variables (updated by felt ops and calls)
- `objEnv`   — instance paths for local variables (updated by `readMember`, `newStruct`, `call`)
- `acc`      — witness accumulator: maps `VarId` to field values (updated by `writeMember`)
- `nextPath` — monotonic counter for allocating fresh `InstancePath`s via `newStruct`

### Error handling

`feltDiv` returns `none` if the divisor is zero. All other errors
propagate via `Option.bind` (`do`-notation). The top-level
`computeWitness` returns `none` iff any division by zero occurred.
-/

/-- Interpreter state for `evalComputeBody`. -/
structure ComputeState (F : Type) where
  /-- Local variable values. -/
  env      : LocalEnv F
  /-- Instance paths bound to local variables. -/
  objEnv   : ObjEnv
  /-- Witness accumulator: `(path, memberIdx) → F`. -/
  acc      : Witness F
  /-- Counter for allocating fresh instance paths via `newStruct`. -/
  nextPath : Nat

variable {F : Type} [Field F] [DecidableEq F] {n : Nat}

/-- Evaluate a `@compute` body for struct `i`, threading `ComputeState`.
    Returns `none` if division by zero occurs. -/
def evalComputeBody (m : Module n F)
    (i : Fin n) (state : ComputeState F)
    (stmts : List (ComputeStmt n i F (m.structs i).members.length)) :
    Option (ComputeState F) :=
  match stmts with
  | [] => some state
  | stmt :: rest =>
    let step : Option (ComputeState F) :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        some { state with env := state.env.update dest (state.env src1 + state.env src2) }
      | .feltSub dest src1 src2 =>
        some { state with env := state.env.update dest (state.env src1 - state.env src2) }
      | .feltMul dest src1 src2 =>
        some { state with env := state.env.update dest (state.env src1 * state.env src2) }
      | .feltDiv dest src1 src2 =>
        if state.env src2 == 0 then none
        else
          some { state with env := state.env.update dest (state.env src1 * (state.env src2)⁻¹) }
      | .feltNeg dest src =>
        some { state with env := state.env.update dest (-(state.env src)) }
      | .feltInv dest src =>
        some { state with env := state.env.update dest ((state.env src)⁻¹) }
      | .feltConst dest c =>
        some { state with env := state.env.update dest c }
      | .readMember dest self member =>
        -- Read a member value from the witness accumulator.
        -- The member's path is (objEnv[self] ++ [member.val]).
        let selfPath := state.objEnv self
        let memberPath := selfPath ++ [member.val]
        let val := state.acc (selfPath, member.val)
        some { state with
          env    := state.env.update dest val,
          objEnv := state.objEnv.update dest memberPath }
      | .writeMember self member src =>
        -- Write a local variable's value into the witness accumulator.
        let path := state.objEnv self
        let vid  := (path, member.val)
        let val  := state.env src
        some { state with acc := fun v => if v == vid then val else state.acc v }
      | .newStruct dest =>
        -- Allocate an instance path for the new struct.
        -- nextPath=0 → root path [], nextPath=k>0 → path [k].
        -- This ensures the first (root) struct in @compute gets path [],
        -- matching the path used for %self in @constrain (initObjEnv[0] = []).
        let path := if state.nextPath == 0 then [] else [state.nextPath]
        some { state with
          objEnv   := state.objEnv.update dest path,
          nextPath := state.nextPath + 1 }
      | .call dest target args =>
        -- Evaluate the callee's compute body with a fresh local env built from args.
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let sd := m.structs j
        let calleeEnv : LocalEnv F := fun param =>
          match args[param]? with
          | some arg => state.env arg
          | none => 0
        let calleeObjEnv : ObjEnv := fun param =>
          match args[param]? with
          | some arg => state.objEnv arg
          | none => []
        let calleeState : ComputeState F :=
          { env := calleeEnv, objEnv := calleeObjEnv,
            acc := state.acc, nextPath := state.nextPath }
        match evalComputeBody m j calleeState sd.compute.body with
        | none => none
        | some s' =>
          -- The callee's return value goes into dest; witness and nextPath are merged back.
          some { state with
            env      := state.env.update dest (s'.env sd.compute.returnVar),
            acc      := s'.acc,
            nextPath := s'.nextPath }
    match step with
    | none => none
    | some state' => evalComputeBody m i state' rest
termination_by (i, stmts.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Build the initial `ComputeState` from a list of public inputs.
    Inputs are placed into local variables `0 .. inputs.length - 1`.
    The witness accumulator is pre-seeded at the canonical param-witness
    coordinates `paramCoord numMembers (paramOffset + k)` so that
    `StructIR.satisfies` reads each constrain-param `paramOffset + k` from
    that exact slot. All other locals and witness positions default to `0`. -/
def initComputeState (numMembers : Nat) (inputs : List F) (paramOffset : Nat) :
    ComputeState F :=
  let env : LocalEnv F := fun k =>
    match inputs[k]? with
    | some v => v
    | none   => 0
  -- Param-canonical-coords (paths of the form `[numMembers + p]`) get seeded
  -- from inputs. Member coords (path `[]`) and sub-struct coords are
  -- written by `evalComputeBody` directly.
  let acc : Witness F := fun vid =>
    match vid with
    | ([p], 0) =>
      if p ≥ numMembers + paramOffset then
        match inputs[p - (numMembers + paramOffset)]? with
        | some v => v
        | none   => 0
      else 0
    | _ => 0
  { env      := env,
    objEnv   := ObjEnv.update (fun _ => []) 0 [],
    acc      := acc,
    nextPath := 0 }  -- nextPath=0 → first newStruct gets root path []

/-- Attempt to compute a satisfying witness for the main struct from public inputs.
    Returns `none` if any `feltDiv` encounters a zero divisor. -/
def computeWitness (m : Module (n + 1) F) (inputs : List F) : Option (Witness F) :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  -- The offset between @constrain param indices and @compute param indices.
  -- @constrain has %self as param 0; @compute does not.  So if @constrain has
  -- 3 params (self, a, b) and @compute has 2 (a, b), the offset is 1.
  let cNumParams := m.main.constrain.numParams
  let pNumParams := m.main.compute.numParams
  let offset := cNumParams - pNumParams
  let numMembers := m.main.members.length
  let state₀ := initComputeState numMembers inputs offset
  match evalComputeBody m mainIdx state₀ m.main.compute.body with
  | none    => none
  | some s' => some s'.acc

/-- `ComputingLanguage` instance for StructIR.
    Public inputs are given as `List F` (positional arguments to `@compute`). -/
instance ComputingLang (n : Nat) (F : Type) [Field F] [DecidableEq F] :
    ComputingLanguage VarId F where
  Program         := Module (n + 1) F
  satisfies       := fun w m => satisfies w m
  Input           := List F
  computeWitness  := fun m inputs => computeWitness m inputs

end StructIR
