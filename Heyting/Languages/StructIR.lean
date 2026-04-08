import Mathlib.Algebra.Field.Basic

import Heyting.Core.Language

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

abbrev LocalVar := Nat

/-! ## Core types -/

-- Member types: felt or a reference to struct `j` (which must exist in module)
inductive MemberType (n : Nat) where
  | felt : MemberType n
  | substruct : Fin n → MemberType n
  deriving Repr

-- A struct member declaration
structure MemberDecl (n : Nat) where
  name : String
  type : MemberType n
  deriving Repr

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
  | feltConst (dest : LocalVar) (c : F)
  | readMember (dest : LocalVar) (self : LocalVar) (member : Fin numMembers)
  | constrainEq (src1 src2 : LocalVar)
  | call (target : Fin i) (args : List LocalVar)
  deriving Repr

-- Statements in @compute (witness-generating function)
inductive ComputeStmt (n : Nat) (i : Fin n) (F : Type) (numMembers : Nat)
    where
  | feltAdd (dest : LocalVar) (src1 src2 : LocalVar)
  | feltSub (dest : LocalVar) (src1 src2 : LocalVar)
  | feltMul (dest : LocalVar) (src1 src2 : LocalVar)
  | feltDiv (dest : LocalVar) (src1 src2 : LocalVar)
  | feltNeg (dest : LocalVar) (src : LocalVar)
  | feltConst (dest : LocalVar) (c : F)
  | readMember (dest : LocalVar) (self : LocalVar) (member : Fin numMembers)
  | writeMember (self : LocalVar) (member : Fin numMembers) (src : LocalVar)
  | newStruct (dest : LocalVar)
  | call (dest : LocalVar) (target : Fin i) (args : List LocalVar)
  deriving Repr

-- @constrain function: parameter count + body
structure ConstrainFunc (n : Nat) (i : Fin n) (F : Type) (numMembers : Nat)
    where
  numParams : Nat   -- first param (0) is always %self
  body : List (ConstrainStmt n i F numMembers)
  deriving Repr

-- @compute function: parameter count + body + return variable
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

structure StructDef (n : Nat) (i : Fin n) (F : Type) where
  name : String
  members : List (MemberDecl n)
  compute : ComputeFunc n i F members.length
  constrain : ConstrainFunc n i F members.length
  deriving Repr

/-! ## Paths, environments, and module structure -/

-- Instance path: sequence of member indices tracing through the struct hierarchy
abbrev InstancePath := List Nat

-- Variable identifier for the Language typeclass
abbrev VarId := InstancePath × Nat  -- (path, member index)

-- Object environment: tracks which instance path is bound to each local var
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

-- Collect (path, memberIdx) pairs read during constrain body traversal.
-- Takes `structs` directly (not `Module`) so it can be used in the `Module` definition.
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

/-!
### Module

A `Module` is a length-indexed vector of struct definitions.
We use a dependent function `Fin n → StructDef n i F` to represent it.

The main struct is always the last one (index `n-1`), which is the root
of the dependency DAG.

**WARNING — NoDuplicateReads**: The `noDupReads` field requires that each
`(path, member)` pair is read at most once across the entire constrain
evaluation tree. This holds for SSA-form programs (e.g., LLZK output) but
is not checked dynamically. Programs violating this condition cannot be
represented as a `Module`.
-/

-- The module: n structs, each at its own index, main is the last.
-- Carries a well-formedness proof that no (path, member) is read twice.
structure Module (n : Nat) (F : Type) where
  structs : (i : Fin n) → StructDef n i F
  noDupReads : ∀ (hn : 0 < n),
    let mainIdx : Fin n := ⟨n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
    let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
    (readPositions structs mainIdx initObjEnv
      (structs mainIdx).constrain.body).Nodup

-- The main struct is the last one (highest index = root of DAG)
def Module.main {n : Nat} (m : Module (n + 1) F) :
    StructDef (n + 1) ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩ F :=
  m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩

/-! ## Witness and Semantics -/

-- The witness maps (path, memberIdx) → field value
abbrev Witness (F : Type) := VarId → F

-- Local variable environment within a function evaluation
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

-- Top-level: evaluate @Main::@constrain (main = last struct)
def satisfies (w : Witness F) {n : Nat} (m : Module (n + 1) F) : Prop :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef := m.structs mainIdx
  let env : LocalEnv F := fun _ => 0
  let objEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
  evalConstrainBody m w mainIdx env objEnv mainDef.constrain.body

instance Language (n : Nat) (F : Type) [Field F] :
    Language VarId F where
  Program := Module (n + 1) F
  satisfies := fun w m => satisfies w m

end StructIR
