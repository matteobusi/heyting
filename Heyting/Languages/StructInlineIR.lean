/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Core.Language
import Heyting.Languages.StructIR

namespace StructInlineIR

abbrev LocalVar := Nat
abbrev InstancePath := StructIR.InstancePath
abbrev VarId := StructIR.VarId
abbrev ObjEnv := StructIR.ObjEnv

inductive ConstrainStmt (n : Nat) (F : Type) where
  | feltAdd (dest : LocalVar) (src1 src2 : LocalVar)
  | feltSub (dest : LocalVar) (src1 src2 : LocalVar)
  | feltMul (dest : LocalVar) (src1 src2 : LocalVar)
  | feltDiv (dest : LocalVar) (src1 src2 : LocalVar)
  | feltNeg (dest : LocalVar) (src : LocalVar)
  | feltConst (dest : LocalVar) (c : F)
  | readMember (dest : LocalVar) (self : LocalVar) (member : Nat)
  | constrainEq (src1 src2 : LocalVar)
  deriving Repr

structure ConstrainFunc (n : Nat) (F : Type) where
  numParams : Nat
  body : List (ConstrainStmt n F)
  deriving Repr

structure StructDef (n : Nat) (F : Type) where
  name : String
  members : List (StructIR.MemberDecl n)
  constrain : ConstrainFunc n F
  deriving Repr

def readPositions {F : Type} (structs : (i : Fin n) -> StructDef n F)
    (i : Fin n) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n F)) :
    List VarId :=
  match stmts with
  | [] => []
  | stmt :: rest =>
    match stmt with
    | .readMember dest self member =>
      let path := objEnv self
      [(path, member)] ++
        readPositions structs i (StructIR.ObjEnv.update objEnv dest (path ++ [member])) rest
    | _ => readPositions structs i objEnv rest

def constrainDests {n : Nat} {F : Type}
    (stmts : List (ConstrainStmt n F)) : List LocalVar :=
  stmts.filterMap fun stmt =>
    match stmt with
    | .feltAdd dest _ _ | .feltSub dest _ _ | .feltMul dest _ _
    | .feltDiv dest _ _ | .feltNeg dest _ | .feltConst dest _
    | .readMember dest _ _ => some dest
    | .constrainEq _ _ => none

def constrainStmtSources {n : Nat} {F : Type}
    (stmt : ConstrainStmt n F) : List LocalVar :=
  match stmt with
  | .feltAdd _ src1 src2 | .feltSub _ src1 src2
  | .feltMul _ src1 src2 | .feltDiv _ src1 src2 => [src1, src2]
  | .feltNeg _ src => [src]
  | .feltConst _ _ => []
  | .readMember _ self _ => [self]
  | .constrainEq src1 src2 => [src1, src2]

def constrainStmtDest {n : Nat} {F : Type}
    (stmt : ConstrainStmt n F) : Option LocalVar :=
  match stmt with
  | .feltAdd dest _ _ | .feltSub dest _ _ | .feltMul dest _ _
  | .feltDiv dest _ _ | .feltNeg dest _ | .feltConst dest _
  | .readMember dest _ _ => some dest
  | .constrainEq _ _ => none

def checkDefBeforeUse {n : Nat} {F : Type}
    (numParams : Nat) (defined : List LocalVar)
    (stmts : List (ConstrainStmt n F)) : Bool :=
  match stmts with
  | [] => true
  | stmt :: rest =>
    let sources := constrainStmtSources stmt
    let allDefined := sources.all fun s => s < numParams || defined.contains s
    let destOk := match constrainStmtDest stmt with
      | some d => !sources.contains d && numParams <= d
      | none => true
    let newDefined := match constrainStmtDest stmt with
      | some d => d :: defined
      | none => defined
    allDefined && destOk && checkDefBeforeUse numParams newDefined rest

abbrev Witness (F : Type) := VarId -> F
abbrev LocalEnv (F : Type) := LocalVar -> F

/-- A `StructInlineIR` module carries the per-struct definitions plus
    well-formedness proofs needed by downstream passes:
    - `noDupReads`: no `(path, member)` pair is read twice in the main body.
    - `isSSA`: in each struct's constrain body, no local variable is written
      twice (SSA form). -/
structure Module (n : Nat) (F : Type) where
  structs : (i : Fin n) → StructDef n F
  noDupReads : ∀ (hn : 0 < n),
    let mainIdx : Fin n := ⟨n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
    let initObjEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) 0 []
    (readPositions structs mainIdx initObjEnv
      (structs mainIdx).constrain.body).Nodup
  isSSA : ∀ (i : Fin n),
    (constrainDests (structs i).constrain.body).Nodup

def LocalEnv.update (env : LocalEnv F) (v : LocalVar) (val : F) : LocalEnv F :=
  fun w => if w == v then val else env w

variable {F : Type} [Field F] {n : Nat}

def evalConstrainBody (m : Module n F) (w : Witness F)
    (i : Fin n) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n F)) : Prop :=
  match stmts with
  | [] => True
  | stmt :: rest =>
    let (env', objEnv', prop) :=
      match stmt with
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
        (env.update dest (w (path, member)),
         StructIR.ObjEnv.update objEnv dest (path ++ [member]), True)
      | .constrainEq src1 src2 =>
        (env, objEnv, env src1 = env src2)
    prop ∧ evalConstrainBody m w i env' objEnv' rest

def satisfies (w : Witness F) {n : Nat} (m : Module (n + 1) F) : Prop :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef := m.structs mainIdx
  let env : LocalEnv F := fun k => w ([], k)
  let objEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) 0 []
  evalConstrainBody m w mainIdx env objEnv mainDef.constrain.body

instance Language (n : Nat) (F : Type) [Field F] :
    Language StructIR.VarId F where
  Program := Module (n + 1) F
  satisfies := fun w m => satisfies w m

/-! ## Evaluation helpers -/

/-- `evalConstrainBody` does not depend on `m` or `i` (phantom params). -/
theorem evalConstrainBody_irrel (m1 m2 : Module n F)
    (w : Witness F) (i1 i2 : Fin n)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n F)) :
    evalConstrainBody m1 w i1 env objEnv stmts =
    evalConstrainBody m2 w i2 env objEnv stmts := by
  induction stmts generalizing env objEnv with
  | nil => simp [evalConstrainBody]
  | cons s rest ih =>
    simp only [evalConstrainBody]; cases s <;> simp_all

/-- State update from one StructInlineIR statement (no constraint). -/
def stepState (w : Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmt : ConstrainStmt n F) : LocalEnv F × ObjEnv :=
  match stmt with
  | .feltAdd dest src1 src2 =>
    (env.update dest (env src1 + env src2), objEnv)
  | .feltSub dest src1 src2 =>
    (env.update dest (env src1 - env src2), objEnv)
  | .feltMul dest src1 src2 =>
    (env.update dest (env src1 * env src2), objEnv)
  | .feltDiv dest src1 src2 =>
    (env.update dest (env src1 * (env src2)⁻¹), objEnv)
  | .feltNeg dest src =>
    (env.update dest (-(env src)), objEnv)
  | .feltConst dest c =>
    (env.update dest c, objEnv)
  | .readMember dest self member =>
    let path := objEnv self
    (env.update dest (w (path, member)),
     StructIR.ObjEnv.update objEnv dest (path ++ [member]))
  | .constrainEq _ _ => (env, objEnv)

/-- State after processing a list of stmts. -/
def runState (w : Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n F)) : LocalEnv F × ObjEnv :=
  match stmts with
  | [] => (env, objEnv)
  | s :: rest =>
    let (env', objEnv') := stepState w env objEnv s
    runState w env' objEnv' rest

/-- Splitting evaluation over concatenated stmts. -/
theorem evalConstrainBody_append (m : Module n F) (w : Witness F)
    (i : Fin n) (env : LocalEnv F) (objEnv : ObjEnv)
    (s1 s2 : List (ConstrainStmt n F)) :
    evalConstrainBody m w i env objEnv (s1 ++ s2) ↔
    evalConstrainBody m w i env objEnv s1 ∧
    evalConstrainBody m w i (runState w env objEnv s1).1
      (runState w env objEnv s1).2 s2 := by
  induction s1 generalizing env objEnv with
  | nil => simp [evalConstrainBody, runState]
  | cons s rest ih =>
    simp only [List.cons_append, evalConstrainBody, runState, stepState]
    cases s <;> simp_all [and_assoc]

/-- Splitting `runState` over concatenated stmts. -/
theorem runState_append (w : Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (s1 s2 : List (ConstrainStmt n F)) :
    runState w env objEnv (s1 ++ s2) =
      runState w (runState w env objEnv s1).1 (runState w env objEnv s1).2 s2 := by
  induction s1 generalizing env objEnv with
  | nil => simp [runState]
  | cons s rest ih =>
    simp only [List.cons_append, runState]
    exact ih _ _

/-- Object-env tracker for `readPositions`. Mirrors the `objEnv` component of
    `runState` but independently of any felt witness `w`. -/
def readObjEnv (objEnv : ObjEnv) (stmts : List (ConstrainStmt n F)) : ObjEnv :=
  match stmts with
  | [] => objEnv
  | stmt :: rest =>
    match stmt with
    | .readMember dest self member =>
      let path := objEnv self
      readObjEnv (StructIR.ObjEnv.update objEnv dest (path ++ [member])) rest
    | _ => readObjEnv objEnv rest

omit [Field F] in
theorem readObjEnv_append (objEnv : ObjEnv) (s1 s2 : List (ConstrainStmt n F)) :
    readObjEnv objEnv (s1 ++ s2) = readObjEnv (readObjEnv objEnv s1) s2 := by
  induction s1 generalizing objEnv with
  | nil => simp [readObjEnv]
  | cons s rest ih =>
    simp only [List.cons_append, readObjEnv]
    cases s <;> (dsimp only; exact ih _)

/-- `readObjEnv` matches the objEnv component of `runState` (they both only
    get updated by `readMember`, identically). -/
theorem readObjEnv_eq_runState (w : Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n F)) :
    readObjEnv objEnv stmts = (runState w env objEnv stmts).2 := by
  induction stmts generalizing env objEnv with
  | nil => simp [readObjEnv, runState]
  | cons s rest ih =>
    simp only [readObjEnv, runState, stepState]
    cases s <;> (dsimp only; apply ih)

omit [Field F] in
/-- `readPositions` of a concatenation splits into two pieces, the second
    evaluated under the objEnv produced by processing the first. -/
theorem readPositions_append {F : Type}
    (structs : (i : Fin n) → StructDef n F) (i : Fin n) (objEnv : ObjEnv)
    (s1 s2 : List (ConstrainStmt n F)) :
    readPositions structs i objEnv (s1 ++ s2) =
      readPositions structs i objEnv s1 ++
      readPositions structs i (readObjEnv objEnv s1) s2 := by
  induction s1 generalizing objEnv with
  | nil => simp [readPositions, readObjEnv]
  | cons s rest ih =>
    simp only [List.cons_append, readPositions, readObjEnv]
    cases s
    all_goals (dsimp only; rw [ih])
    -- For readMember, we additionally append the recorded (path, member)
    simp

end StructInlineIR
