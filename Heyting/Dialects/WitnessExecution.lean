/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.ASTToDialect
import Heyting.Core.WitnessSemantics

/-!
# Dialect compute execution

Executable semantics for the typed compute-side source set
`[Call, StructObject, Oracle, Felt, ConstrainEq]`. The state makes field locals,
object paths, witness storage, allocation, and the oracle cursor explicit.
Recursive calls are topologically decreasing and thread the witness, allocation,
and oracle components linearly.

The evaluator produces candidates, not proofs that the constraint body accepts them.
The named runtime faults distinguish execution failure from Boolean constraint failure.
The whole-pipeline generated-witness theorem assumes successful generation and forwarding;
it does not prove that this interpreter succeeds or satisfies constraints for all inputs.
-/

namespace Dialect.WitnessExecution

open Dialect

abbrev ResidualSet : DialectSet :=
  [StructObject.sig, Oracle.sig, Felt.sig, ConstrainEq.sig]

abbrev SourceSet : DialectSet := Call.sig :: ResidualSet

abbrev Fault := WitnessSemantics.RuntimeFault

structure State (F : Type) where
  values : LocalVar → F
  objects : StructObject.ObjEnv
  witness : StructObject.Witness F
  nextPath : Nat
  oracle : Oracle.Stream F

def ValueEnv.update (env : LocalVar → F) (dest : LocalVar) (value : F) :
    LocalVar → F :=
  fun v => if v = dest then value else env v

def bindValues [OfNat F 0] (caller : LocalVar → F) (args : List LocalVar) :
    LocalVar → F :=
  fun v => match args[v]? with
    | some arg => caller arg
    | none => 0

def bindObjects (caller : StructObject.ObjEnv) (args : List LocalVar) :
    StructObject.ObjEnv :=
  fun v => match args[v]? with
    | some arg => caller arg
    | none => []

def objectStep (op : StructObject.Op γ F) (state : State F) : State F :=
  let out := StructObject.apply op {
    values := state.values
    objects := state.objects
    witness := state.witness
    nextPath := state.nextPath
  }
  { state with
    values := out.values
    objects := out.objects
    witness := out.witness
    nextPath := out.nextPath }

def structHandler (F : Type) :
    WitnessSemantics.DialectHandler StructObject.sig (State F) F where
  step op state := .ok (objectStep op state)

def oracleHandler (F : Type) :
    WitnessSemantics.DialectHandler Oracle.sig (State F) F where
  step op state :=
    match op with
    | .next dest =>
      match state.oracle.values[state.oracle.cursor]? with
      | none => .error .oracleUnderflow
      | some value => .ok { state with
          values := ValueEnv.update state.values dest value
          oracle := state.oracle.advance }

def feltHandler [Field F] [DecidableEq F] :
    WitnessSemantics.DialectHandler Felt.sig (State F) F where
  step op state :=
    match op with
    | .div _ _ src2 =>
      if state.values src2 = 0 then .error (.divisionByZero src2)
      else .ok { state with values := Felt.applyOp op state.values }
    | _ => .ok { state with values := Felt.applyOp op state.values }

def constrainHandler (F : Type) :
    WitnessSemantics.DialectHandler ConstrainEq.sig (State F) F where
  step _ state := .ok state

/-- The source runtime is assembled dialect-by-dialect. Adding a leaf dialect
requires one handler and one assembly case; the evaluator below is unchanged. -/
def residualHandlers [Field F] [DecidableEq F] :
    WitnessSemantics.HandlerFamily ResidualSet (State F) F
  | ⟨0, _⟩ => structHandler F
  | ⟨1, _⟩ => oracleHandler F
  | ⟨2, _⟩ => feltHandler
  | ⟨3, _⟩ => constrainHandler F

/-- Evaluate a typed compute body. `Call` is the sole structural case; every
leaf statement is dispatched through the statically assembled residual family. -/
def evalBody [Field F] [DecidableEq F] {n : Nat}
    (m : Module SourceSet n F) (i : Fin n) (state : State F)
    (body : List (Stmt SourceSet
      ⟨n, i.val, (m.structs i).members.length⟩ F)) : Except Fault (State F) :=
  match body with
  | [] => .ok state
  | .op d payload :: rest =>
    let step : Except Fault (State F) :=
      match d with
      | ⟨0, _⟩ =>
        match payload with
        | .call dest target selector args =>
          if selector != 0 then .error (.unsupportedCallSelector selector)
          else
            let j : Fin n := Call.moduleTarget target i.isLt
            let callee := m.structs j
            let calleeState : State F := {
              values := bindValues state.values args
              objects := bindObjects state.objects args
              witness := state.witness
              nextPath := state.nextPath
              oracle := state.oracle
            }
            match evalBody m j calleeState callee.compute.body with
            | .error fault => .error fault
            | .ok result =>
              let values := match dest, callee.compute.returnVar with
                | some dst, some ret => ValueEnv.update state.values dst (result.values ret)
                | _, _ => state.values
              let objects := match dest, callee.compute.returnVar with
                | some dst, some ret =>
                    StructObject.ObjEnv.update state.objects dst (result.objects ret)
                | _, _ => state.objects
              .ok { state with
                values := values
                objects := objects
                witness := result.witness
                nextPath := result.nextPath
                oracle := result.oracle }
      | ⟨index + 1, h⟩ =>
        let residualIx : Fin ResidualSet.length := ⟨index, by
          simp [SourceSet, ResidualSet] at h ⊢
          omega⟩
        (residualHandlers residualIx).step payload state
    step.bind fun state' => evalBody m i state' rest
termination_by (i.val, body.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Initial compute state of an entry: its inputs are the first locals, no object exists yet,
and the witness store is empty (zero). -/
def initialState [Field F] (inputs oracle : List F) : State F :=
  { values := fun k => inputs[k]?.getD 0
    objects := fun _ => []
    witness := fun _ => 0
    nextPath := 0
    oracle := { values := oracle } }

/-- Execute the main struct's typed compute function and return the witness of the object it
returns, re-rooted at path `[]` (the root object of the constraint semantics), together with
the consumed-oracle count. Sub-components stored by `writeObject` lie below that object. -/
def genWitness [Field F] [DecidableEq F] {k : Nat}
    (m : Module SourceSet (k + 1) F) (inputs : List F)
    (oracle : List F := []) : Except Fault (StructObject.Witness F × Nat) :=
  let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let s := m.structs entry
  (evalBody m entry (initialState inputs oracle) s.compute.body).map fun out =>
    let root := match s.compute.returnVar with
      | some ret => out.objects ret
      | none => []
    (fun (path, member) => out.witness (root ++ path, member), out.oracle.cursor)

/-! ## Faults

The executor faults only on run-time data (an exhausted oracle or a zero denominator), once
every compute call uses the supported selector `0`. It never raises `invalidCallTarget`:
call targets are topological by typing. -/

/-- Faults caused by run-time data: an exhausted oracle or a zero denominator. -/
def isDataFault : Fault → Bool
  | .oracleUnderflow | .divisionByZero _ => true
  | _ => false

/-- Selectors of the `Call` statements of a body, in order. -/
def callSelectors {γ : OpCtx} : List (Stmt SourceSet γ F) → List Nat
  | [] => []
  | .op ⟨0, _⟩ (.call _ _ sel _) :: rest => sel :: callSelectors rest
  | _ :: rest => callSelectors rest

/-- Every compute call of `m` uses selector `0`. -/
def SelectorsSupported {n : Nat} (m : Module SourceSet n F) : Prop :=
  ∀ j, ∀ sel ∈ callSelectors (m.structs j).compute.body, sel = 0

/-- Executable check of `SelectorsSupported`. -/
def checkSelectors {n : Nat} (m : Module SourceSet n F) : Bool :=
  (List.finRange n).all fun j ↦ (callSelectors (m.structs j).compute.body).all (· == 0)

/-- `checkSelectors` decides `SelectorsSupported`. -/
theorem checkSelectors_iff {n : Nat} (m : Module SourceSet n F) :
    checkSelectors m = true ↔ SelectorsSupported m := by
  simp [checkSelectors, SelectorsSupported]

/-- A leaf handler faults only on run-time data. -/
theorem residualHandlers_fault [Field F] [DecidableEq F] {γ : OpCtx}
    (d : Fin ResidualSet.length) (payload : (ResidualSet.get d).Op γ F) (state : State F)
    (fault : Fault) (h : (residualHandlers d).step payload state = .error fault) :
    isDataFault fault = true := by
  match d, payload with
  | ⟨0, _⟩, _ => cases h
  | ⟨1, _⟩, .next _ =>
    simp only [residualHandlers, oracleHandler] at h
    split at h <;> cases h
    rfl
  | ⟨2, _⟩, payload =>
    simp only [residualHandlers, feltHandler] at h
    split at h
    · split_ifs at h
      cases h
      rfl
    · cases h
  | ⟨3, _⟩, _ => cases h

/-- Under `SelectorsSupported`, a body whose own calls use selector `0` faults only on
run-time data.

Proof sketch: strong induction on the struct index, then induction on the body. A leaf
statement faults by `residualHandlers_fault`; a call has selector `0` and faults only when the
callee body (an earlier struct) does. -/
theorem evalBody_fault [Field F] [DecidableEq F] {n : Nat} (m : Module SourceSet n F)
    (hm : SelectorsSupported m) (i : Fin n) (state : State F)
    (body : List (Stmt SourceSet ⟨n, i.val, (m.structs i).members.length⟩ F))
    (hbody : ∀ sel ∈ callSelectors body, sel = 0) (fault : Fault)
    (h : evalBody m i state body = .error fault) :
    isDataFault fault = true := by
  induction hv : i.val using Nat.strong_induction_on generalizing i state body fault with
  | _ v ih =>
  induction body generalizing state with
  | nil => simp [evalBody] at h
  | cons stmt rest ihb =>
    obtain ⟨d, payload⟩ := stmt
    match d, payload with
    | ⟨0, _⟩, .call dest target sel args =>
      have hsel : sel = 0 := hbody sel (by simp [callSelectors])
      subst hsel
      rw [evalBody] at h
      simp only [Except.bind, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
      have hrest : ∀ sel ∈ callSelectors rest, sel = 0 :=
        fun sel hs ↦ hbody sel (by simp [callSelectors, hs])
      split at h
      · next fault' hcallee =>
        split at hcallee
        · next fault'' hexec =>
          cases hcallee
          cases h
          exact ih _ (hv ▸ target.isLt) _ _ _ (hm _) _ hexec rfl
        · cases hcallee
      · exact ihb _ hrest h
    | ⟨idx + 1, hd⟩, payload =>
      have hrest : ∀ sel ∈ callSelectors rest, sel = 0 :=
        fun sel hs ↦ hbody sel (by simpa [callSelectors] using hs)
      rw [evalBody] at h
      simp only [Except.bind] at h
      split at h
      · next fault' hstep =>
        cases h
        exact residualHandlers_fault _ _ _ _ hstep
      · exact ihb _ hrest h

/-- Witness generation for a module whose compute calls use selector `0` fails only on
run-time data: an exhausted oracle or a zero denominator. -/
theorem genWitness_fault [Field F] [DecidableEq F] {k : Nat} (m : Module SourceSet (k + 1) F)
    (hm : SelectorsSupported m) (inputs oracle : List F) (fault : Fault)
    (h : genWitness m inputs oracle = .error fault) :
    isDataFault fault = true := by
  unfold genWitness at h
  cases he : evalBody m ⟨k, Nat.lt_succ_self k⟩ (initialState inputs oracle)
      (m.structs ⟨k, Nat.lt_succ_self k⟩).compute.body with
  | error fault' =>
    simp only [he, Except.map, Except.error.injEq] at h
    exact h ▸ evalBody_fault m hm _ _ _ (hm _) _ he
  | ok _ => simp [he, Except.map] at h

end Dialect.WitnessExecution
