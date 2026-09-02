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

def initialState [Field F] (numMembers : Nat) (inputs oracle : List F)
    (paramOffset : Nat) : State F :=
  let values : LocalVar → F := fun k => inputs[k]?.getD 0
  let witness : StructObject.Witness F := fun key =>
    match key with
    | ([p], 0) =>
      if p ≥ numMembers + paramOffset then
        inputs[p - (numMembers + paramOffset)]?.getD 0
      else 0
    | _ => 0
  { values := values
    objects := StructObject.ObjEnv.update (fun _ => []) 0 []
    witness := witness
    nextPath := 0
    oracle := { values := oracle } }

/-- Execute the main struct's typed compute function and return its object
witness together with the consumed-oracle count. -/
def genWitness [Field F] [DecidableEq F] {k : Nat}
    (m : Module SourceSet (k + 1) F) (inputs : List F)
    (oracle : List F := []) : Except Fault (StructObject.Witness F × Nat) :=
  let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let s := m.structs entry
  let offset := s.constrain.numParams - s.compute.numParams
  let initial := initialState s.members.length inputs oracle offset
  (evalBody m entry initial s.compute.body).map
    (fun out => (out.witness, out.oracle.cursor))

/-- Compatibility wrapper for callers that only distinguish success/failure. -/
def computeWitness [Field F] [DecidableEq F] {k : Nat}
    (m : Module SourceSet (k + 1) F) (inputs : List F)
    (oracle : List F := []) : Option (StructObject.Witness F × Nat) :=
  (genWitness m inputs oracle).toOption

end Dialect.WitnessExecution
