/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.ASTToDialect
import Heyting.Core.VarIdEncoding

/-!
# Direct typed-source constraint semantics

This file interprets `[Call, StructObject, Oracle, Felt, ConstrainEq]` directly.
It does not invoke Oracle projection, call expansion, object erasure, FlatIR
lowering, or a compilation artifact.

`Call` is the only structural case. The residual leaf semantics is assembled
separately over one statically selected `StructObject.State`.
-/

namespace Dialect.TypedSourceSemantics

open Dialect

abbrev ResidualSet : DialectSet :=
  [StructObject.sig, Oracle.sig, Felt.sig, ConstrainEq.sig]

abbrev SourceSet : DialectSet := Call.sig :: ResidualSet

abbrev ProjectedResidualSet : DialectSet :=
  [StructObject.sig, Felt.sig, ConstrainEq.sig]

abbrev ProjectedSet : DialectSet := Call.sig :: ProjectedResidualSet

abbrev State (F : Type) := StructObject.State F

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

/-- Direct interpretation of one non-structural statement. Oracle operations
are illegal in a certified constraint body; assigning `False` gives malformed
unchecked syntax an explicit semantics without manufacturing a value. -/
def evalLeaf [Field F] [DecidableEq F] {ctx : OpCtx} :
    Stmt ResidualSet ctx F → State F → State F × Bool
  | .op ⟨0, _⟩ op, state => (StructObject.apply op state, true)
  | .op ⟨1, _⟩ _, state => (state, false)
  | .op ⟨2, _⟩ op, state =>
      ({ state with values := Felt.applyOp op state.values },
        Felt.backendValidBool op state.values)
  | .op ⟨3, _⟩ op, state =>
      match op with
      | .eq left right => (state, decide (state.values left = state.values right))

def evalProjectedLeaf [Field F] [DecidableEq F] {ctx : OpCtx} :
    Stmt ProjectedResidualSet ctx F → State F → State F × Bool
  | .op ⟨0, _⟩ op, state => (StructObject.apply op state, true)
  | .op ⟨1, _⟩ op, state =>
      ({ state with values := Felt.applyOp op state.values },
        Felt.backendValidBool op state.values)
  | .op ⟨2, _⟩ op, state =>
      match op with
      | .eq left right => (state, decide (state.values left = state.values right))

/-- Direct, topologically recursive source constraint execution. -/
def evalBody [Field F] [DecidableEq F] {n : Nat}
    (m : Module SourceSet n F) (i : Fin n) (state : State F)
    (body : List (Stmt SourceSet
      ⟨n, i.val, (m.structs i).members.length⟩ F)) : State F × Bool :=
  match body with
  | [] => (state, true)
  | .op d payload :: rest =>
    let step : State F × Bool :=
      match d with
      | ⟨0, _⟩ =>
        match payload with
        | .call dest target selector args =>
          if selector = 0 then
            let j : Fin n := Call.moduleTarget target i.isLt
            let callee := m.structs j
            let calleeState : State F := {
              values := bindValues state.values args
              objects := bindObjects state.objects args
              witness := state.witness
              nextPath := state.nextPath
            }
            let result := evalBody m j calleeState callee.constrain.body
            let values := match dest, callee.constrain.returnVar with
              | some dst, some ret =>
                  StructObject.ValueEnv.update state.values dst (result.1.values ret)
              | _, _ => state.values
            let objects := match dest, callee.constrain.returnVar with
              | some dst, some ret =>
                  StructObject.ObjEnv.update state.objects dst (result.1.objects ret)
              | _, _ => state.objects
            ({ state with
                values := values
                objects := objects
                witness := result.1.witness
                nextPath := result.1.nextPath },
              result.2)
          else (state, false)
      | ⟨index + 1, h⟩ =>
        let residualIx : Fin ResidualSet.length := ⟨index, by
          simp [SourceSet, ResidualSet] at h ⊢
          omega⟩
        evalLeaf (.op residualIx payload) state
    let tail := evalBody m i step.1 rest
    (tail.1, step.2 && tail.2)
termination_by (i.val, body.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Direct execution after Oracle-only syntax has been projected away.

`numMembers` is explicit because Oracle projection preserves a source body's
context propositionally. Calls still enter the callee context stored in `m`. -/
def evalProjectedBodyIn [Field F] [DecidableEq F] {n numMembers : Nat}
    (m : Module ProjectedSet n F) (i : Fin n) (state : State F)
    (body : List (Stmt ProjectedSet ⟨n, i.val, numMembers⟩ F)) : State F × Bool :=
  match body with
  | [] => (state, true)
  | .op d payload :: rest =>
    let step : State F × Bool :=
      match d with
      | ⟨0, _⟩ =>
        match payload with
        | .call dest target selector args =>
          if selector = 0 then
            let j : Fin n := Call.moduleTarget target i.isLt
            let callee := m.structs j
            let calleeState : State F := {
              values := bindValues state.values args
              objects := bindObjects state.objects args
              witness := state.witness
              nextPath := state.nextPath
            }
            let result := evalProjectedBodyIn m j calleeState callee.constrain.body
            let values := match dest, callee.constrain.returnVar with
              | some dst, some ret =>
                  StructObject.ValueEnv.update state.values dst (result.1.values ret)
              | _, _ => state.values
            let objects := match dest, callee.constrain.returnVar with
              | some dst, some ret =>
                  StructObject.ObjEnv.update state.objects dst (result.1.objects ret)
              | _, _ => state.objects
            ({ state with
                values := values
                objects := objects
                witness := result.1.witness
                nextPath := result.1.nextPath },
              result.2)
          else (state, false)
      | ⟨index + 1, h⟩ =>
        let residualIx : Fin ProjectedResidualSet.length := ⟨index, by
          simp [ProjectedSet, ProjectedResidualSet] at h ⊢
          omega⟩
        evalProjectedLeaf (.op residualIx payload) state
    let tail := evalProjectedBodyIn m i step.1 rest
    (tail.1, step.2 && tail.2)
termination_by (i.val, body.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Projected execution in the selected struct's stored member context. -/
def evalProjectedBody [Field F] [DecidableEq F] {n : Nat}
    (m : Module ProjectedSet n F) (i : Fin n) (state : State F)
    (body : List (Stmt ProjectedSet
      ⟨n, i.val, (m.structs i).members.length⟩ F)) : State F × Bool :=
  evalProjectedBodyIn m i state body

/-- Initialize direct source constraint state from finite canonical
observables. Constraint-only prefix parameters (notably `%self`) are zero in
the value channel; object local `0` denotes the root path. -/
def initialState [Field F] (numParams computeParams : Nat)
    (inputs objects : List F) : State F :=
  let paramOffset := numParams - computeParams
  {
    values := fun v =>
      if v < numParams then
        if v < paramOffset then 0 else inputs[v - paramOffset]?.getD 0
      else 0
    objects := StructObject.ObjEnv.update (fun _ => []) 0 []
    witness := fun key => objects[VarIdEncoding.encode key]?.getD 0
    nextPath := 0
  }

/-- Executable direct checker for one selected entry. -/
def checkAt [Field F] [DecidableEq F] {n : Nat} (m : Module SourceSet n F)
    (entry : Fin n) (inputs objects : List F) : Bool :=
  let source := m.structs entry
  let initial := initialState source.constrain.numParams source.compute.numParams
    inputs objects
  (evalBody m entry initial source.constrain.body).2

/-- Direct satisfaction of one selected entry in the original typed module. -/
def satisfiesAt [Field F] [DecidableEq F] {n : Nat} (m : Module SourceSet n F)
    (entry : Fin n) (inputs objects : List F) : Prop :=
  checkAt m entry inputs objects = true

theorem checkAt_true_iff [Field F] [DecidableEq F] {n : Nat}
    (m : Module SourceSet n F) (entry : Fin n) (inputs objects : List F) :
    checkAt m entry inputs objects = true ↔ satisfiesAt m entry inputs objects :=
  Iff.rfl

def checkProjectedAt [Field F] [DecidableEq F] {n : Nat}
    (m : Module ProjectedSet n F) (entry : Fin n)
    (inputs objects : List F) : Bool :=
  let source := m.structs entry
  let initial := initialState source.constrain.numParams source.compute.numParams
    inputs objects
  (evalProjectedBody m entry initial source.constrain.body).2

end Dialect.TypedSourceSemantics
