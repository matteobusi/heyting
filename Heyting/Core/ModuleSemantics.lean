/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Module
import Heyting.Core.Semantics

/-!
# Dialect Module Semantics

A first module-level semantics layer for dialect-native modules.

This file deliberately stays call-agnostic: it lifts the existing local/body
semantics to functions, structs, and modules, but does not assign recursive
meaning to the `Call` dialect yet. A call-aware evaluator will refine or replace
this layer once the call semantics interface is fixed.
-/

namespace Dialect

variable {F : Type}
variable {Δ : DialectSet} {n i numMembers : Nat}

/-- Positional function inputs. Local `0` receives the first argument, etc. -/
structure FuncInput (F : Type) where
  args : List F
  deriving Repr

/-- Compute result plus optional return value read from the final environment. -/
structure FuncOutput (F : Type) where
  env : LocalVar → F
  returnValue : Option F

/-- Bind positional arguments into low local variables; all other locals read `default`. -/
def bindParams (args : List F) (default : F) : LocalVar → F :=
  fun v =>
    if h : v < args.length then
      args.get ⟨v, h⟩
    else
      default

@[simp] theorem bindParams_lt (args : List F) (default : F) {v : LocalVar}
    (h : v < args.length) :
    bindParams args default v = args.get ⟨v, h⟩ := by
  simp [bindParams, h]

@[simp] theorem bindParams_ge (args : List F) (default : F) {v : LocalVar}
    (h : args.length ≤ v) :
    bindParams args default v = default := by
  have hv : ¬ v < args.length := Nat.not_lt_of_ge h
  simp [bindParams, hv]

/-- Read a function return value from an environment, if the function declares one. -/
def readReturn (returnVar : Option LocalVar) (env : LocalVar → F) : Option F :=
  returnVar.map env

@[simp] def semCtx [Field F] (m : Module Δ n F) : SemCtx Δ n F where
  module := m


@[simp] theorem readReturn_none (env : LocalVar → F) :
    readReturn (F := F) none env = none := rfl

@[simp] theorem readReturn_some (r : LocalVar) (env : LocalVar → F) :
    readReturn (F := F) (some r) env = some (env r) := rfl

/-- Evaluate a witness-generation function from positional inputs. -/
def evalFuncCompute
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (fn : FuncDef Δ n i F .witness numMembers)
    (input : FuncInput F) (default : F) : Option (FuncOutput F) :=
  (evalComputeBody handlers (semCtx m) fn.body (bindParams input.args default)).map
    (fun env => { env := env, returnValue := readReturn fn.returnVar env })

/-- Evaluate a constraint-generation function against an existing local environment. -/
def evalFuncConstrain
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (fn : FuncDef Δ n i F .constraint numMembers)
    (env : LocalVar → F) : Prop :=
  evalConstrainBody handlers (semCtx m) fn.body env

/-- Evaluate a struct by computing witness locals, then checking constraints. -/
def satisfiesStruct
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    {i : Fin n} (s : StructDef Δ n i F)
    (input : FuncInput F) (default : F) : Prop :=
  ∃ out, evalFuncCompute handlers m s.compute input default = some out ∧
    evalFuncConstrain handlers m s.constrain out.env

/-- Evaluate a module at one entry struct. -/
def satisfiesModuleAt
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (entry : Fin n)
    (input : FuncInput F) (default : F) : Prop :=
  satisfiesStruct handlers m (m.structs entry) input default

@[simp] theorem evalFuncConstrain_eq
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (fn : FuncDef Δ n i F .constraint numMembers)
    (env : LocalVar → F) :
    evalFuncConstrain handlers m fn env = evalConstrainBody handlers (semCtx m) fn.body env := rfl

@[simp] theorem evalFuncCompute_eq
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (fn : FuncDef Δ n i F .witness numMembers)
    (input : FuncInput F) (default : F) :
    evalFuncCompute handlers m fn input default =
      (evalComputeBody handlers (semCtx m) fn.body (bindParams input.args default)).map
        (fun env => { env := env, returnValue := readReturn fn.returnVar env }) := rfl

@[simp] theorem satisfiesModuleAt_eq
    [Field F]
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (entry : Fin n)
    (input : FuncInput F) (default : F) :
    satisfiesModuleAt handlers m entry input default =
      satisfiesStruct handlers m (m.structs entry) input default := rfl

end Dialect
