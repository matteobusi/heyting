/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.ModuleSemantics

/-!
# Call Dialect

Callable invocation syntax as ordinary dialect ops.

Initial Phase-4 semantics policy:
- `target : Fin γ.i` enforces topological calls to earlier callables.
- `sel = 0` selects the target struct's existing compute/constrain body.
- other selectors are reserved for Phase 3 first-class callable space.
-/

namespace Dialect.Call

open Dialect

inductive Op (γ : OpCtx) (F : Type) : Type where
  | call (dest : Option LocalVar) (target : Fin γ.i) (sel : Nat) (args : List LocalVar) : Op γ F
  deriving Repr

def dest : Op γ F → Option LocalVar
  | .call dst _ _ _ => dst

def reads : Op γ F → List LocalVar
  | .call _ _ _ args => args

def cap : Op γ F → Capability
  | _ => .pure

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .call dst target sel args => .call (dst.map ρ) target sel (args.map ρ)

/-- Initial selector policy: selector `0` chooses the existing compute/constrain body. -/
def selectorSupported (sel : Nat) : Bool := sel == 0

/-- Bind call arguments into a callee-local environment. -/
def bindArgs (callerEnv : LocalVar → F) (args : List LocalVar) (default : F) : LocalVar → F :=
  bindParams (args.map callerEnv) default

@[simp] theorem bindArgs_lt (callerEnv : LocalVar → F) (args : List LocalVar) (default : F)
    {v : LocalVar} (h : v < args.length) :
    bindArgs callerEnv args default v = callerEnv (args.get ⟨v, h⟩) := by
  simp [bindArgs, bindParams, h]

@[simp] theorem bindArgs_ge (callerEnv : LocalVar → F) (args : List LocalVar) (default : F)
    {v : LocalVar} (h : args.length ≤ v) :
    bindArgs callerEnv args default v = default := by
  simp [bindArgs, bindParams_ge, List.length_map, h]

/-- Lift a topological call target `Fin γ.i` into the enclosing module index. -/
def moduleTarget {n i : Nat} (target : Fin i) (hi : i < n) : Fin n :=
  ⟨target.val, Nat.lt_trans target.isLt hi⟩

/-- Lookup the target struct for a call target, given the current index is in bounds. -/
def targetStruct {Δ : DialectSet} {n : Nat} {F : Type} [Field F] {γ : OpCtx}
    (ctx : SemCtx Δ n F)
    (target : Fin γ.i)
    (hi : γ.i < n) : StructDef Δ n (moduleTarget target hi) F :=
  ctx.module.structs (moduleTarget target hi)

/-- Lookup a call target from a concrete enclosing struct index.

Unlike `targetStruct`, this form carries the topological bound in `i : Fin n`.
It is the form used by the call-aware module evaluator and call erasure pass.
-/
def targetStructAt {Δ : DialectSet} {n : Nat} {F : Type}
    (m : Module Δ n F) (i : Fin n) (target : Fin i.val) :
    StructDef Δ n (moduleTarget target i.isLt) F :=
  m.structs (moduleTarget target i.isLt)

/-- Bind a callee's optional return value to an optional caller destination.

No write occurs when either side is absent. This deliberately gives constraint
calls (which have no return value) an identity environment update.
-/
def bindReturn (dest : Option LocalVar) (value : Option F) (env : LocalVar → F) :
    LocalVar → F :=
  match dest, value with
  | some d, some v => fun x => if x = d then v else env x
  | _, _ => env

@[simp] theorem bindReturn_noneDest (value : Option F) (env : LocalVar → F) :
    bindReturn (F := F) none value env = env := by
  cases value <;> rfl

@[simp] theorem bindReturn_noneValue (dest : Option LocalVar) (env : LocalVar → F) :
    bindReturn (F := F) dest none env = env := by
  cases dest <;> rfl

@[simp] theorem bindReturn_at_dest (d : LocalVar) (value : F) (env : LocalVar → F) :
    bindReturn (some d) (some value) env d = value := by
  simp [bindReturn]

/-- Return binding leaves every non-destination local unchanged. -/
theorem bindReturn_frame (dest : Option LocalVar) (value : Option F)
    (env : LocalVar → F) (v : LocalVar) (h : dest ≠ some v) :
    bindReturn dest value env v = env v := by
  cases dest with
  | none => simp [bindReturn]
  | some d =>
    cases value with
    | none => simp [bindReturn]
    | some value =>
      have hd : d ≠ v := by
        intro hd
        apply h
        simp [hd]
      have hvd : v ≠ d := Ne.symm hd
      simp [bindReturn, hvd]

/-- Semantics of a constrain-context call once its callee has been evaluated.

Calls do not expose a return value in constrain context, so the caller
environment is unchanged and the callee's constraint proposition is emitted.
-/
def constrainStep (calleeHolds : Prop) (env : LocalVar → F) :
    (LocalVar → F) × Prop :=
  (env, calleeHolds)

@[simp] theorem constrainStep_env (calleeHolds : Prop) (env : LocalVar → F) :
    (constrainStep calleeHolds env).1 = env := rfl

@[simp] theorem constrainStep_prop (calleeHolds : Prop) (env : LocalVar → F) :
    (constrainStep calleeHolds env).2 = calleeHolds := rfl

/-- Semantics of a compute-context call once its callee has been evaluated.

The outer `none` denotes callee failure; an inner `none` is a successful
callee with no declared return value.
-/
def computeStep (dest : Option LocalVar) (calleeResult : Option (Option F))
    (env : LocalVar → F) : Option (LocalVar → F) :=
  calleeResult.map (fun returnValue => bindReturn dest returnValue env)

@[simp] theorem computeStep_failure (dest : Option LocalVar) (env : LocalVar → F) :
    computeStep (F := F) dest none env = none := rfl

@[simp] theorem computeStep_success (dest : Option LocalVar) (returnValue : Option F)
    (env : LocalVar → F) :
    computeStep dest (some returnValue) env = some (bindReturn dest returnValue env) := rfl

/-- A successful compute call preserves every non-destination local. -/
theorem computeStep_frame (dest : Option LocalVar) (returnValue : Option F)
    (env : LocalVar → F) (v : LocalVar) (h : dest ≠ some v) :
    (computeStep dest (some returnValue) env).map (fun out => out v) = some (env v) := by
  change some (bindReturn dest returnValue env v) = some (env v)
  rw [bindReturn_frame dest returnValue env v h]

def sig : OpSig where
  Op      := Op
  dest    := dest
  reads   := reads
  mapVars := mapVars
  cap     := cap
  mapVars_id    := by intro γ F op; cases op; simp [mapVars]
  mapVars_comp  := by intro γ F ρ σ op; cases op; simp [mapVars, Option.map_map, List.map_map]
  dest_mapVars  := by intro γ F ρ op; cases op; simp [mapVars, dest]
  reads_mapVars := by intro γ F ρ op; cases op; simp [mapVars, reads]
  cap_mapVars   := by intro γ F ρ op; cases op; simp [cap]

end Dialect.Call
