/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Dialect

/-!
# Generic Dialect Semantics

Per-dialect `DialectSem` handler interface, a family of handlers for a
`DialectSet`, and generic body evaluators for constrain and compute contexts.

## Design

`DialectSem` bundles the two step functions (`constrainStep`,
`computeStep`) with the laws needed by the T1 macro-expansion theorem:
reads-congruence and dest-frame. Rename-commutation laws (needed for T2 and
`EraseCalls` freshening proofs) are deferred to Phase 2.

The body evaluators are structurally recursive on the statement list and do
**not** handle `call` directly — call semantics are supplied as an opaque
`ConstrainCallHandler`/`ComputeCallHandler` continuation. This separation
keeps the list-level evaluators termination-trivial; the module-level
evaluator in `Core/Eval.lean` supplies call handlers via well-founded
recursion on the callable index `i`.

## Note on definition style

`evalConstrainBody`/`evalConstrainEnv`/`evalComputeBody` use `.1`/`.2`
projections rather than `let` bindings so that the `@[simp]` equation
lemmas are definitionally `rfl` and simp can reduce them without unfolding
into `Prod.casesOn`.
-/

namespace Dialect

variable {F : Type} [Field F]

/-! ## Per-dialect handler interface -/

/--
Semantic handlers for one dialect over field `F`.

`constrainStep op env` returns `(new_env, emitted_constraint)`.
Arithmetic ops emit `True` and update `new_env`; `constrainEq`-style ops
emit `src₁ = src₂` and leave `new_env = env`.

`computeStep op env` returns the updated environment or `none` on fault
(e.g. division by zero).
-/
structure DialectSem (sig : OpSig) (F : Type) [Field F] where
  /-- Constrain-context step: `(new_env, emitted_Prop)`. -/
  constrainStep : ∀ {γ : OpCtx}, sig.Op γ F → (LocalVar → F) → (LocalVar → F) × Prop

  /-- Compute-context step: updated env or `none` on fault. -/
  computeStep : ∀ {γ : OpCtx}, sig.Op γ F → (LocalVar → F) → Option (LocalVar → F)

  /-- `constrainStep` depends only on `reads op`. -/
  constrainStep_congr : ∀ {γ : OpCtx} (op : sig.Op γ F) (env₁ env₂ : LocalVar → F),
    (∀ v ∈ sig.reads op, env₁ v = env₂ v) →
    constrainStep op env₁ = constrainStep op env₂

  /-- `constrainStep` does not modify variables other than `dest op`. -/
  constrainStep_frame : ∀ {γ : OpCtx} (op : sig.Op γ F) (env : LocalVar → F) (v : LocalVar),
    sig.dest op ≠ some v →
    (constrainStep op env).1 v = env v

  /-- `computeStep` depends only on `reads op`. -/
  computeStep_congr : ∀ {γ : OpCtx} (op : sig.Op γ F) (env₁ env₂ : LocalVar → F),
    (∀ v ∈ sig.reads op, env₁ v = env₂ v) →
    computeStep op env₁ = computeStep op env₂

  /-- On success, `computeStep` does not modify variables other than `dest op`. -/
  computeStep_frame : ∀ {γ : OpCtx} (op : sig.Op γ F) (env env' : LocalVar → F) (v : LocalVar),
    computeStep op env = some env' →
    sig.dest op ≠ some v →
    env' v = env v

/-- A family of dialect handlers, one per dialect in `Δ`. -/
abbrev HandlerFamily (Δ : DialectSet) (F : Type) [Field F] :=
  (d : Fin Δ.length) → DialectSem (Δ.get d) F

/-! ## Call handler types -/

/--
Handler for `call` in constrain context. Returns `(new_env, emitted_Prop)`.
`dst = none` for void calls; `dst = some d` for value-returning calls.
-/
abbrev ConstrainCallHandler (γ : OpCtx) (F : Type) :=
  Option LocalVar → Fin γ.i → Nat → List LocalVar → (LocalVar → F) →
  (LocalVar → F) × Prop

/-- Handler for `call` in compute context. Returns updated env or `none`. -/
abbrev ComputeCallHandler (γ : OpCtx) (F : Type) :=
  Option LocalVar → Fin γ.i → Nat → List LocalVar → (LocalVar → F) →
  Option (LocalVar → F)

/-! ## Single-step dispatch -/

/-- Execute one statement in constrain context. -/
@[inline] def evalConstrainStep
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ConstrainCallHandler γ F)
    (s : Stmt Δ calls γ F)
    (env : LocalVar → F) : (LocalVar → F) × Prop :=
  match s with
  | .op d p                => (handlers d).constrainStep p env
  | .call _ dst t sel args => callHandler dst t sel args env

/-- Execute one statement in compute context. -/
@[inline] def evalComputeStep
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ComputeCallHandler γ F)
    (s : Stmt Δ calls γ F)
    (env : LocalVar → F) : Option (LocalVar → F) :=
  match s with
  | .op d p                => (handlers d).computeStep p env
  | .call _ dst t sel args => callHandler dst t sel args env

/-! ## Body evaluators -/

/--
Constrain body: thread env through statements, conjoin emitted constraints.
`call` dispatches to `callHandler`. Structurally recursive on `stmts`.
-/
def evalConstrainBody
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ConstrainCallHandler γ F)
    (stmts : List (Stmt Δ calls γ F))
    (env : LocalVar → F) : Prop :=
  match stmts with
  | []       => True
  | s :: rest =>
    (evalConstrainStep handlers callHandler s env).2 ∧
    evalConstrainBody handlers callHandler rest (evalConstrainStep handlers callHandler s env).1

/--
Final env after executing a constrain body.
Companion to `evalConstrainBody` for frame/congruence proofs.
-/
def evalConstrainEnv
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ConstrainCallHandler γ F)
    (stmts : List (Stmt Δ calls γ F))
    (env : LocalVar → F) : LocalVar → F :=
  match stmts with
  | []       => env
  | s :: rest =>
    evalConstrainEnv handlers callHandler rest (evalConstrainStep handlers callHandler s env).1

/-- Compute body: thread env through statements, fault on `none`. -/
def evalComputeBody
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ComputeCallHandler γ F)
    (stmts : List (Stmt Δ calls γ F))
    (env : LocalVar → F) : Option (LocalVar → F) :=
  match stmts with
  | []       => some env
  | s :: rest =>
    (evalComputeStep handlers callHandler s env).bind
      (evalComputeBody handlers callHandler rest)

/-! ## Equation lemmas -/

@[simp] theorem evalConstrainBody_nil
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) (callHandler : ConstrainCallHandler γ F)
    (env : LocalVar → F) :
    evalConstrainBody handlers callHandler ([] : List (Stmt Δ calls γ F)) env = True := rfl

@[simp] theorem evalConstrainBody_cons
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) (callHandler : ConstrainCallHandler γ F)
    (s : Stmt Δ calls γ F) (rest : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalConstrainBody handlers callHandler (s :: rest) env =
      ((evalConstrainStep handlers callHandler s env).2 ∧
       evalConstrainBody handlers callHandler rest
         (evalConstrainStep handlers callHandler s env).1) := rfl

@[simp] theorem evalConstrainEnv_nil
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) (callHandler : ConstrainCallHandler γ F)
    (env : LocalVar → F) :
    evalConstrainEnv handlers callHandler ([] : List (Stmt Δ calls γ F)) env = env := rfl

@[simp] theorem evalConstrainEnv_cons
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) (callHandler : ConstrainCallHandler γ F)
    (s : Stmt Δ calls γ F) (rest : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalConstrainEnv handlers callHandler (s :: rest) env =
      evalConstrainEnv handlers callHandler rest
        (evalConstrainStep handlers callHandler s env).1 := rfl

@[simp] theorem evalComputeBody_nil
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) (callHandler : ComputeCallHandler γ F)
    (env : LocalVar → F) :
    evalComputeBody handlers callHandler ([] : List (Stmt Δ calls γ F)) env = some env := rfl

@[simp] theorem evalComputeBody_cons
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) (callHandler : ComputeCallHandler γ F)
    (s : Stmt Δ calls γ F) (rest : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalComputeBody handlers callHandler (s :: rest) env =
      (evalComputeStep handlers callHandler s env).bind
        (evalComputeBody handlers callHandler rest) := rfl

end Dialect
