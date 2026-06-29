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

The body evaluators are structurally recursive on the statement list. Recursive
constructs such as calls are handled by ordinary dialect semantics.

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

  /--
  Reads congruence for constrain: if two environments agree on `reads op`,
  (1) the emitted Prop is the same (iff), and
  (2) the value written to `dest` (if any) is the same.

  Note: the whole output pair is NOT required to be equal — the non-dest
  components of the output env differ when the input envs differ on those
  variables. Only `dest` and the Prop are reads-determined.
  -/
  constrainStep_reads_congr :
    ∀ {γ : OpCtx} (op : sig.Op γ F) (env₁ env₂ : LocalVar → F),
    (∀ v ∈ sig.reads op, env₁ v = env₂ v) →
    ((constrainStep op env₁).2 ↔ (constrainStep op env₂).2) ∧
    ∀ d, sig.dest op = some d →
      (constrainStep op env₁).1 d = (constrainStep op env₂).1 d

  /-- `constrainStep` does not modify variables other than `dest op`. -/
  constrainStep_frame : ∀ {γ : OpCtx} (op : sig.Op γ F) (env : LocalVar → F) (v : LocalVar),
    sig.dest op ≠ some v →
    (constrainStep op env).1 v = env v

  /--
  Reads congruence for compute: if two environments agree on `reads op`,
  the value written to `dest` (if any) is the same (mapping through Option).
  -/
  computeStep_reads_congr :
    ∀ {γ : OpCtx} (op : sig.Op γ F) (env₁ env₂ : LocalVar → F),
    (∀ v ∈ sig.reads op, env₁ v = env₂ v) →
    ∀ d, sig.dest op = some d →
      (computeStep op env₁).map (· d) = (computeStep op env₂).map (· d)

  /-- Compute success/failure is determined by reads. -/
  computeStep_status_congr :
    ∀ {γ : OpCtx} (op : sig.Op γ F) (env₁ env₂ : LocalVar → F),
    (∀ v ∈ sig.reads op, env₁ v = env₂ v) →
      (computeStep op env₁).isSome = (computeStep op env₂).isSome

  /-- On success, `computeStep` does not modify variables other than `dest op`. -/
  computeStep_frame : ∀ {γ : OpCtx} (op : sig.Op γ F) (env env' : LocalVar → F) (v : LocalVar),
    computeStep op env = some env' →
    sig.dest op ≠ some v →
    env' v = env v

/-- A family of dialect handlers, one per dialect in `Δ`. -/
abbrev HandlerFamily (Δ : DialectSet) (F : Type) [Field F] :=
  (d : Fin Δ.length) → DialectSem (Δ.get d) F

/-! ## Single-step dispatch -/

/-- Execute one statement in constrain context. -/
@[inline] def evalConstrainStep
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F)
    (env : LocalVar → F) : (LocalVar → F) × Prop :=
  match s with
  | .op d p => (handlers d).constrainStep p env

/-- Execute one statement in compute context. -/
@[inline] def evalComputeStep
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F)
    (env : LocalVar → F) : Option (LocalVar → F) :=
  match s with
  | .op d p => (handlers d).computeStep p env

/-! ## Body evaluators -/

/--
Constrain body: thread env through statements, conjoin emitted constraints.
Structurally recursive on `stmts`.
-/
def evalConstrainBody
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (stmts : List (Stmt Δ γ F))
    (env : LocalVar → F) : Prop :=
  match stmts with
  | []       => True
  | s :: rest =>
    (evalConstrainStep handlers s env).2 ∧
    evalConstrainBody handlers rest (evalConstrainStep handlers s env).1

/--
Final env after executing a constrain body.
Companion to `evalConstrainBody` for frame/congruence proofs.
-/
def evalConstrainEnv
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (stmts : List (Stmt Δ γ F))
    (env : LocalVar → F) : LocalVar → F :=
  match stmts with
  | []       => env
  | s :: rest =>
    evalConstrainEnv handlers rest (evalConstrainStep handlers s env).1

/-- Compute body: thread env through statements, fault on `none`. -/
def evalComputeBody
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (stmts : List (Stmt Δ γ F))
    (env : LocalVar → F) : Option (LocalVar → F) :=
  match stmts with
  | []       => some env
  | s :: rest =>
    (evalComputeStep handlers s env).bind
      (evalComputeBody handlers rest)

/-! ## Equation lemmas -/

@[simp] theorem evalConstrainBody_nil
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (env : LocalVar → F) :
    evalConstrainBody handlers ([] : List (Stmt Δ γ F)) env = True := rfl

@[simp] theorem evalConstrainBody_cons
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F) (rest : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalConstrainBody handlers (s :: rest) env =
      ((evalConstrainStep handlers s env).2 ∧
       evalConstrainBody handlers rest
         (evalConstrainStep handlers s env).1) := rfl

@[simp] theorem evalConstrainEnv_nil
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (env : LocalVar → F) :
    evalConstrainEnv handlers ([] : List (Stmt Δ γ F)) env = env := rfl

@[simp] theorem evalConstrainEnv_cons
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F) (rest : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalConstrainEnv handlers (s :: rest) env =
      evalConstrainEnv handlers rest
        (evalConstrainStep handlers s env).1 := rfl

@[simp] theorem evalComputeBody_nil
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (env : LocalVar → F) :
    evalComputeBody handlers ([] : List (Stmt Δ γ F)) env = some env := rfl

@[simp] theorem evalComputeBody_cons
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F) (rest : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalComputeBody handlers (s :: rest) env =
      (evalComputeStep handlers s env).bind
        (evalComputeBody handlers rest) := rfl

end Dialect
