/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Semantics

/-!
# T1 Macro-Expansion Theorem

Phase 0, body-level version of the T1 (no-fresh-temp) macro-expansion theorem.

Module-level `PresReflPass` construction is Phase 1 work (requires
`Language` instances from `Core/Eval.lean`).

## What T1 says

Given:
- Source dialect set `Δ` with handlers `handlers`.
- Target dialect set `Δ'` with handlers `handlers'`.
- A per-op lowering `lowerOp`, generic over `OpCtx γ`, that replaces each op
  of each source dialect with a list of target statements.
- Simulation conditions `T1ConstrainSim` / `T1ComputeSim`: for each op, the
  lowered list produces the same final environment and constraint as the
  original `constrainStep` / `computeStep`.

Then for any body `stmts`, the lowered body `lowerBody lowerOp stmts` is
semantically equivalent.

## Note on `callHandler`

T1 is stated for a fixed `callHandler`. Both sides use the *same* handler
because `call` statements pass through `lowerBody` unchanged — the pass
erases only leaf ops, not calls.
-/

namespace Dialect

variable {F : Type} [Field F]

/-! ## Body lowering -/

/--
Lower a statement list by replacing each leaf op with the result of
`lowerOp`. `call` statements pass through unchanged.

`lowerOp` is generic over `OpCtx` so it can be used in any body; Lean
infers `γ` at each call site from the op's type.
-/
def lowerBody
    {Δ Δ' : DialectSet} {calls : Bool}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    {γ : OpCtx} : List (Stmt Δ calls γ F) → List (Stmt Δ' calls γ F)
  | [] => []
  | .op d p               :: rest => lowerOp d p ++ lowerBody lowerOp rest
  | .call h dst t sel args :: rest => .call h dst t sel args :: lowerBody lowerOp rest

omit [Field F] in
@[simp] theorem lowerBody_nil
    {Δ Δ' : DialectSet} {calls : Bool} {γ : OpCtx}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F)) :
    lowerBody lowerOp ([] : List (Stmt Δ calls γ F)) = [] := rfl

omit [Field F] in
@[simp] theorem lowerBody_op
    {Δ Δ' : DialectSet} {calls : Bool} {γ : OpCtx}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    (d : Fin Δ.length) (p : (Δ.get d).Op γ F) (rest : List (Stmt Δ calls γ F)) :
    lowerBody lowerOp (.op d p :: rest) = lowerOp d p ++ lowerBody lowerOp rest := rfl

omit [Field F] in
@[simp] theorem lowerBody_call
    {Δ Δ' : DialectSet} {calls : Bool} {γ : OpCtx}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    (h : calls = true) (dst : Option LocalVar) (t : Fin γ.i) (sel : Nat)
    (args : List LocalVar) (rest : List (Stmt Δ calls γ F)) :
    lowerBody lowerOp (.call h dst t sel args :: rest) =
      .call h dst t sel args :: lowerBody lowerOp rest := rfl

/-! ## Append lemmas -/

/-- Constrain body over a concatenated list splits into two sequential evaluations. -/
theorem evalConstrainBody_append
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ConstrainCallHandler γ F)
    (l1 l2 : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalConstrainBody handlers callHandler (l1 ++ l2) env ↔
    evalConstrainBody handlers callHandler l1 env ∧
    evalConstrainBody handlers callHandler l2
      (evalConstrainEnv handlers callHandler l1 env) := by
  induction l1 generalizing env with
  | nil => simp
  | cons s rest ih =>
    simp only [List.cons_append, evalConstrainBody_cons, evalConstrainEnv_cons, ih]
    tauto

/-- Compute body over a concatenated list faults if the first half faults. -/
theorem evalComputeBody_append
    {Δ : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (callHandler : ComputeCallHandler γ F)
    (l1 l2 : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalComputeBody handlers callHandler (l1 ++ l2) env =
    (evalComputeBody handlers callHandler l1 env).bind
      (evalComputeBody handlers callHandler l2) := by
  induction l1 generalizing env with
  | nil => simp
  | cons s rest ih =>
    simp only [List.cons_append, evalComputeBody_cons, Option.bind_assoc]
    congr 1; funext e; exact ih e

/-! ## T1 simulation conditions -/

/--
Per-op constrain-context simulation condition.

For each dialect `d`, op `op`, call-handler `callHandler`, and env `env`,
the lowered op list must produce the same final env (`.1`) and the same
constraint (`.2`) as the original `constrainStep`.
-/
def T1ConstrainSim
    {Δ Δ' : DialectSet} {calls : Bool}
    (handlers : HandlerFamily Δ F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    (handlers' : HandlerFamily Δ' F) : Prop :=
  ∀ {γ : OpCtx} (d : Fin Δ.length) (op : (Δ.get d).Op γ F)
    (ch : ConstrainCallHandler γ F) (env : LocalVar → F),
    evalConstrainEnv handlers' ch (lowerOp d op) env =
      ((handlers d).constrainStep op env).1 ∧
    (evalConstrainBody handlers' ch (lowerOp d op) env ↔
      ((handlers d).constrainStep op env).2)

/--
Per-op compute-context simulation condition.

For each dialect `d`, op `op`, call-handler, and env, the lowered op list
must produce the same `Option (LocalVar → F)` as `computeStep`.
-/
def T1ComputeSim
    {Δ Δ' : DialectSet} {calls : Bool}
    (handlers : HandlerFamily Δ F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    (handlers' : HandlerFamily Δ' F) : Prop :=
  ∀ {γ : OpCtx} (d : Fin Δ.length) (op : (Δ.get d).Op γ F)
    (ch : ComputeCallHandler γ F) (env : LocalVar → F),
    evalComputeBody handlers' ch (lowerOp d op) env =
      (handlers d).computeStep op env

/-! ## T1 macro-expansion theorem (body level) -/

/--
**T1 constrain theorem.** Under `T1ConstrainSim`, lowering a constrain body
preserves the emitted constraint set (iff) for any initial environment.

Proof: induction on `stmts`; `op` case uses `evalConstrainBody_append` +
sim; `call` case passes through unchanged.
-/
theorem t1_constrainBody
    {Δ Δ' : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (handlers' : HandlerFamily Δ' F)
    (callHandler : ConstrainCallHandler γ F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    (sim : T1ConstrainSim handlers lowerOp handlers')
    (stmts : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalConstrainBody handlers' callHandler (lowerBody lowerOp stmts) env ↔
    evalConstrainBody handlers callHandler stmts env := by
  induction stmts generalizing env with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | op d p =>
      simp only [lowerBody_op, evalConstrainBody_cons, evalConstrainStep]
      rw [evalConstrainBody_append]
      obtain ⟨env_eq, body_iff⟩ := sim d p callHandler env
      rw [env_eq, body_iff]
      exact and_congr Iff.rfl (ih _)
    | call h dst t sel args =>
      simp only [lowerBody_call, evalConstrainBody_cons, evalConstrainStep]
      exact and_congr Iff.rfl (ih _)

/--
**T1 compute theorem.** Under `T1ComputeSim`, lowering a compute body
preserves the `Option (LocalVar → F)` result.
-/
theorem t1_computeBody
    {Δ Δ' : DialectSet} {calls : Bool} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (handlers' : HandlerFamily Δ' F)
    (callHandler : ComputeCallHandler γ F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' calls γ F))
    (sim : T1ComputeSim handlers lowerOp handlers')
    (stmts : List (Stmt Δ calls γ F)) (env : LocalVar → F) :
    evalComputeBody handlers' callHandler (lowerBody lowerOp stmts) env =
    evalComputeBody handlers callHandler stmts env := by
  induction stmts generalizing env with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | op d p =>
      simp only [lowerBody_op, evalComputeBody_cons, evalComputeStep]
      rw [evalComputeBody_append, sim d p callHandler env]
      congr 1; funext e; exact ih e
    | call h dst t sel args =>
      simp only [lowerBody_call, evalComputeBody_cons, evalComputeStep]
      congr 1; funext e; exact ih e

end Dialect
