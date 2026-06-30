/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.DialectPass
import Heyting.Dialects.Call
import Heyting.Dialects.Felt
import Heyting.Dialects.ConstrainEq

/-!
# EraseCalls Pass Skeleton (Phase 5)

Syntax-only lowering from the concrete source dialect set

```text
[Call, Felt, ConstrainEq]
```

into the call-free target set

```text
[Felt, ConstrainEq]
```

by inlining call targets. This file contains **no correctness theorems**;
inlining semantics preservation is Phase 6 work.

Why standalone rather than a generic `DialectPass`: the generic `FreshLowerOp`
handler has no module access, but call inlining must read the callee body from
the enclosing module. Until a module-aware pass abstraction is introduced,
`eraseBody` takes the module explicitly.

## TODO (Phase 6)

- freshen callee body without variable capture against caller locals
- bind call arguments to callee parameters
- bind callee return value to the call destination
- compute-context return binding (currently only constrain path sketched)
- prove `eraseBody` preserves `evalConstrainBody` / `evalComputeBody`
- wrap as a `ModuleConstraintPass`
-/

namespace Dialect.CallPass

open Dialect

/-! ## Concrete source / target dialect sets -/

/-- Source set with `Call` at index 0, then `Felt`, then `ConstrainEq`. -/
abbrev SourceSet : DialectSet := [Call.sig, Felt.sig, ConstrainEq.sig]

/-- Target set: `Call` erased. -/
abbrev TargetSet : DialectSet := [Felt.sig, ConstrainEq.sig]

/-- `Call` index in `SourceSet`. -/
def callSourceIx : Fin SourceSet.length := ⟨0, by simp [SourceSet]⟩

/-- `Felt` index in `SourceSet`. -/
def feltSourceIx : Fin SourceSet.length := ⟨1, by simp [SourceSet]⟩

/-- `ConstrainEq` index in `SourceSet`. -/
def constrSourceIx : Fin SourceSet.length := ⟨2, by simp [SourceSet]⟩

/-- `Felt` index in `TargetSet`. -/
def feltTargetIx : Fin TargetSet.length := ⟨0, by simp [TargetSet]⟩

/-- `ConstrainEq` index in `TargetSet`. -/
def constrTargetIx : Fin TargetSet.length := ⟨1, by simp [TargetSet]⟩

/-- A source statement is a call iff its dialect index is `callSourceIx`. -/
def isCall {γ : OpCtx} {F : Type} (s : Stmt SourceSet γ F) : Bool :=
  match s with
  | .op d _ => d == callSourceIx

/-! ## Index reindexing helpers -/

/-- Translate a `Felt` op payload from the source set to a target statement. -/
def reindexFelt {γ : OpCtx} {F : Type} (op : Felt.Op γ F) : Stmt TargetSet γ F :=
  .op feltTargetIx op

/-- Translate a `ConstrainEq` op payload from the source set to a target statement. -/
def reindexConstr {γ : OpCtx} {F : Type} (op : ConstrainEq.Op γ F) : Stmt TargetSet γ F :=
  .op constrTargetIx op

/-! ## Fresh-offset utilities -/

/-- Fresh variable offset for inlining a callee body: one past the current bound. -/
def freshOffset (next : LocalVar) (calleeBody : List (Stmt SourceSet γ F)) : LocalVar :=
  max next (maxVarBody calleeBody)

/-- Rename a local `v` into the fresh space starting at `base`. -/
def shiftLocal (base : LocalVar) (v : LocalVar) : LocalVar :=
  base + v

/-! ## Body lowering (syntax only) -/

/--
Lower a source body into the call-free target set, threading a fresh counter.

Non-call ops are reindexed unchanged. A call op is replaced by a TODO placeholder
list (empty for now): full inlining — freshen callee body, bind args, bind return —
is Phase 6. The signature and dispatch shape are fixed here so Phase 6 only fills
the call branch.
-/
def eraseBody
    {γ : OpCtx} (m : Module SourceSet n F)
    (next : LocalVar) : List (Stmt SourceSet γ F) → List (Stmt TargetSet γ F) × LocalVar
  | [] => ([], next)
  | .op d p :: rest =>
      match d, d.isLt with
      | ⟨0, _⟩, _ =>
        -- Call op (index 0). TODO (Phase 6): inline the call target's body,
        -- freshened above `next`, bind arguments to callee parameters, and bind
        -- the callee return value to the call destination. For now this branch
        -- emits nothing and keeps the fresh counter unchanged.
        let r := eraseBody m next rest
        (r.1, r.2)
      | ⟨1, _⟩, _ =>
        let s' : Stmt TargetSet γ F := reindexFelt p
        let r := eraseBody m next rest
        (s' :: r.1, r.2)
      | ⟨2, _⟩, _ =>
        let s' : Stmt TargetSet γ F := reindexConstr p
        let r := eraseBody m next rest
        (s' :: r.1, r.2)

/-! ## Function / module wrappers (syntax only) -/

/-- Lower a function body to the target dialect set. -/
def eraseFunc {n i : Nat} {kind : Capability} {numMembers : Nat}
    (m : Module SourceSet n F) (fn : FuncDef SourceSet n i F kind numMembers) :
    List (Stmt TargetSet ⟨n, i, numMembers⟩ F) :=
  (eraseBody m (max fn.numParams (maxVarBody fn.body)) fn.body).1

/-- Lower a struct's two bodies to the target dialect set. -/
def eraseStruct {n : Nat} {i : Fin n}
    (m : Module SourceSet n F) (s : StructDef SourceSet n i F) :
    List (Stmt TargetSet ⟨n, i.val, s.members.length⟩ F) ×
      List (Stmt TargetSet ⟨n, i.val, s.members.length⟩ F) :=
  (eraseFunc m s.compute, eraseFunc m s.constrain)

/-- Lower every struct body in a module to the target dialect set. -/
def eraseModule {n : Nat} (m : Module SourceSet n F) (i : Fin n) :
    List (Stmt TargetSet ⟨n, i.val, (m.structs i).members.length⟩ F) ×
      List (Stmt TargetSet ⟨n, i.val, (m.structs i).members.length⟩ F) :=
  eraseStruct m (m.structs i)

end Dialect.CallPass
