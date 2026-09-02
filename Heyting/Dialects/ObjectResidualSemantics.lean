/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.CallErasure

/-!
# Object-aware residual semantics

Concrete constraint semantics for `[StructObject, Felt, ConstrainEq]`. The
stage state is the standalone StructObject state: field locals, object paths,
witness storage, and the allocation counter. This is the residual
interpretation used by the Phase-11 structural Call certificate.
-/

namespace Dialect.ObjectResidualSemantics

open Dialect

abbrev Set : DialectSet :=
  [StructObject.sig, Felt.sig, ConstrainEq.sig]

/-- Execute one residual constraint statement and return its constraint. -/
def evalStmt [Field F] {ctx : OpCtx} :
    Stmt Set ctx F → StructObject.State F → StructObject.State F × Prop
  | .op ⟨0, _⟩ op, state => (StructObject.apply op state, True)
  | .op ⟨1, _⟩ op, state =>
      ({ state with values := Felt.applyOp op state.values },
        Felt.backendValid op state.values)
  | .op ⟨2, _⟩ op, state =>
      match op with
      | .eq a b => (state, state.values a = state.values b)

/-- Sequential residual constraint semantics. -/
def evalBody [Field F] {ctx : OpCtx} :
    List (Stmt Set ctx F) → StructObject.State F → StructObject.State F × Prop
  | [], state => (state, True)
  | stmt :: rest, state =>
    let step := evalStmt stmt state
    let tail := evalBody rest step.1
    (tail.1, step.2 ∧ tail.2)

abbrev ConstraintState (n : Nat) (F : Type) :=
  Fin n × StructObject.State F

/-- Object-aware call-free module stage. -/
def stage (n : Nat) (F : Type) [Field F] : ModuleStage Set n F where
  State := ConstraintState n F
  satisfies observation m :=
    (evalBody (m.structs observation.1).constrain.body observation.2).2

/-- Object-aware Call-bearing stage, with Call interpreted by hygienic
expansion into the residual stage. -/
noncomputable def callStage (n : Nat) (F : Type) [Field F] :
    ModuleStage (Call.sig :: Set) n F :=
  CallErasure.expandedSourceStage
    (CallErasure.objectFeltConstrainSyntax (F := F)) (stage n F)

/-- Certified Phase-11 object-aware Call erasure. -/
noncomputable def eraseCallPass (n : Nat) (F : Type) [Field F] :
    EraseDialect Call.sig Set (callStage n F) (stage n F) :=
  CallErasure.structuralPass
    (CallErasure.objectFeltConstrainSyntax (F := F))
    (CallErasure.objectFeltConstrainRenameStable (F := F))
    (stage n F)

end Dialect.ObjectResidualSemantics
