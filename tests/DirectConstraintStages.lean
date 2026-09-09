import Heyting.Dialects.ObjectCallSemantics
import Heyting.Dialects.R1CSLikePass
import Mathlib.Algebra.Field.Rat

/-!
# Direct constraint-stage alignment

Check that Oracle and Call compose without changing the independent source predicate,
and that the object/leaf boundary uses the same division-validating evaluator.
-/

open Dialect

noncomputable section

example (n : Nat) (F : Type) [Field F] [DecidableEq F] :
    StructuralPass (TypedSourceSemantics.sourceStage n F)
      (ObjectResidualSemantics.canonicalStage n F) :=
  ObjectCallSemantics.directPrefixPass n F

example {n : Nat} {F : Type} [Field F] [DecidableEq F]
    (source : Module TypedSourceSemantics.SourceSet n F)
    (target : Module ObjectResidualSemantics.Set n F)
    (hlower : (ObjectCallSemantics.directPrefixPass n F).lower source = .ok target)
    (observation : TypedSourceSemantics.ConstraintObservation n F)
    (hsat : TypedSourceSemantics.satisfiesAt source observation.entry
      observation.inputs observation.objects) :
    ∃ out, (ObjectCallSemantics.directPrefixPass n F).stateRel source target observation out ∧
      (ObjectResidualSemantics.canonicalStage n F).satisfies out target :=
  (ObjectCallSemantics.directPrefixPass n F).preservation source target observation hlower hsat

example {n : Nat} {F : Type} [Field F] [DecidableEq F]
    (source : Module TypedSourceSemantics.SourceSet n F)
    (target : Module ObjectResidualSemantics.Set n F)
    (hlower : (ObjectCallSemantics.directPrefixPass n F).lower source = .ok target)
    (observation : TypedSourceSemantics.ConstraintObservation n F)
    (hsat : (ObjectResidualSemantics.canonicalStage n F).satisfies observation target) :
    ∃ input, (ObjectCallSemantics.directPrefixPass n F).stateRel source target input observation ∧
      TypedSourceSemantics.satisfiesAt source input.entry input.inputs input.objects :=
  (ObjectCallSemantics.directPrefixPass n F).reflection source target observation hlower hsat

example {F : Type} [Field F] {ctx : OpCtx}
    (body : List (Stmt CallPass.TargetSet ctx F)) (env : LocalVar → F) :
    R1CSLikePass.evalSourceBody body env = StructObjectPass.evalTargetBody body env := rfl

private def zeroDivision : List (Stmt CallPass.TargetSet ⟨0, 0, 0⟩ ℚ) :=
  [.op ⟨0, by decide⟩ (.div 1 0 0)]

-- Generic field-local execution is not the division-validating compiler boundary.
example : CallSemantics.evalTargetConstrainBody zeroDivision (fun _ ↦ 0) := by
  simp [zeroDivision, CallSemantics.evalTargetConstrainBody]

example : ¬ (R1CSLikePass.evalSourceBody zeroDivision (fun _ ↦ 0)).2 := by
  simp [zeroDivision, R1CSLikePass.evalSourceBody, StructObjectPass.evalTargetBody,
    StructObjectPass.evalTargetStmt, Felt.backendValid]

#print axioms Dialect.OracleErasure.directConstraintPass
#print axioms Dialect.ObjectCallSemantics.directConstraintPass
#print axioms Dialect.ObjectCallSemantics.directPrefixPass
#print axioms Dialect.StructObjectPass.lowerFunc_canonical_iff

-- Unallocated locals are not constrained by the observation adapter.
example {F : Type} [Field F] (numParams computeParams span : Nat)
    (inputs objects : List F) (garbage : LocalVar → F) :
    StructObjectPass.CanonicalStateRel numParams computeParams span inputs objects
      (fun v ↦ if v < numParams + span then
        StructObjectPass.seedCanonicalWitness numParams span (numParams - computeParams)
          inputs objects v else garbage v) := by
  intro v hv
  simp [hv]

#print axioms Dialect.StructObjectPass.lowerFunc_related_iff
#print axioms Dialect.R1CSLikePass.source_target_related_materialize_iff
