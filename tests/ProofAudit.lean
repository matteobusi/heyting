import Heyting.Passes.DialectPipeline

/-!
# Major compiler proof axiom audit

Print the axiom dependencies of the principal composition interfaces and semantic
bridges. The statements have different contracts; see `docs/AUDIT.md` before treating
any one of them as whole-compiler preservation/reflection.
-/

#print axioms PresReflPass.compose
#print axioms Dialect.StructuralPass.compose
#print axioms WitnessCodec.CompilationArtifact.compose
#print axioms Dialect.OracleErasure.checkAt_eq_checkProjectedAt
#print axioms Dialect.OracleErasure.directConstraintPass
#print axioms Dialect.ObjectCallSemantics.directConstraintPass
#print axioms Dialect.ObjectCallSemantics.directPrefixPass
#print axioms Dialect.ObjectCallSemantics.structuralPrefix_satisfies_iff
#print axioms Dialect.StructObjectPass.lowerBody_simulation
#print axioms Dialect.StructObjectPass.lowerBody_canonical_iff
#print axioms Dialect.StructObjectPass.lowerFunc_canonical_iff
#print axioms Dialect.R1CSLikePass.source_materialize_iff
#print axioms Dialect.R1CSLike.CorrectPass
#print axioms Dialect.R1CSLike.compileWitness_satisfies_iff
#print axioms Dialect.R1CSLike.toR1CS_reflection
#print axioms Dialect.Pipeline.typed_source_artifact_iff
#print axioms Dialect.Pipeline.typed_source_r1cs_iff
#print axioms Dialect.Pipeline.generated_typed_source_r1cs_iff
#print axioms Dialect.Pipeline.typed_pipeline_readback
#print axioms Dialect.StructObjectPass.lowerFunc_related_iff
#print axioms Dialect.R1CSLikePass.source_target_related_materialize_iff
