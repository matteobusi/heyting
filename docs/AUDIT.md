# Compiler proof audit guide

This guide describes current contracts, not the intended final theorem. Source
docstrings carry local contracts; the sketches below explain how their results fit.

## Start here

1. Read `Core/Language.lean`, `Core/Pass.lean`, `Core/StructuralPass.lean`, and
   `Core/WitnessCodec.lean`. Distinguish their quantifiers before reading any pass.
2. Read `Dialects/TypedSourceSemantics.lean` for the independent source predicate.
3. Read `Passes/DialectPipeline.lean`, especially `TypedEntryCompilationArtifact`,
   `typed_source_artifact_iff`, `typed_source_r1cs_iff`, and `typed_pipeline_readback`.
4. Follow the bridges below to their local simulations and arithmetic proofs.

All Lean paths in this guide are relative to `Heyting/`.

## Three different correctness contracts

| Interface | Contract | Important limitation |
|---|---|---|
| `PresReflPass S T` | Every satisfying source witness has a related satisfying target witness; every satisfying target witness has a related satisfying source witness | Requires exactly matching intermediate languages to compose |
| `StructuralPass S T` | Same existential directions for semantic states, assuming `lower M = Ok N` | Relative to the supplied stage predicates, which may be lowering-defined |
| `CompilationArtifact S T M` | Successful `forward w = Ok z` implies satisfaction iff and exact readback | Does not imply forward totality or arbitrary-target reflection |

`ModuleConstraintPass` provides a fourth, specialized interface: equivalence of
constraint evaluation under a common initial local environment. Composition requires
equality of the middle handlers. This is not automatically the terminal fixed-witness relation.

The whole-entry theorem currently has the third shape:

```text
A : TypedEntryCompilationArtifact M entry
A.artifact.forward w = Ok z
──────────────────────────────────────────────────────────────────
TypedSourceSatisfies M entry w ↔ R1CS.satisfies z A.artifact.target
```

It also proves `A.artifact.readback z = w` under the same success premise.
There is no claim here about arbitrary target assignments, transport totality,
parser fidelity, serialized bytes, or public-wire visibility.

## Proof chain

| Boundary | Declarations to inspect | Proof sketch and hypotheses |
|---|---|---|
| Oracle projection | `OracleErasure.constrain_body_no_oracle`, `checkAt_eq_checkProjectedAt` | Capability certification excludes Oracle reads from constraint bodies. Recursive evaluation then agrees after projection; projected compute execution is not preserved. |
| Direct Call execution → expansion | `ObjectCallSemantics.structuralPrefix_check_eq`, `structuralPrefix_satisfies_iff` | Induct over topologically decreasing calls and statement lists. Track fresh locals, argument/return binding, object aliases, storage, and allocation. Requires exact successful expansion/certification. |
| Objects → leaf locals | `StructObjectPass.lowerBody_simulation`, `lowerBody_canonical_iff` | Track static paths and aliases; member reads select encoded witness coordinates. Fresh shifted locals cannot collide with initial witness slots. Canonical specialization fixes finite input/object layout. |
| Leaf execution → terminal witness | `R1CSLikePass.materialize_spec`, `materialize_satisfies_iff`, `source_materialize_iff` | Induct over SSA bodies. Later writes cannot change earlier operands or destinations. Materialization enforces division validity; exact lowering equations identify the terminal list. |
| Terminal witness → R1CS | `R1CSLike.compileWitness_satisfies_iff` | Construct one/inverse/is-zero wires, prove each operation's equations, then induct over the constraint list. |
| Arbitrary R1CS witness → terminal | `R1CSLike.toR1CS_reflection`, `CorrectPass` | Read ordinary wires from an arbitrary satisfying assignment. Quotient and nonzero equations force division; inverse equations force the output in both zero/nonzero cases. |
| Direct source → artifact | `Pipeline.typed_source_artifact_iff` | Compose the structural and materialization bridges using exact artifact equations and canonical witness lengths. |
| Artifact → internal R1CS | `Pipeline.pipeline_witness_iff`, `typed_source_r1cs_iff` | Invert successful forwarding to obtain the materialized witness and backend success equation; compose pointwise equivalences. |
| Exact finite readback | `Pipeline.pipeline_readback`, `typed_pipeline_readback` | Invert successful forwarding and extract its final equality check. No assertion about non-forwarded target witnesses follows. |

## Structural wrappers are not independent source specifications

`CallErasure.expandedSourceStage` defines satisfaction through successful expansion
and the residual stage. `StructObjectPass.sourceStage` defines it through successful
object lowering and a related target observation. Their packaged preservation/reflection
laws are valid for these predicates. The independent interpreter connection comes from
the simulations above, not from unfolding those wrappers alone.

Do not replace `TypedSourceSemantics` with these predicates when stating a stronger
whole-compiler theorem: that would move the specification to the compiler output.

## Supporting lemmas: what their invariants mean

- `Core/Dialect.lean`, `Core/Module.lean`: operation metadata, capabilities, and SSA.
  Certification lemmas turn Boolean checks into the intrinsic function invariants.
- `Core/Semantics.lean`, `Core/ModuleSemantics.lean`: sequential handler evaluation,
  parameter binding, and module entry interpretation. List equations are definitional;
  append lemmas split sequential evaluation at a body boundary.
- `Core/DialectPass.lean`: freshness bounds and environment agreement isolate temporary
  locals. These lemmas support body simulation and SSA-preserving module construction.
- `Core/VarIdEncoding.lean`: mathematical encoding of object-path/member coordinates.
  This is distinct from the unverified finite wire numbering in `Backends/WireAssignment`.
- `Dialects/CallPass.lean`, `CallSemantics.lean`: field-local Call infrastructure.
  Retained because the active generic/object proofs use its freshening and semantic lemmas;
  it is not an alternate CLI pipeline.
- `Dialects/ObjectResidualSemantics.lean`, `StructObject.lean`: object state operations,
  residual evaluation, and frame laws used by the independent simulations.
- `Core/WitnessSemantics.lean`, `Dialects/WitnessExecution.lean`: source candidate execution
  with static dialect handlers. Candidate generation is not proof of constraint satisfaction.

## Remaining obligations

1. Align intermediate semantics/witness relations and compose whole-entry existential
   preservation/reflection, including arbitrary satisfying target assignments.
2. Prove constructive transport success for an explicitly supported source class.
3. Establish frontend fidelity and agreement with the intended upstream LLZK fragment.
4. State and prove source generator correctness under appropriate input/program assumptions.
5. Certify finite wire layout, public/private observations, and serialization. Encoding
   injectivity must be restricted to allocated constructor ranges; global injectivity is false.

These are not filled by the present pointwise theorem or by passing integration tests.

## Reproducing checks

```bash
python3 scripts/check_active_imports.py
lake build
lake build hey
lake env lean tests/ProofAudit.lean
./tests/run_tests.sh
./scripts/smoke_cli.sh
```

`tests/ProofAudit.lean` prints axioms for the major contracts and bridges. Expected
axioms: `propext`, `Classical.choice`, `Quot.sound` only. This is an audit report,
not a substitute for reading theorem statements or a mechanically enforced axiom allowlist.
CLI-only concrete field primality assumptions are documented separately in `WARNING.md`.

## Documentation conventions

Use Mathlib-like module documentation after imports and result-oriented declaration
docstrings. State success, canonical-layout, freshness, and semantic-relation premises
explicitly. Give nontrivial proofs a high-level sketch; document routine helper families
by invariant instead of narrating each tactic. Keep development chronology in Git/history
documents. Preserve theorem contracts during documentation cleanup.
