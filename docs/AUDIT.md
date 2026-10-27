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

It also proves `A.artifact.readback z = w` under the same success premise. This pointwise
form is the base case; `typed_entry_correct` (below) adds arbitrary-target reflection,
existential preservation and totality of `forward` on canonical satisfying sources.
There is no claim about parser fidelity or serialized bytes. Public-wire visibility is covered
by `entryLevinReduction` and the `WireAssignment` layout theorems (see GUARANTEES).

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

### Direct prefix alignment

`TypedSourceSemantics.ConstraintObservation` shares the selected entry, finite inputs,
and finite object observations across three independently interpreted stages:

```text
TypedSourceSemantics.sourceStage
  -- OracleErasure.directConstraintPass -->
TypedSourceSemantics.projectedStage
  -- ObjectCallSemantics.directConstraintPass -->
ObjectResidualSemantics.canonicalStage
```

`ObjectCallSemantics.directPrefixPass` composes these with `StructuralPass.compose`.
Both local relations preserve the observation exactly. Preservation/reflection are
conditional only on successful module lowering, not on witness forwarding. The Call
bridge inverts function certification and uses the independent recursive simulation.
The module pass is noncomputable because module-wide Call certification uses classical
choice; the CLI still uses its existing executable selected-entry artifacts.

At the next boundary, `StructObjectPass.lowerFunc_canonical_iff` exposes the exact
certified leaf body with its canonical seed. `R1CSLikePass.evalSourceBody` is an alias
of `StructObjectPass.evalTargetBody`, so those semantics now agree definitionally,
including division validity. The existing materialization bridge uses this local theorem.

`StructObjectPass.CanonicalStateRel` supplies the finite-observation/layout adapter:
the leaf environment agrees with the canonical seed below `numParams + span`, with
all other locals unrestricted. Layout is computed from the source function, never
guessed from the erased target. `CanonicalStateRel.initial_rel` establishes the
simulation invariant; `lowerFunc_related_iff` proves both satisfaction directions
for every related environment and the exact certified target. No forwarding premise
is needed. `R1CSLikePass.source_target_related_materialize_iff` composes this with leaf
materialization. Its canonical specialization is used by the executable entry artifact's
existing correctness proof. Boundary alignment is complete, but packaging one existential
whole-entry pass remains separate work. Arbitrary-target reflection is now supplied by
`typed_source_of_r1cs`, using the zero-prefix enforcement described below.

### Item 2 repair: reserved parameters and arbitrary-target reflection

`tests/ReservedParameterReflection.lean` gives an intrinsically certified full typed
module accepted by `compileTypedEntryArtifact`: no compute parameters, one constraint
parameter, and a body comparing parameter `0` with a fresh constant `1`.
`source_unsatisfied` proves that every finite source observation fails, because source
initialization fixes the reserved parameter to zero. The old emitted R1CS accepted
the all-one assignment (including `varOne`); the regression now verifies rejection.

`R1CSLike.enforceZeroPrefix` emits terminal constant equations for reserved slots.
`satisfies_enforceZeroPrefix_iff` proves that the new target means exactly the old target
plus canonical zeros. Both entry compilation routes use this enforcement. Forwarding
checks the same invariant, retaining the pointwise theorem for arbitrary artifact values.

`Pipeline.typed_source_of_r1cs` now proves that every satisfying compiled R1CS witness
reads back to a satisfying independent typed-source observation. Proof chain: enforced
zeros → terminal reflection → finite slot readback → terminal materialization fixed point
→ related-state object reflection → Oracle/Call correspondence. No forwarding premise.
`target_unsatisfied` in the regression proves rejection of *every* target witness for the
counterexample, not only the all-one assignment. `Pipeline.typed_source_exists_r1cs` proves the converse: a canonical satisfying source
observation yields the compiled witness `compileWitness w` (from the materialized leaf witness
`w`), which satisfies the target and reads back exactly. Proof: `materialize_spec` preserves
every local below `numParams + span` (`materializeBody_preserves_params`), so reserved zeros
and finite readback survive. The layout invariant `computeParams ≤ numParams` is a field of `EntryLoweringArtifact`,
checked by `lowerEntryCertified`. `typed_source_forward_total` shows `forward` succeeds on
canonical satisfying sources (the same witness, plus its final readback/zero checks).
`typed_entry_correct` bundles both directions as `EntryCorrect`.

### Lowering-defined wrappers (existing interfaces)

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

1. Optionally repackage `EntryCorrect` as a `PresReflPass` instance (needs a source `Language`
   for finite observations and total or option-valued compilation).
2. Prove `generateSourceWitness` yields satisfying observations for a supported source class;
   `forward` totality on satisfying observations is done.
3. Establish frontend fidelity and agreement with the intended upstream LLZK fragment.
4. State and prove source generator correctness under appropriate input/program assumptions.
5. Certify byte-level serialization. Statement-wire placement and layout injectivity are
   proved (`WireAssignment`); the Circom byte encoding is tested only.
6. Formalize the transfer of knowledge soundness and zero knowledge through
   `entryLevinReduction` for an abstract proof system.

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
