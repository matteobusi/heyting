# Formal Guarantees

Current proof status for the dialect architecture and legacy reference path.

Phase 13 is complete. Dialect witness generation is modular at the source
compute boundary, and compilation returns an entry artifact containing its
exact target, structural layout, forward codec, readback, and correctness laws.
The canonical source witness contains only finite input and reachable-object
observables; call frames, paths, allocation counters, oracle cursors, ordinary
SSA locals, and R1CS auxiliaries are excluded.

Phase 14 is complete. A direct executable semantics checks the original
typed `[Call, StructObject, Oracle, Felt, ConstrainEq]` module without invoking
erasure or compilation, including nested calls and object state. Its local
checker theorem is complete. Oracle projection and hygienic Call expansion now
preserve and reflect that direct observation pointwise. StructObject erasure,
canonical seeding/readback, leaf materialization, and Phase-13 artifact
satisfaction have pointwise preservation/reflection theorems. Whole-entry
compilation retains and composes these certificates through exact R1CS target.

## Framework

Passes target `PresReflPass S T` from `Heyting/Core/Pass.lean`.

- `compile`: source program -> target program
- `witnessRel`: relation between source and target witnesses
- `reflection`: target sat -> related source sat
- `preservation`: source sat -> related target sat

When both directions exist, source and target are equisatisfiable.

Structural dialect erasures additionally use
`Heyting/Core/StructuralPass.lean`. A `StructuralPass` may change the static
semantic state type and may reject malformed input; its preservation and
reflection fields apply whenever lowering returns a concrete target module.
Explicit structural composition is proved, and total witness-backed instances
convert to/from `PresReflPass`. The certified leaf Call pass is now exposed
through this wrapper. Generic Call expansion is also certified against any
residual `ModuleStage` interpretation. Its object-aware instance uses one
static state containing field locals, object paths, witness storage, and the
allocation counter.

## Dialect-native path

The primary typed frontend now produces
`[Call, StructObject, Oracle, Felt, ConstrainEq]`. The default dialect backend
explicitly erases Oracle from the constraint projection, erases calls, then
erases StructObject and uses explicit structural
preservation/reflection certificates before the proved leaf-dialect
composition through the R1CSLike boundary. The final
adapter reuses the verified FlatIR-to-R1CS backend. StructObject has standalone
residual state semantics and a certified structural erasure with an explicit
object-state/encoded-target-state relation.

The typed source evaluator recognizes only structural `Call`; leaf operations
dispatch through independent StructObject, Oracle, Felt, and ConstrainEq
handlers over one static source state. Oracle exhaustion and division by zero
are named runtime/transport faults. StructObject owns finite slot seeding and
observable readback, the leaf pass owns SSA materialization, and the backend
owns inverse/is-zero auxiliaries.

`OracleErasure.checkAt_eq_checkProjectedAt` proves Oracle projection preserves
selected-entry checking. `ObjectCallSemantics.structuralPrefix_check_eq` and
`structuralPrefix_satisfies_iff` compose that result with successful hygienic
Call expansion. Recursive simulation preserves Boolean truth, defined field
locals, witness/cursor state, object aliases required by future statements, and
empty fresh storage. These are direct-semantics theorems, independent of
Call-erasure-defined elaboration semantics.

`StructObjectPass.lowerBody_simulation` proves direct object-aware and encoded
leaf observations equivalent under alias/path relation. Canonical specialization
`lowerBody_canonical_iff` uses finite input/object seed. `R1CSLikePass` proves
leaf materialization succeeds with satisfying FlatIR witness exactly for same
direct observation. `Pipeline.source_artifact_iff` composes these into exact
equivalence with Phase-13 `Source.satisfies` for certified lowering metadata.
Felt division validity is observed consistently: zero denominator is false in
direct constraint semantics and named materialization failure.

`EntryCompilationArtifact` exposes `forward`, `readback`, and the following
proved results without `sorry`:

- `checkSource_true_iff`: the executable source checker agrees with canonical
  source constraint satisfaction
- `pipeline_witness_iff`: every successful forward transport satisfies the
  source constraint observation iff it satisfies the artifact's exact R1CS
- `generated_witness_iff`: the same result specialized to a witness returned
  by modular source generation
- `pipeline_readback`: successful forward transport reads back exactly to the
  finite canonical source witness

`TypedEntryCompilationArtifact` additionally retains original typed module,
selected entry, Oracle projection, selected Call expansion, certified
StructObject erasure, exact leaf program, and backend artifact. It exposes:

- `typed_source_artifact_iff`: original typed-source satisfaction iff canonical
  artifact satisfaction
- `typed_source_check_eq_artifact`: direct and erased executable checkers agree
  for every canonical source witness
- `typed_source_r1cs_iff`: original typed-source satisfaction iff exact
  artifact R1CS satisfaction after successful forwarding
- `generated_typed_source_r1cs_iff`: generated-witness specialization
- `typed_pipeline_readback`: exact canonical finite readback

The witness CLI runs direct typed-source checker first and retains artifact
checker as a differential assertion before backend transport.

These constructive results supplement, rather than replace, the existential
`PresReflPass` and `StructuralPass` results. Parser/typing correctness and a
theorem that source generation always produces a satisfying candidate remain
separate concerns; unsatisfying candidates are intentionally representable.

## Legacy reference pipeline

```text
StructIR
  --[StructIRToFlatIR]--> FlatIR
  --[FlatIRCompact]------> FlatIR
  --[FlatIRToR1CS]------------> R1CS
```

## Per-stage status

### `StructIR -> FlatIR`

Files:

- `Heyting/Passes/StructIRToFlatIR.lean`
- `Heyting/Languages/StructIRFreshen.lean`

Status:

- executable lowering is quarantined under `Legacy.Pipeline` and used by the
  compatibility CLI path
- full `PresReflPass` (`CorrectPass`)
- source and target use original `StructIR.satisfies` / `FlatIR.satisfies` semantics
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

### `FlatIR -> R1CS`

File:

- `Heyting/Passes/FlatIRToR1CS.lean`

Status:

- full `PresReflPass`
- executable `compileWitness_preservation` and pointwise
  `compileWitness_satisfies_iff` for the exact constructed witness
- exact `extract_compileWitness` readback
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

### `FlatIR -> FlatIR(compact)`

File:

- `Heyting/Passes/FlatIRCompact.lean`

Status:

- full `PresReflPass`
- densely renames all used FlatIR variables to `0..k-1`
- used by the legacy reference pipeline before R1CS lowering
- shrinks sparse emitted wire spaces without changing satisfiability

## Pipeline status

Canonical import:

- `Heyting/Legacy/Pipeline.lean`

Status:

- declarations live under `Legacy.Pipeline`
- explicit `--legacy` CLI mode runs through this path
- full `PresReflPass` (`CorrectPass`)
- runtime path uses FlatIR compaction before R1CS lowering
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

## Witness generation

Both compiler paths interpret `@compute` bodies.

Status:

- the default dialect path uses `Dialect.WitnessExecution`, including typed
  oracle-stream state and nested calls
- `--oracle` supplies positional `llzk.nondet` values; exhaustion reports the
  typed `oracleUnderflow` runtime fault
- `--legacy` uses `Legacy.Pipeline.pipelineWitness`
- dialect candidate generation is separate from the proved source checker
- equality failure produces an unsatisfying transported candidate rather than
  a transport error; the CLI checker rejects it before serialization
- division by zero remains the leaf transport's explicit partial boundary
- the legacy executable generator still has no separate generator-soundness theorem

### Division validity

`Felt.backendValid` names the nonzero-divisor precondition imposed by FlatIR and
R1CS division. Total field evaluation still defines `x / 0 = 0`, so unconditional
end-to-end equivalence is not claimed for zero divisors. The executable dialect
witness boundary rejects them, and the R1CS encoding enforces nonzero through an
inverse constraint.

## Test coverage

Comprehensive test suite at `tests/` exercises all supported LLZK features:

| Feature | Test File | Coverage |
|---------|-----------|----------|
| Felt operations | `felt_ops.llzk` | `add`, `sub`, `mul`, `div`, `neg`, `inv`, `const` |
| Struct operations | `struct_ops.llzk` | `new`, `readm`, `writem` |
| Function calls | `function_call.llzk` | helper functions in `@compute`/`@constrain` |
| Constraint emission | `constrain_eq.llzk` | multiple `constrain.eq` statements |
| Nondeterministic witnesses | `nondet.llzk` | `llzk.nondet` |
| Multiple struct members | `multi_struct.llzk` | 8 members, objEnv tracking |
| Nested function calls | `nested_calls.llzk` | call chain depth 3 |
| Public members | `pub_members.llzk` | `llzk.pub` attribute |

Run: `./tests/run_tests.sh` or `./scripts/smoke_cli.sh`

All tests verify:
- Parser accepts LLZK input
- Both dialect and legacy compilers produce R1CS output
- Witness-capable fixtures produce witnesses accepted by `snarkjs` on both paths
- Smoke coverage validates a nonzero Oracle witness and division-by-zero rejection
