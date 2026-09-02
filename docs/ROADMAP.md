# Roadmap

## Current state

Dialect migration phases 0–14 completed. Phase 15 extracted retired StructIR
implementation to branch `legacy-infrastructure`. Active branch contains one
compiler path:

```text
LLZK AST
  → typed dialect module
  → Oracle → Call → StructObject erasure
  → Felt/ConstrainEq → R1CSLike → FlatIR → R1CS
```

Whole typed-entry artifact composes local correctness and proves
typed-source/R1CS satisfaction equivalence after successful lowering and
witness transport.

## Priority 1 — verified frontend boundary

Current text parser and AST-to-dialect lowering are unverified. Define useful
correctness without inventing `AST.satisfies`:

1. define canonical typed pretty-printer or `unlower`
2. state structural round-trip modulo normalization/name resolution
3. prove AST analysis preserves declarations, dependency order, and SSA naming
4. add translation validation while full proof matures
5. ensure skipped operations never cross typed boundary silently

## Priority 2 — witness-generation soundness

Current theorem is pointwise: generated candidate satisfies source iff its
transport satisfies R1CS. Add explicit source-side preconditions and prove:

```text
validInputs program inputs oracle
  → TypedSource.satisfies (genWitness program inputs oracle) program
```

Compose with `generated_typed_source_r1cs_iff`. Keep unsatisfying candidates
observable for negative testing.

## Priority 3 — callable model

Typed module exposes one `compute` and one `constrain` per struct; selector `0`
only; calls target earlier topological structs. Extend to named callable space:

- same-struct helpers
- free functions
- explicit selector typing and arity proofs
- recursion policy separate from lookup

Preserve residual-polymorphic Call erasure and local simulation.

## Priority 4 — LLZK dialect coverage

1. static arrays and scalarization
2. booleans and `constrain.in`
3. casts
4. non-native Felt operations such as power/bit decomposition
5. globals and constant inlining
6. bounded control flow and monomorphization

Each needs syntax, typed lowering, source handler, erasure/lowering, local
correctness certificate, pipeline composition, and adversarial fixture.

## Priority 5 — optimization and backends

- verified optimizations with constructive codecs
- public/private wire classification in serializers
- reusable constraint dialect above backend specializations
- Plonkish backend after constraint semantics stabilizes
- proof/build performance profiling as dialect count grows

## Research/paper milestones

1. stabilize verified frontend statement
2. publish theorem dependency diagram and axiom audit
3. add nontrivial benchmark: Poseidon round, IsZero/range gadget, or Merkle step
4. compare with Clap-lean and ACL2 gadget verification
5. send design/paper draft to project-llzk for feedback

## Completed migration history

See `docs/dialect-migration-plan.md`. Phase-14 checkpoint is commit `b608671`;
same commit anchors `legacy-infrastructure` branch before active removal.
