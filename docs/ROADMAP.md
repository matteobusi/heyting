# Roadmap

## Current state

One compiler path:

```text
LLZK AST
  → typed dialect module
  → Oracle → Call → StructObject erasure
  → Felt/ConstrainEq → R1CSLike → R1CS
```

Proved: whole-entry preservation and reflection (`typed_entry_correct`), the Levin reduction
with verified public statement wires (`entryLevinReduction`), determinism preservation, prover
soundness and conditional completeness, all bundled in `compiler_guarantee`. See
[GUARANTEES.md](GUARANTEES.md) and [AUDIT.md](AUDIT.md).

## Priority 0 — packaging

Optionally repackage `EntryCorrect` as a `PresReflPass` instance (needs a source `Language`
for finite observations and total or option-valued compilation).

## Priority 1 — verified frontend boundary

Current text parser and AST-to-dialect lowering are unverified. Define useful
correctness without inventing `AST.satisfies`:

1. define canonical typed pretty-printer or `unlower`
2. state structural round-trip modulo normalization/name resolution
3. prove AST analysis preserves declarations, dependency order, and SSA naming
4. add translation validation while full proof matures

The parser rejects unsupported input and the frontend type-checks member access (tested in
`tests/Frontend.lean`); this is executable strictness, not a proof.

Compute and constrain share the tree object model (`writeObject`, `read_through_writeObject`).

## Priority 2 — compute semantics

Done: prover soundness and conditional completeness (`proveEntry_sound`,
`proveEntry_complete`), data-only faults (`genWitness_fault`), determinism preservation
(`determines_iff`). Open:

1. differential testing of `WitnessExecution` against an upstream LLZK compute interpreter;
2. a verified analysis that proves, for a class of programs, that compute output satisfies
   the constraints (for example, compute and constrain derived from one source);
3. a decision procedure or analysis for source determinism (under-constrained circuits).

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
- reusable constraint dialect above backend specializations
- Plonkish backend after constraint semantics stabilizes
- proof/build performance profiling as dialect count grows

## Research/paper milestones

1. stabilize verified frontend statement
2. publish theorem dependency diagram and axiom audit
3. add nontrivial benchmark: Poseidon round, IsZero/range gadget, or Merkle step
4. compare with Clap-lean and ACL2 gadget verification
5. send design/paper draft to project-llzk for feedback
