# Formal Guarantees

## Guarantee boundary

Strong guarantee starts after successful AST lowering into typed
`Module [Call, StructObject, Oracle, Felt, ConstrainEq]` and selected-entry
compilation. Parser and AST-to-dialect lowering remain executable, partial, and
unverified.

For successful compilation and witness forwarding, whole-entry theorem relates
original typed source semantics to exact emitted R1CS. No constraint is added
or lost relative to that typed source observation.

## Framework

`PresReflPass S T` contains program translation, program-indexed witness
relation, preservation, and reflection. `PresReflPass.compose` lifts local
proofs through intermediate witnesses.

`StructuralPass` handles partial dialect erasures that change static semantic
state. Laws are conditional on lowering returning exact target. Explicit
composition preserves certificates; total witness-backed stages bridge to
`PresReflPass`.

## Active path

```text
typed [Call, StructObject, Oracle, Felt, ConstrainEq]
  → Oracle projection
  → [Call, StructObject, Felt, ConstrainEq]
  → Call erasure
  → [StructObject, Felt, ConstrainEq]
  → StructObject erasure
  → [Felt, ConstrainEq]
  → R1CSLike → FlatIR → R1CS
```

### Oracle and Call prefix

- `OracleErasure.checkAt_eq_checkProjectedAt`: projection preserves selected-entry checking.
- `ObjectCallSemantics.structuralPrefix_check_eq`: direct checker correspondence.
- `ObjectCallSemantics.structuralPrefix_satisfies_iff`: source satisfaction iff successful
  Oracle projection plus hygienic Call expansion.

Call simulation preserves Boolean truth, field locals, witness/Oracle state,
needed object aliases, and allocation freshness.

### StructObject and leaf boundary

- `StructObjectPass.lowerBody_simulation`: object-aware and encoded leaf execution agree.
- `StructObjectPass.lowerBody_canonical_iff`: canonical finite source specialization.
- `R1CSLikePass`: leaf operations materialize into exact FlatIR semantics.
- `Pipeline.source_artifact_iff`: certified source artifact satisfaction equivalence.

Object paths remain compile-time identities. Only `(path, member)` witness
coordinates receive injective natural-number slots.

### Whole-entry artifact

`TypedEntryCompilationArtifact` retains original typed module, selected entry,
Oracle projection equation, Call expansion/certification, StructObject erasure,
leaf program, forward/readback codec, and exact R1CS target.

Major results:

- `typed_source_artifact_iff`: original typed-source satisfaction iff canonical artifact satisfaction
- `typed_source_check_eq_artifact`: direct and erased checkers agree on canonical witnesses
- `typed_source_r1cs_iff`: typed-source satisfaction iff exact R1CS satisfaction after forwarding
- `generated_typed_source_r1cs_iff`: specialization to generated candidate
- `typed_pipeline_readback`: forwarding reads back exact canonical finite source witness

These constructive pointwise results supplement existential pass correctness
and use standard axioms only.

### FlatIR backend

`Heyting/Passes/FlatIRToR1CS.lean` provides full `PresReflPass`, exact witness
construction/readback, and two-constraint nonzero division encoding.

## Witness generation

`Dialect.WitnessExecution` interprets full typed compute module using handlers
for StructObject, Oracle, Felt, and ConstrainEq plus structural Call recursion.
Transient state projects to finite canonical source witness.

CLI sequence:

1. execute source compute body
2. run direct typed-source constraint checker
3. run erased artifact checker as differential assertion
4. forward witness through artifact codec
5. serialize exact R1CS/witness pair

Unsatisfying candidate remains representable and checker rejects it. No theorem
yet states every generated candidate satisfies source program. Division by zero
and Oracle exhaustion are explicit runtime/transport faults.

## Trust and audit

- proof files: zero sorries
- major proof axioms: `propext`, `Classical.choice`, `Quot.sound` only
- CLI field primality: isolated `private axiom`, absent from pass theorems
- serializers and snarkjs validation: executable integration, not kernel theorem

## Test coverage

`tests/adversarial_full.llzk` covers nested compute/constrain calls, objects,
public members, two Oracle reads, every supported Felt operation, and multiple
equalities. Correct witness passes snarkjs; altered Oracle fails typed-source
checking. Smoke also checks Oracle exhaustion, division by zero, retired
selector rejection, JSON/binary output, and full fixture suite.

## Archived implementation

Old StructIR pipeline and proofs are preserved on branch
`legacy-infrastructure`. They are not compiled, imported, or exposed by active
CLI, and make no contribution to active guarantee statement.
