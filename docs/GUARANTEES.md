# Formal Guarantees

## Top-level statement

`Dialect.Pipeline.compiler_guarantee` (`Heyting/Guarantees.lean`) bundles, for every
successful compilation `c` of typed module `M` at entry `e`, the structure
`CompilerGuarantee M e c`:

| Field | Meaning |
|---|---|
| `statement_wires` | statement wires are distinct and the serializer places wire `i` at `i + 1` |
| `statement_fidelity` | statement wires carry the public part of the extracted source |
| `completeness` | `forward` maps every source instance `(x, w)` to an R1CS instance for `x` |
| `soundness` | every R1CS instance `(x, z)` extracts to the source instance `(x, readback z)` |
| `extractor_reindex` | the extractor reads fixed wires |
| `language` | `x` has a source witness iff it has an R1CS witness |
| `determinism` | for every key and observable, the source determines the observable from the key iff the R1CS does through `readback` |

`determinism` means that compilation adds and removes no under-constrained witness pairs;
`inputs_determine_objects_iff` is its wire form for "inputs determine every object slot".

Not covered: the parser and frontend, file bytes, cryptographic transfer to a proof system
(standard, not formalized), and equality of the compute executor with upstream LLZK compute.
Details follow.

## Guarantee boundary

Strong guarantee starts after successful AST lowering into typed
`Module [Call, StructObject, Oracle, Felt, ConstrainEq]` and selected-entry
compilation. Parser and AST-to-dialect lowering remain executable, partial, and
unverified.

For a certified compilation artifact `A` of typed module `M` and selected entry `e`:

```text
A.forward(w) = Ok z
  → (TypedSource.satisfies(M, e, w) ↔ R1CS.satisfies(A.target, z))
```

The target is the internal R1CS, before serialization. This is pointwise equivalence
for successfully transported witnesses, not yet a whole-entry `PresReflPass`.
It does not establish transport success for all satisfying source witnesses.
Separately, `typed_source_of_r1cs` proves unrestricted target reflection:
`R1CS.satisfies z A.target → TypedSource.satisfies (A.readback z) M`.
Reserved source slots are enforced as zero in the target. Conversely,
`typed_source_exists_r1cs` proves existential preservation, and `typed_source_forward_total`
proves the executable `forward` accepts every canonically sized satisfying source observation,
returning a satisfying R1CS witness that reads back to it. `typed_entry_correct` bundles both
directions as `EntryCorrect`; `typed_source_iff_exists_r1cs` states the resulting equivalence.
The layout invariant `computeParams ≤ numParams` is checked by `lowerEntryCertified`.
Source witnesses come from the compute executor; see [Witness generation](#witness-generation)
and [AUDIT.md](AUDIT.md).

## Statement-indexed guarantee (Levin reduction)

`entryLevinReduction` is a Levin reduction (`Core/Levin.lean`) from the source relation
`SourceRelation M e A x w` (canonical shape, typed-source satisfaction, and public part of
`w` equal to `x`) to `R1CS.Relation A.target x z` (satisfaction, and statement wires of `z`
equal to `x`). The statement map is the identity; the prover map is `forward`; the extractor
is `readback`, a reindexing of target wires (`readback_inputs`, `readback_objects`).
`statement_readback` proves the target statement wires carry exactly the source public
outputs (public felt members of the entry) followed by the public inputs (`{llzk.pub}`
compute parameters). `typed_entry_levin` gives the language equivalence.

`WireAssignment` proves the serializer places the statement wires at wires `1..k` in order
(`encode_statement`, `decode_statement`) and assigns distinct wires (`layout_nodup`). Hence a
proof system for the emitted R1CS sees as public exactly the source statement. The transfer
of knowledge soundness and zero knowledge through the reduction is standard but not
formalized.

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
  → R1CSLike → R1CS
```

### Oracle and Call prefix

`OracleErasure.directConstraintPass` and `ObjectCallSemantics.directConstraintPass`
use independent source/projected/residual semantics with the same finite observation.
`ObjectCallSemantics.directPrefixPass` composes their existential preservation/reflection,
conditional on successful module lowering. This module-level theorem does not replace
the CLI's selected-entry artifact. The subsequent object-layout boundary uses
`StructObjectPass.CanonicalStateRel`: finite observations agree with an initial leaf
environment on allocated slots, with other locals unrestricted. `lowerFunc_related_iff`
proves direct satisfaction equivalence; `source_target_related_materialize_iff` joins
it to leaf materialization. The existing artifact proof uses its canonical specialization.
The whole-entry `typed_source_of_r1cs` combines related-state reflection with finite
readback and enforced reserved-slot zeros to cover arbitrary satisfying target witnesses.

- `OracleErasure.checkAt_eq_checkProjectedAt`: projection preserves selected-entry checking.
- `ObjectCallSemantics.structuralPrefix_check_eq`: direct checker correspondence.
- `ObjectCallSemantics.structuralPrefix_satisfies_iff`: source satisfaction iff successful
  Oracle projection plus hygienic Call expansion.

Call simulation preserves Boolean truth, field locals, witness/Oracle state,
needed object aliases, and allocation freshness.

### StructObject and leaf boundary

- `StructObjectPass.lowerBody_simulation`: object-aware and encoded leaf execution agree.
- `StructObjectPass.lowerBody_canonical_iff`: canonical finite source specialization.
- `StructObjectPass.lowerFunc_canonical_iff`: exact certified target-body specialization.
- `R1CSLikePass`: leaf operations materialize into exact terminal dialect semantics.
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

These constructive pointwise results use standard axioms only. The generic structural
wrappers use lowering-defined predicates; direct Oracle/Call wrappers additionally expose
independent semantics. The complete chain of existential pass correctness with matching
direct-source and terminal witness semantics is not yet packaged.

### Direct terminal backend

`R1CSLike.CorrectPass` provides full direct `PresReflPass`: preservation uses
constructed wires; reflection reads back any satisfying R1CS assignment.
`compileWitness_satisfies_iff` additionally proves pointwise equivalence for
the exact generated wire assignment. Constructive codec supplies exact readback.
Division retains two constraints enforcing quotient and nonzero denominator;
inverse retains three constraints including the zero-input case.

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

Unsatisfying candidate remains representable and checker rejects it. The executor
is the operational semantics of compute; it is not proved equal to upstream LLZK compute.
Proved about the prover `proveEntry` (steps 1–4, `Heyting/Guarantees.lean`):

- `proveEntry_sound`: a returned witness is an R1CS instance for the public part of a
  generated observation that satisfies the typed-source semantics and records the inputs.
- `proveEntry_complete`: with one value per compute parameter, a fully read oracle, and a
  generated observation that satisfies the constraints, the prover succeeds. That the
  compute output satisfies the constraints is a property of the source program, so it is a
  hypothesis.
- `WitnessExecution.genWitness_fault`: when every compute call uses selector `0`
  (`SelectorsSupported`, decided by `checkSelectors`), generation fails only with
  `oracleUnderflow` or `divisionByZero`.
- `StructObject.read_through_writeObject`: after `writeObject`, reading the member and then a
  field of the sub-component gives the stored sub-component's value (the access pattern of
  `@constrain`).

## Trust and audit

- proof files: zero sorries
- major proof axioms: `propext`, `Classical.choice`, `Quot.sound` only
- CLI field primality: isolated `private axiom`, absent from pass theorems
- serializers and snarkjs validation: executable integration, not kernel theorem

## Test coverage

`tests/adversarial_full.llzk` covers nested compute/constrain calls, objects,
public members, two Oracle reads, every supported Felt operation, and multiple
equalities. Correct witness passes snarkjs; altered Oracle fails typed-source
checking. Smoke also checks Oracle exhaustion, division by zero, input/field boundaries,
JSON/binary output, the Groth16 public statement, and the full fixture suite.
