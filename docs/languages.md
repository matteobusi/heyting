# Languages in Heyting

The dialect-native architecture is the primary migration target:

```text
parser AST
  ---> Module [Call, StructObject, Oracle, Felt, ConstrainEq]
  ---> Oracle erasure (constraint projection)
  ---> Module [Call, StructObject, Felt, ConstrainEq]
  ---> call erasure
  ---> Module [StructObject, Felt, ConstrainEq]
  ---> StructObject erasure
  ---> Module [Felt, ConstrainEq]
  ---> [R1CSLike]
  ---> FlatIR/R1CS backend adapter
```

It is the default executable `hey compile` pipeline. The quarantined reference
pipeline remains available through `--legacy`:

```text
StructIR  --->  FlatIR  --->  FlatIR(compact)  --->  R1CS
```

The dialect path compiles Felt operations, equality constraints, typed calls,
objects, and nondeterministic witness reads. `--auto` and `--input` execute the
typed compute module; `--oracle` supplies the positional Oracle stream. Skipped
parser operations remain rejected at the typed frontend boundary. The reference
composition is available as `Legacy.Pipeline` through
`Heyting.Legacy.Pipeline`.

## Oracle dialect

Files:

- `Heyting/Dialects/Oracle.lean`
- `Heyting/Dialects/OracleErasure.lean`
- `Heyting/Dialects/WitnessExecution.lean`

`Oracle.next` is witness-only syntax for `llzk.nondet`. Its runtime state is a
typed list plus cursor, threaded through nested calls. Source execution reports
`oracleUnderflow` when the stream is exhausted. Constraint compilation
explicitly projects Oracle away before Call erasure; compute execution uses the
un-erased module.

## Structural-prefix correspondence

File: `Heyting/Dialects/ObjectCallSemantics.lean`

Certified constraint bodies contain no Oracle operation, so Oracle projection
preserves direct selected-entry execution. Successful hygienic Call expansion
then preserves direct object-aware truth plus field, witness-cursor, and object
freshness invariants. `PrefixCertificate` composes both steps, and
`structuralPrefix_satisfies_iff` proves equivalence between original typed-source
satisfaction and call-free `[StructObject, Felt, ConstrainEq]` satisfaction.

## Constructive witness artifacts

Files:

- `Heyting/Core/WitnessSemantics.lean`
- `Heyting/Core/WitnessCodec.lean`
- `Heyting/Passes/FlatIRWitnessCodec.lean`
- `Heyting/Passes/DialectPipeline.lean`

Source compute execution dispatches leaf operations through per-dialect
handlers. It projects transient state to `SourceWitness`, containing finite
input and reachable-object coordinates. `TypedEntryCompilationArtifact`
retains original typed module plus Oracle, Call, StructObject, leaf, and backend
certificates. Its `EntryCompilationArtifact.forward` applies pass-owned object
layout, leaf materialization, and backend auxiliary construction. Direct and
artifact checkers agree on canonical witnesses; original typed-source/R1CS
satisfaction iff and exact canonical readback are proved.

## Core abstractions

All languages and passes are generic over `F : Type [Field F]`.

### `Language`

`Language` pairs:

- program syntax
- witness type
- satisfaction relation `w |= p`

### `Pass` / `PresReflPass`

`Pass` gives `compile` and `witnessRel`.

`PresReflPass` adds:

- preservation: source sat -> related target sat
- reflection: target sat -> related source sat

### Structural module stages

File: `Heyting/Core/StructuralPass.lean`

`ModuleStage Δ n F` gives a module stage one statically known semantic state
type. `StructuralPass` is an explicit partial transformation between two such
stages, with a source/target-module-indexed state relation and conditional
preservation/reflection.

`EraseDialect removed residual` specializes this to canonical head erasure:

```text
Module (removed :: residual) → Module residual
```

Structural pass selection and ordering are explicit. There is no runtime
effect registry or heterogeneous state list. Witness-backed stages bridge to
the existing `Language`/`PresReflPass` framework, so total structural passes
compose with established leaf and backend proofs.

## StructIR

File: `Heyting/Languages/StructIR.lean`

Highest-level IR.

- hierarchical structs
- `readMember`
- cross-struct `call`
- intrinsic well-formedness via dependent types
- witness indexed by `VarId = InstancePath × Nat`

Key semantic channels:

- value channel: local arithmetic environment
- object-path channel: `ObjEnv` for nested member reads and calls

## FlatIR

File: `Heyting/Languages/FlatIR.lean`

Flat instruction list over `Nat` variable IDs.

Instructions:

- `assignAdd`
- `assignSub`
- `assignMul`
- `assignDiv`
- `assignNeg`
- `assignConst`
- `assertEq`

No calls, no struct hierarchy.

## R1CS

File: `Heyting/Languages/R1CS.lean`

Rank-1 Constraint Systems.

- constraints have shape `A * B = C`
- variable IDs are `varOne | var n | aux n`
- target of fully verified `FlatIR -> R1CS` pass

## R1CSLike dialect

Files:

- `Heyting/Dialects/R1CSLike.lean`
- `Heyting/Dialects/R1CSLikePass.lean`

The dialect-native, call-free instruction boundary above the existing backend.
Arithmetic assignments and equality assertions map directly to `FlatIR.Instr`.
The `[Felt, ConstrainEq] -> [R1CSLike]` module pass preserves constraint
semantics and well-formedness. The FlatIR/R1CS division backend has a
nonzero-divisor precondition, named by `Felt.backendValid`. Dialect witness
execution rejects zero divisors rather than emitting an invalid backend witness.
Equality assertions do not make transport partial; they remain observable to
the proved source checker.

## StructObject dialect

File: `Heyting/Dialects/StructObject.lean`

Typed source operations:

- object allocation (`newStruct`)
- typed member reads (`readMember` with `Fin numMembers`)
- typed member writes (`writeMember` with `Fin numMembers`)

The dialect provides executable state semantics over field locals, object
paths, witness storage, and fresh paths. `ObjectResidualSemantics.lean`
interprets the call-free `[StructObject, Felt, ConstrainEq]` stage with that
single static state and supplies the target of the certified object-aware Call
erasure. `StructObjectPass.lean` then lowers member reads to an injectively
encoded witness-local range, shifts ordinary non-parameter SSA locals above
that range, and removes object syntax before the leaf/backend passes. Object
paths are never encoded as field values.

## FlatIR compaction pass

File: `Heyting/Passes/FlatIRCompact.lean`

This is not a new user-facing language. It is a semantics-preserving FlatIR to
FlatIR renaming pass that:

- collects all used FlatIR variables
- assigns them dense IDs `0 .. k - 1` in first-occurrence order
- preserves satisfiability via a proved `PresReflPass`
- reduces emitted R1CS wire counts when upstream FlatIR variable IDs are sparse

The legacy reference pipeline uses this pass before `FlatIR -> R1CS` lowering.

## Helper semantic layers

These are proof-support files, not separate user-facing IRs in active compiler pipeline.

### StructIR freshening support

Files:

- `Heyting/Core/SubstSemantics.lean`
- `Heyting/Languages/StructIRFreshen.lean`

Purpose:

- freshening and renaming support for constrain bodies
- environment-agreement lemmas used by `StructIR -> FlatIR` full correctness proof

### Active pass proof file

Files:

- `Heyting/Passes/StructIRToFlatIR.lean`

Purpose:

- executable `StructIR -> FlatIR` lowering
- direct `PresReflPass` proof for `StructIR -> FlatIR`

## Historical note

Older docs may mention `StructInlineIR` and `MemberlessIR`. Those intermediate
languages are not part of either current executable pipeline.
