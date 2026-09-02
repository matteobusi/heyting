# Languages and Stages

## Pipeline

```text
LLZK text
  → AST
  → Module [Call, StructObject, Oracle, Felt, ConstrainEq]
  → Module [Call, StructObject, Felt, ConstrainEq]
  → Module [StructObject, Felt, ConstrainEq]
  → Module [Felt, ConstrainEq]
  → R1CSLike → FlatIR → R1CS
```

Proof-bearing languages and passes are generic over `F : Type [Field F]`.

## Untyped LLZK AST

Files: `Heyting/Parsers/AST.lean`, `ASTAnalysis.lean`, `Parser.lean`.

Parser keeps source names, positions, unsupported markers. AST analysis sorts
struct dependencies and assigns SSA indices. Boundary not yet verified.

## Typed dialect module

File: `Heyting/Core/Dialect.lean`.

`OpSig` packages context-indexed operation syntax plus destination, reads,
renaming, capability metadata. `Stmt Δ γ F` is finite dialect sum.
`FuncDef` carries intrinsic capability and SSA proofs. `Module Δ n F` indexes
structs and calls using finite topological indices.

## Oracle

Files: `Oracle.lean`, `OracleErasure.lean`, `WitnessExecution.lean`.

`Oracle.next` is compute-only nondeterministic input. Source execution threads
typed stream/cursor. Constraint projection removes Oracle before structural
lowering. Exhaustion is explicit runtime fault.

## Call

Files: `Call.lean`, `CallErasure.lean`, `ObjectCallSemantics.lean`.

Call is structural head dialect. Erasure recursively inlines topologically
decreasing calls, renames locals hygienically, binds returns, and is polymorphic
over residual syntax. Object-aware protocol transports field locals and object
aliases while threading witness/allocation state.

## StructObject

Files: `StructObject.lean`, `ObjectResidualSemantics.lean`,
`StructObjectPass.lean`.

State contains field locals, object paths, witness store, next allocation.
Erasure executes paths statically, maps observable `(path, member)` coordinates
to injective slots, and shifts ordinary SSA locals outside witness range. Object
paths never become field values.

## Felt and ConstrainEq

Files: `Felt.lean`, `ConstrainEq.lean`, `R1CSLikePass.lean`.

Felt supplies arithmetic assignments. ConstrainEq supplies Boolean equality
observation. Leaf materialization builds exact FlatIR program and witness locals.
Zero-divisor backend validity is explicit.

## R1CSLike

Files: `R1CSLike.lean`, `R1CSLikePass.lean`.

Call/object-free constraint dialect mirrors backend instructions. It isolates
dialect semantics from FlatIR representation and supports pass-local proof.

## FlatIR

File: `Heyting/Languages/FlatIR.lean`.

Flat instructions over natural variable IDs: add, sub, mul, div, neg, const,
assert equality. No calls, objects, or Oracle.

## R1CS

Files: `Heyting/Languages/R1CS.lean`, `Heyting/Passes/FlatIRToR1CS.lean`.

Constraints have `A * B = C`. Variable IDs distinguish constant one, ordinary
wires, auxiliaries. Backend is full `PresReflPass`; division emits relation plus
inverse/nonzero constraint.

## Source witness and artifact

Files: `WitnessSemantics.lean`, `WitnessCodec.lean`,
`FlatIRWitnessCodec.lean`, `DialectPipeline.lean`.

Compute execution projects transient state to finite source witness containing
inputs and reachable object coordinates. `TypedEntryCompilationArtifact`
retains every structural certificate and exact target. Codec performs forward
materialization and exact readback.

## Retired languages

StructIR pipeline is preserved only on Git branch `legacy-infrastructure`.
Active modules must not import it.
