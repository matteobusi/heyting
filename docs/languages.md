# Languages in Heyting

Current active pipeline:

```text
StructIR  --->  FlatIR  --->  FlatIR(compact)  --->  R1CS
```

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

## FlatIR compaction pass

File: `Heyting/Passes/FlatIRCompact.lean`

This is not a new user-facing language. It is a semantics-preserving FlatIR to
FlatIR renaming pass that:

- collects all used FlatIR variables
- assigns them dense IDs `0 .. k - 1` in first-occurrence order
- preserves satisfiability via a proved `PresReflPass`
- reduces emitted R1CS wire counts when upstream FlatIR variable IDs are sparse

Active pipeline uses this pass before `FlatIR -> R1CS` lowering.

## Helper semantic layers

These are proof-support files, not separate user-facing IRs in active compiler pipeline.

### StructIR freshening support

Files:

- `Heyting/Core/SubstSemantics.lean`
- `Heyting/Languages/StructIRFreshen.lean`

Purpose:

- freshening and renaming support for constrain bodies
- environment-agreement lemmas used by `StructIR -> FlatIR` reflection proof

### Active pass proof file

Files:

- `Heyting/Passes/StructIRToFlatIR.lean`

Purpose:

- executable `StructIR -> FlatIR` lowering
- direct `ReflectingPass` proof for `StructIR -> FlatIR`

## Historical note

Older docs may mention `StructInlineIR` and `MemberlessIR`. Those intermediate languages are not part of current active executable pipeline.
