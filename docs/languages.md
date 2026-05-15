# Languages in Heyting

Current active pipeline:

```text
StructIR  --->  FlatIR  --->  R1CS
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

## Helper semantic layers

These are proof-support files, not separate user-facing IRs in active compiler pipeline.

### StructIR substitution semantics

Files:

- `Heyting/Core/SubstSemantics.lean`
- `Heyting/Languages/StructIRSubst.lean`

Purpose:

- symbolic / substitution-style account of StructIR evaluation
- bridge between executable semantics and direct reflection proof

### FlatIR substitution semantics

File:

- `Heyting/Languages/FlatIRSubst.lean`

Purpose:

- atom-level checked semantics used by direct simulation / reflection scaffolding

### Direct proof scaffold

Files:

- `Heyting/Passes/StructIRToFlatIRDirectSim.lean`
- `Heyting/Passes/StructIRToFlatIRDirectCorrectness.lean`

Purpose:

- checked-semantics simulation lemmas
- direct `ReflectingPass` scaffold for `StructIR -> FlatIR`

## Historical note

Older docs may mention `StructInlineIR` and `MemberlessIR`. Those intermediate languages are not part of current active executable pipeline.
