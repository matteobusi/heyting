# Formal Guarantees

Current proof status for active compiler path.

## Framework

Passes target `PresReflPass S T` from `Heyting/Core/Pass.lean`.

- `compile`: source program -> target program
- `witnessRel`: relation between source and target witnesses
- `reflection`: target sat -> related source sat
- `preservation`: source sat -> related target sat

When both directions exist, source and target are equisatisfiable.

## Active executable pipeline

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

- executable lowering is active and used by CLI
- full `PresReflPass` (`CorrectPass`)
- source and target use original `StructIR.satisfies` / `FlatIR.satisfies` semantics
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

### `FlatIR -> R1CS`

File:

- `Heyting/Passes/FlatIRToR1CS.lean`

Status:

- full `PresReflPass`
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

### `FlatIR -> FlatIR(compact)`

File:

- `Heyting/Passes/FlatIRCompact.lean`

Status:

- full `PresReflPass`
- densely renames all used FlatIR variables to `0..k-1`
- used by active executable pipeline before R1CS lowering
- shrinks sparse emitted wire spaces without changing satisfiability

## Pipeline status

File:

- `Heyting/Passes/Pipeline.lean`

Status:

- executable composition of active path is active
- CLI and smoke tests run through this path
- full `PresReflPass` (`CorrectPass`)
- runtime path uses FlatIR compaction before R1CS lowering
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

## Witness generation

`StructIR.computeWitness` in `Heyting/Languages/StructIR.lean` computes witnesses by
interpreting `@compute` bodies.

Status:

- executable witness generation is active
- used by `Pipeline.pipelineWitness` / CLI `--auto`
- separate correctness theorem for `computeWitness` is still future work

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
- Compiler produces R1CS output
- Optional: `snarkjs` validates constraint system structure
