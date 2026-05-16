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
  --[FlatIRToR1CS]------------> R1CS
```

## Per-stage status

### `StructIR -> FlatIR`

Files:

- `Heyting/Passes/StructIRToFlatIR.lean`
- `Heyting/Languages/StructIRFreshen.lean`

Status:

- executable lowering is active and used by CLI
- proved `ReflectingPass`
- source and target use original `StructIR.satisfies` / `FlatIR.satisfies` semantics
- not yet a completed `PresReflPass`

### `FlatIR -> R1CS`

File:

- `Heyting/Passes/FlatIRToR1CS.lean`

Status:

- full `PresReflPass`
- 0 sorries
- standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)

## Pipeline status

File:

- `Heyting/Passes/Pipeline.lean`

Status:

- executable composition of active path is active
- CLI and smoke tests run through this path
- proved `ReflectingPass`
- end-to-end `PresReflPass` is not yet available

## Witness generation

`StructIR.computeWitness` in `Heyting/Languages/StructIR.lean` computes witnesses by interpreting `@compute` bodies.

Status:

- executable witness generation is active
- used by `Pipeline.pipelineWitness` / CLI `--auto`
- separate correctness theorem for `computeWitness` is still future work
