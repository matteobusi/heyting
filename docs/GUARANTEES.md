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
  --[StructIRToFlatIRDirect]--> FlatIR
  --[FlatIRToR1CS]------------> R1CS
```

## Per-stage status

### `StructIR -> FlatIR`

Files:

- `Heyting/Passes/StructIRToFlatIRDirect.lean`
- `Heyting/Passes/StructIRToFlatIRDirectSim.lean`
- `Heyting/Passes/StructIRToFlatIRDirectCorrectness.lean`
- `Heyting/Languages/StructIRSubst.lean`
- `Heyting/Languages/FlatIRSubst.lean`

Status:

- executable lowering is active and used by CLI
- checked-simulation / reflection scaffold restored
- not yet a completed active `PresReflPass`
- current live proof gaps are concentrated in substitution/correctness scaffold files

Current remaining proof gaps:

- `Heyting/Languages/StructIRSubst.lean`
  - `evalConstrainBody_env_agree_on_init`
  - `evalConstrainBody_objEnv_agree_on_init`
- `Heyting/Passes/StructIRToFlatIRDirectCorrectness.lean`
  - `evalConstrainBody_env_agree_on_init`
  - `CorrectReflectingPass.reflection`

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

- executable composition of direct path is active
- CLI and smoke tests run through this path
- end-to-end `PresReflPass` for direct path is not yet bundled in active build

## Witness generation

`StructIR.computeWitness` in `Heyting/Languages/StructIR.lean` computes witnesses by interpreting `@compute` bodies.

Status:

- executable witness generation is active
- used by `Pipeline.pipelineWitness` / CLI `--auto`
- separate correctness theorem for `computeWitness` is still future work
