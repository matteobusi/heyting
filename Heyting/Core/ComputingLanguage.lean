import Heyting.Core.Language

/-!
# ComputingLanguage — Witness Generation Extension

This typeclass extends `Language` with a `computeWitness` function that,
given a program and public inputs, attempts to produce a satisfying witness.

## Design

`computeWitness` returns `Option (Witness V F)`:
- `some w` — the interpreter ran successfully and produced witness `w`
- `none`   — the interpreter encountered a runtime fault (e.g. division by zero)

Soundness of the interpreter (i.e. that if `computeWitness m inputs = some w`
then `w` satisfies `m`) is not bundled into the typeclass. It is stated as a
separate theorem for each instance, allowing instances to carry proof stubs
during development.

## Usage in the pipeline

If `computeWitness m inputs = some w`, then `w` is a candidate StructIR witness.
The full pipeline correctness (`Pipeline.compileWitnessCorrect`) then gives:
  `StructIR.satisfies w m →
   R1CS.satisfies (Pipeline.compileWitness m w) (Pipeline.compileProgram m)`

No new pass proofs are required — the witness generator is an entry point
into the existing `PresReflPass` chain, not a new pass.
-/

class ComputingLanguage (V : Type) (F : Type) [Field F] extends Language V F where
  /-- The type of public inputs to the witness generator. -/
  Input : Type

  /-- Attempt to compute a satisfying witness from public inputs.
      Returns `none` if the computation fails (e.g. division by zero). -/
  computeWitness : Program → Input → Option (Witness V F)
