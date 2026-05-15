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

## Usage in the executable pipeline

If `computeWitness m inputs = some w`, then `w` is a candidate StructIR witness.
Current executable path lifts that witness to FlatIR via `VarIdEncoding.decode`,
then to R1CS via `FlatIRToR1CS.compileWitness`.

Proof-carrying end-to-end witness correctness is not currently bundled here.
-/

class ComputingLanguage (V : Type) (F : Type) [Field F] extends Language V F where
  /-- The type of public inputs to the witness generator. -/
  Input : Type

  /-- Attempt to compute a satisfying witness from public inputs.
      Returns `none` if the computation fails (e.g. division by zero). -/
  computeWitness : Program → Input → Option (Witness V F)
