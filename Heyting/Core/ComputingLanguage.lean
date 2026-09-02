/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

## Usage

This generic interface does not prescribe source dialect state or witness
transport. Active pipeline uses modular source execution plus explicit
`WitnessCodec`; proof-carrying correctness remains external to this class.
-/

class ComputingLanguage (V : Type) (F : Type) [Field F] extends Language V F where
  /-- The type of public inputs to the witness generator. -/
  Input : Type

  /-- Attempt to compute a satisfying witness from public inputs.
      Returns `none` if the computation fails (e.g. division by zero). -/
  computeWitness : Program → Input → Option (Witness V F)
