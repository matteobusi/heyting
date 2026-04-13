---
title: Hey CLI
---

## Overview

The Heyting compiler provides a small command-line interface via the `hey` executable. The CLI is deliberately minimal while the project evolves. The main command is `compile`, which emits an R1CS JSON file from an LLZK input.

## Usage

```
hey compile [options] <input.llzk> <output>
hey help
```

## Options

- `--json`
  Produce a human-readable R1CS JSON file (default behavior of `compile`).

- `--prime-field <name>`
  Select the prime field for arithmetic. Supported values:

  | Name | Prime | Used by |
  |------|-------|---------|
  | `bn254` *(default)* | 21888242871839275222246405745257275088696311157297823662689037894645226208583 | circom |
  | `bn128` | same as bn254 (alias) | circom |
  | `babybear` | 2013265921 (15 · 2²⁷ + 1) | zirgen |
  | `goldilocks` | 18446744069414584321 (2⁶⁴ − 2³² + 1) | plonky2 |
  | `mersenne31` | 2147483647 (2³¹ − 1) | Plonky3 |
  | `koalabear` | 2130706433 (2³¹ − 2²⁴ + 1) | Plonky3 |

  These match the 6 fields in `llzk-lib/lib/Util/Field.cpp`. If `--prime-field` is omitted, `bn254` is used.

- `--input <path>`
  JSON file of public circuit inputs (field elements) to pass to the circuit's `@compute`
  bodies. Not yet implemented — passing this option raises an informative error. The planned
  format is a JSON array of field element values (as decimal strings), one per positional
  parameter of the top-level `@compute` function.

- `--auto`
  Automatically run compute bodies to produce a witness, using empty public inputs.
  Writes `<output>.witness.json` alongside the R1CS file.

- `--output <path>`
  Alternative way to specify the output path (useful when paths contain spaces or when scripting).

## Examples

```bash
# Default field (bn254, matches circom)
lake exe hey compile emit_pass.llzk out/system.json

# Explicit field
lake exe hey compile --prime-field babybear circuit.llzk out/system.json
lake exe hey compile --prime-field goldilocks circuit.llzk out/system.json
lake exe hey compile --prime-field mersenne31 circuit.llzk out/system.json
```

## Field selection and correctness

All compiler passes and verified theorems are **generic over `F : Type [Field F]`** — the
correctness proofs hold for any field. The `--prime-field` flag selects the field at the
CLI boundary only; no proof-bearing code is parameterized on a specific prime.

The primality facts for `bn254`/`bn128` and `goldilocks` are declared via `private axiom`
in `Heyting/CLI.lean` — they cannot be verified by `native_decide` or `norm_num` (primes
are too large / not Mersenne-form for norm_num). These axioms are CLI-only and never appear
in any `PresReflPass` proof. See `docs/WARNING.md` §7 for the full axiom policy.

## Notes on features not yet implemented

- `--input <path>` will load public circuit inputs from a JSON array of decimal field element
  strings and pass them to `StructIR.computeWitness`. Until then, `--auto` runs with an empty
  input list (works for circuits with no public parameters).

- User-supplied witness loading (i.e. providing a pre-computed witness directly, bypassing
  `@compute` bodies) is not currently exposed via any flag.

## Where to find the CLI code

```
Heyting/CLI.lean       -- compileToJson, runCommand, main
Heyting/CLIArgs.lean   -- argument parsing (Options, parse)
```
