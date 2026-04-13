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

- `--witness <path>`
  Use a user-supplied witness JSON file to populate StructIR witness values. (Not implemented yet — passing this option will raise an informative error.)

- `--auto`
  Automatically run compute bodies to produce a witness from the program's `compute` functions. (Not implemented yet — this is planned and passing the flag will raise an informative error.)

- `--input <path>` / `--output <path>`
  Alternative ways to specify input file and output path (useful when paths contain spaces or when scripting).

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

- Witness generation from compute bodies (`--auto`) is a staged feature. The project will
  implement a pure Lean interpreter for StructIR compute bodies first (so proofs can be
  added later), followed by an optional native codegen path for performance. Until then,
  `--auto` raises an explanatory error.

- User-supplied witness loading (`--witness`) will accept a JSON array of entries in the
  form `{ "path": [ints], "member": int, "value": "repr" }`. The `value` field uses the
  same stringified field representation as the R1CS JSON output. Until implemented, the
  CLI raises an explanatory error when `--witness` is used.

## Where to find the CLI code

```
Heyting/CLI.lean       -- compileToJson, runCommand, main
Heyting/CLIArgs.lean   -- argument parsing (Options, parse)
```
