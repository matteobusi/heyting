---
title: Hey CLI
---

## Overview

The Heyting compiler provides `hey`, a small CLI for compiling LLZK to R1CS and,
optionally, generating a witness by running dialect `@compute` bodies. The
StructIR reference implementation remains available with `--legacy`.

## Usage

```
hey compile [options] <input.llzk> <output>
hey help
```

## Options

- `--json`
  Produce human-readable JSON output.
  Without this flag, `compile` writes Circom-compatible binary `.r1cs` output.

- `--prime-field <name>`
  Select the prime field for arithmetic. Supported values:

  | Name | Prime | Used by |
  |------|-------|---------|
  | `bn254` *(default)* | 21888242871839275222246405745257275088548364400416034343698204186575808495617 | circom/snarkjs |
  | `bn128` | same as bn254 (alias) | circom |
  | `babybear` | 2013265921 (15 · 2²⁷ + 1) | zirgen |
  | `goldilocks` | 18446744069414584321 (2⁶⁴ − 2³² + 1) | plonky2 |
  | `mersenne31` | 2147483647 (2³¹ − 1) | Plonky3 |
  | `koalabear` | 2130706433 (2³¹ − 2²⁴ + 1) | Plonky3 |

  These are Heyting's supported CLI fields. For `bn254` / `bn128`, Heyting uses
  the BN128 scalar field modulus expected by Circom/snarkjs binary `.r1cs` /
  `.wtns` tooling. If `--prime-field` is omitted, `bn254` is used.

- `--input <path>`
  JSON file of public circuit inputs (field elements) to pass to the circuit's `@compute`
  bodies. Parsed by signal name and reordered to match top-level `@compute` parameters.

- `--auto`
  Automatically run compute bodies to produce a witness, using empty public inputs unless
  `--input` is also provided.
  Writes `<output>.witness.json` with `--json`, or `<output>.wtns` otherwise.

- `--oracle <path>`
  JSON array of decimal strings consumed positionally by `llzk.nondet`, for
  example `["3", "-1"]`. Requires `--auto` or `--input` and is dialect-only.
  Supplying fewer values than the program consumes reports oracle exhaustion;
  missing private values are never silently replaced by zero.

- `--dialect`
  Explicitly select the dialect-native pipeline, which is already the default.
  Witness generation checks original typed-source constraints before transport,
  then runs erased artifact checker as an internal differential assertion.
  Source constraint failures are reported separately from execution,
  materialization, and backend transport faults.

- `--legacy`
  Select the quarantined, proved StructIR reference pipeline.

- `--output <path>`
  Alternative way to specify the output path (useful when paths contain spaces or when scripting).

## Examples

```bash
# Default field (bn254, matches circom), binary output
lake exe hey compile circuit.llzk out/system

# JSON R1CS
lake exe hey compile --json circuit.llzk out/system

# JSON R1CS + auto witness
lake exe hey compile --json --auto circuit.llzk out/system

# Explicit field
lake exe hey compile --prime-field babybear circuit.llzk out/system
lake exe hey compile --prime-field goldilocks circuit.llzk out/system
lake exe hey compile --prime-field mersenne31 circuit.llzk out/system

# Typed nondeterministic input
lake exe hey compile --auto --oracle oracle.json circuit.llzk out/system
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

- User-supplied witness loading (i.e. providing a pre-computed witness directly, bypassing
  `@compute` bodies) is not currently exposed via any flag.

## Where to find the CLI code

```
Heyting/CLI.lean       -- compileToJson, runCommand, main
Heyting/CLIArgs.lean   -- argument parsing (Options, parse)
```
