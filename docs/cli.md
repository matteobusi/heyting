---
title: Hey CLI
---

# Hey CLI

## Usage

```text
hey compile [options] <input.llzk> <output>
hey help
```

CLI exposes one dialect-native compiler pipeline. Retired `--legacy` and
redundant `--dialect` selectors are errors.

## Options

- `--json`: write `<output>.r1cs.json`; otherwise Circom-compatible `<output>.r1cs`.
- `--auto`: execute compute body with default-zero public inputs and write witness.
- `--input <path>`: named JSON public inputs, reordered to top-level compute parameters.
- `--oracle <path>`: positional JSON array consumed by `llzk.nondet`; requires witness generation.
- `--prime-field <name>`: `bn254`, `bn128`, `babybear`, `goldilocks`, `mersenne31`, `koalabear`.
- `--output <path>`: alternative output path syntax.

`--input` triggers witness generation without `--auto`. `--oracle` requires
`--auto` or `--input`. Missing Oracle values fail with `oracleUnderflow`.

## Examples

```bash
lake exe hey compile circuit.llzk out/system
lake exe hey compile --json circuit.llzk out/system
lake exe hey compile --json --auto circuit.llzk out/system
lake exe hey compile --input inputs.json --oracle oracle.json circuit.llzk out/system
lake exe hey compile --prime-field babybear circuit.llzk out/system
```

Witness generation checks original typed-source constraints first, erased
artifact constraints second as differential assertion, then transports to R1CS.
Failure messages distinguish runtime/lowering faults from constraint rejection.
Argument, lowering, runtime, and constraint errors return nonzero process status.

## Field boundary

Default `bn254` uses BN128 scalar modulus expected by Circom/snarkjs. All pass
theorems are generic over `F : Type [Field F]`; field selection happens only in
CLI. Large primality facts are isolated private CLI axioms.

## Outputs

| Mode | Constraints | Witness |
|---|---|---|
| default | `.r1cs` | `.wtns` when generated |
| `--json` | `.r1cs.json` | `.witness.json` when generated |

User-supplied precomputed witness loading is not exposed.
