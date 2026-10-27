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
- `--auto`: execute the entry compute body and write a witness. Only for entries without
  inputs: inputs are never defaulted, so an entry with inputs needs `--input`.
- `--input <path>`: JSON object of inputs, keyed by the entry `@compute` parameter names.
  Every parameter needs a value; unknown keys are errors.
- `--oracle <path>`: positional JSON array consumed by `llzk.nondet`; requires witness generation.
- `--prime-field <name>`: `bn254`, `bn128`, `babybear`, `goldilocks`, `mersenne31`, `koalabear`.
  Default: the field the program names (`!felt.type<"name">`), else `bn254`.
- `--output <path>`: alternative output path syntax.

`--input` triggers witness generation without `--auto`. `--oracle` requires
`--auto` or `--input`. Missing Oracle values fail with `oracleUnderflow`; values that
`llzk.nondet` never reads are an error.

## Examples

```bash
lake exe hey compile circuit.llzk out/system
lake exe hey compile --json circuit.llzk out/system
lake exe hey compile --json --input inputs.json circuit.llzk out/system
lake exe hey compile --input inputs.json --oracle oracle.json circuit.llzk out/system
lake exe hey compile --prime-field babybear circuit.llzk out/system
```

Witness generation checks original typed-source constraints first, erased
artifact constraints second as differential assertion, then transports to R1CS.
Failure messages distinguish runtime/lowering faults from constraint rejection.
Argument, lowering, runtime, and constraint errors return nonzero process status.
When witness generation is requested (`--auto` or `--input`), a witness failure aborts
before any output is written, so no `.r1cs` file is produced. Compiling without a witness
request writes the R1CS only.
A struct without a `constrain` function is rejected (it would compile to an unconstrained
circuit); a struct without `compute` is accepted but cannot produce a witness. Duplicate
member names are rejected.
Entries whose compute function has more parameters than the constrain function are
rejected at lowering.

## Entry struct

The circuit is the struct named by the root-module attribute
`llzk.main = !struct.type<@Path>`, as in upstream LLZK. Without `llzk.main`, it is the
unique struct that no other struct uses; several candidates are an error. Only the entry
and the structs it uses, directly or transitively, are lowered. Free functions anywhere in
the module are rejected.

## Public statement

The R1CS statement is the entry's public outputs (`{llzk.pub}` felt members, in member order)
followed by its public inputs (`{llzk.pub}` compute parameters, in order). They occupy wires
`1..k` (`nPubOut`, then `nPubIn` in the `.r1cs` header); every other wire is private.

## Frontend strictness

The parser and typed frontend reject every construct outside the supported subset instead
of skipping it. See [supported LLZK syntax](llzk-dialects.md#heyting-frontend-rules).

## Field boundary

Without `--prime-field` and without a field name in the program, `bn254` is used: the BN128
scalar modulus expected by Circom/snarkjs. A program that names a field compiles only for
that field, and a program that names two fields is rejected. All pass
theorems are generic over `F : Type [Field F]`; field selection happens only in
CLI. Large primality facts are isolated private CLI axioms.

## Outputs

| Mode | Constraints | Witness |
|---|---|---|
| default | `.r1cs` | `.wtns` when generated |
| `--json` | `.r1cs.json` | `.witness.json` when generated |

User-supplied precomputed witness loading is not exposed.
