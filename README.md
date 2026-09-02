# Heyting

Lean 4 + Mathlib compiler from core LLZK fragment to R1CS, with machine-checked
preservation and reflection across typed dialect pipeline.

## Architecture

```text
LLZK text → untyped AST
  → Module [Call, StructObject, Oracle, Felt, ConstrainEq]
  → Oracle projection
  → Call erasure
  → StructObject erasure
  → [Felt, ConstrainEq] → R1CSLike → FlatIR → R1CS
```

Compute execution runs against full typed source module. It threads field
locals, object paths, witness storage, allocation state, and positional Oracle
input. Compiler artifact transports canonical source witness through exact
layout used by generated R1CS.

Core correctness abstractions:

- `PresReflPass`: program translation, witness relation, preservation, reflection
- `StructuralPass`: partial structural erasure with source/target state relation
- `WitnessCodec`: constructive forward transport and readback

`TypedEntryCompilationArtifact` retains full source module and every certified
intermediate. Lean proves typed-source/R1CS satisfaction equivalence, direct vs
erased checker agreement, and canonical witness readback after successful
lowering/transport.

| Boundary | Status | Main file |
|---|---|---|
| Text → AST | executable, unverified | `Heyting/Parsers/Parser.lean` |
| AST → typed dialect module | executable, partial, unverified | `Heyting/Passes/ASTToDialect.lean` |
| Oracle projection | selected-entry correspondence proved | `Heyting/Dialects/OracleErasure.lean` |
| Call erasure | conditional structural preservation/reflection | `Heyting/Dialects/CallErasure.lean` |
| StructObject erasure | simulation + canonical equivalence | `Heyting/Dialects/StructObjectPass.lean` |
| Leaf dialect → FlatIR | proved semantic/materialization boundary | `Heyting/Dialects/R1CSLikePass.lean` |
| FlatIR → R1CS | full `PresReflPass` | `Heyting/Passes/FlatIRToR1CS.lean` |
| Whole typed entry → R1CS | pointwise satisfaction iff + readback | `Heyting/Passes/DialectPipeline.lean` |

Retired StructIR implementation is preserved on Git branch
`legacy-infrastructure`; it is absent from active source and CLI.

## Supported LLZK fragment

- `felt.add`, `felt.sub`, `felt.mul`, `felt.div`, `felt.neg`, `felt.inv`, `felt.const`
- `constrain.eq`
- `struct.def`, `struct.new`, `struct.readm`, `struct.writem`
- topologically decreasing `@compute`/`@constrain` calls
- `llzk.nondet` through explicit Oracle stream
- public struct members

See [dialect mapping](docs/llzk-dialects.md) and [formal guarantees](docs/GUARANTEES.md).

## Build

Requires [elan](https://github.com/leanprover/elan).

```bash
lake build
lake build hey
```

## CLI

```bash
lake exe hey help
lake exe hey compile [options] <input.llzk> <output>
```

```bash
# Circom-compatible binary R1CS
lake exe hey compile circuit.llzk out/system

# JSON R1CS and generated witness
lake exe hey compile --json --auto circuit.llzk out/system

# Named public inputs and positional private Oracle values
lake exe hey compile --input inputs.json --oracle oracle.json circuit.llzk out/system

# Alternative field
lake exe hey compile --prime-field babybear circuit.llzk out/system
```

Supported fields: `bn254` (default), `bn128`, `babybear`, `goldilocks`,
`mersenne31`, `koalabear`. `bn254`/`bn128` outputs are checked with snarkjs.
See [CLI reference](docs/cli.md).

## Tests

```bash
./tests/run_tests.sh
./scripts/smoke_cli.sh
```

Suite covers arithmetic, division/inverse validity, objects, public members,
nested calls, Oracle consumption/exhaustion, binary/JSON output, and snarkjs
witness validation. `tests/adversarial_full.llzk` combines every supported
compiler feature; valid Oracle values pass, altered values must fail direct
typed-source checking.

## Remaining work

- verify or translation-validate parser and AST-to-dialect lowering
- prove source witness generator satisfies source constraints under explicit preconditions
- support free/helper functions, arrays, control flow, casts, bool/poly dialects
- add verified optimization passes and additional constraint backends

## License

Apache 2.0
