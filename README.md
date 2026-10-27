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
  → [Felt, ConstrainEq] → R1CSLike → R1CS
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

## Top-level guarantee

`compiler_guarantee` (`Heyting/Guarantees.lean`) bundles, for every successfully compiled
entry, the properties proved about its R1CS output:

- **Levin reduction** (`entryLevinReduction`): the public statement is the public outputs
  (`{llzk.pub}` members) then the public inputs (`{llzk.pub}` compute parameters). Every
  source instance maps to an R1CS instance for the same statement, and every R1CS instance
  extracts, by a fixed wire reindexing, to a source instance.
- **Statement wires**: distinct, and serialized at wires `1..k` as Circom/snarkjs expect.
- **Determinism** (`determines_iff`): compilation adds and removes no under-constrained
  witness pairs.

For the prover, `proveEntry_sound` and `proveEntry_complete` relate the executable witness
generator to the relation, and `genWitness_fault` shows that compute fails only on run-time
data (oracle underflow, zero denominator). For a proof system that is knowledge-sound and
zero-knowledge for R1CS, the Levin reduction transfers both properties to the source; that
transfer argument is standard but not formalized.

| Boundary | Status | Main file |
|---|---|---|
| Text → AST | executable, unverified | `Heyting/Parsers/Parser.lean` |
| AST → typed dialect module | executable, partial, unverified | `Heyting/Passes/ASTToDialect.lean` |
| Oracle projection | selected-entry correspondence proved | `Heyting/Dialects/OracleErasure.lean` |
| Call erasure | conditional structural preservation/reflection | `Heyting/Dialects/CallErasure.lean` |
| StructObject erasure | simulation + canonical equivalence | `Heyting/Dialects/StructObjectPass.lean` |
| Leaf dialect → R1CSLike | proved semantic/materialization boundary | `Heyting/Dialects/R1CSLikePass.lean` |
| R1CSLike → R1CS | direct `PresReflPass` + constructive codec | `Heyting/Dialects/R1CSLike.lean` |
| Whole typed entry → R1CS | `EntryCorrect`: preservation (with total `forward`) + arbitrary-target reflection + readback | `Heyting/Passes/DialectPipeline.lean` |
| Public statement | Levin reduction, statement fidelity | `Heyting/Passes/DialectPipeline.lean` |
| Wire layout | statement wires at `1..k`, injective layout | `Heyting/Backends/WireAssignment.lean` |
| Top-level bundle | `compiler_guarantee` | `Heyting/Guarantees.lean` |
| `.r1cs`/`.wtns` bytes | executable, tested with snarkjs | `Heyting/Backends/` |

`typed_entry_correct` proves both directions for a compiled entry. Every canonically sized
observation satisfying the typed-source semantics is accepted by `forward`, giving a
satisfying R1CS witness that reads back to it. Every satisfying R1CS witness, however
obtained, reads back to a satisfying observation. Not covered: parser and AST-to-dialect
fidelity, agreement of the compute executor with upstream LLZK, and serialization bytes.
The prover is sound and conditionally complete (`proveEntry_sound`, `proveEntry_complete`),
and compilation preserves and reflects determinism (`determines_iff`).
`EntryCorrect` is not a literal `PresReflPass` instance. See the
[proof audit guide](docs/AUDIT.md) for exact contracts, dependencies, and proof sketches.

## Supported LLZK fragment

- `felt.add`, `felt.sub`, `felt.mul`, `felt.div`, `felt.neg`, `felt.inv`, `felt.const`
- `constrain.eq`
- `struct.def`, `struct.new`, `struct.readm`, `struct.writem`, including struct-typed
  members (sub-components)
- topologically decreasing `@compute`/`@constrain` calls with absolute symbol paths
- `llzk.nondet` through explicit Oracle stream
- `{llzk.pub}` members (public outputs) and compute/constrain parameters (public inputs)
- entry selection by `llzk.main`, else the unique root struct

Objects form a tree shared by compute and constrain: a sub-component stored in member `m`
of the object at path `p` lives at `p ++ [m]`. The frontend is strict: unsupported
operations, attributes, types, templates, and ill-typed member accesses are errors, never
skipped.

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

# JSON R1CS and generated witness from named inputs
lake exe hey compile --json --input inputs.json circuit.llzk out/system

# Named inputs and positional private Oracle values
lake exe hey compile --input inputs.json --oracle oracle.json circuit.llzk out/system

# Alternative field
lake exe hey compile --prime-field babybear circuit.llzk out/system
```

Supported fields: `bn254` (default unless the program names a field), `bn128`, `babybear`,
`goldilocks`, `mersenne31`, `koalabear`. `bn254`/`bn128` outputs are checked with snarkjs.
See [CLI reference](docs/cli.md).

## Tests

```bash
./tests/run_tests.sh
./scripts/smoke_cli.sh
```

Suite covers arithmetic, division/inverse validity, objects, sub-component placement,
public outputs and inputs (snarkjs Groth16 `public.json`), frontend rejections, nested calls, Oracle consumption/exhaustion, binary/JSON output, and snarkjs
witness validation. `tests/adversarial_full.llzk` combines every supported
compiler feature; valid Oracle values pass, altered values must fail direct
typed-source checking.

## Remaining work

- verify or translation-validate parser and AST-to-dialect lowering
- prove compute output satisfies constraints for a supported program class
- differential testing of the compute executor against upstream LLZK
- support free/helper functions, arrays, control flow, casts, bool/poly dialects
- certify byte-level `.r1cs`/`.wtns` serialization
- formalize the transfer of knowledge soundness and zero knowledge through the Levin
  reduction for an abstract proof system
- add verified optimization passes and additional constraint backends

## License

Apache 2.0
