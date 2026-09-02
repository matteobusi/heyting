# Heyting

A formally verified ZKP compiler, written in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

Heyting compiles constraint languages (currently a core fragment of [LLZK](https://github.com/project-llzk/llzk-lib)) down to [R1CS](https://www.rareskills.io/post/r1cs) arithmetizations, and proves that compilation is correct: no constraints added, no constraints lost.

## Architecture

Compiler organized around 2 core abstractions:

- **Language**: typeclass pairing program syntax with satisfaction relation over witnesses (`w |= p`)
- **PresReflPass**: compiler pass with witness relation and 2 proofs:
  - *Reflection* (= CC~): target sat implies related source sat
  - *Preservation*: source sat implies related target sat

Together, these give equisatisfiability for passes with full proofs.

### Compiler pipelines

The architecture under active development is dialect-native:

```text
LLZK AST -> [Call, StructObject, Oracle, Felt, ConstrainEq]
         -> oracle erasure -> [Call, StructObject, Felt, ConstrainEq]
         -> call erasure -> [StructObject, Felt, ConstrainEq]
         -> object erasure -> [Felt, ConstrainEq] -> R1CSLike -> R1CS
```

Struct-object and oracle operations survive the typed frontend boundary.
Compute execution threads field locals, object paths, witness storage,
allocation state, and the oracle cursor. Constraint compilation explicitly
erases Oracle before Call and StructObject. The unflagged CLI uses this
dialect-native path; the quarantined reference remains available explicitly:

```text
StructIR  --->  FlatIR  --->  FlatIR(compact)  --->  R1CS
```

| Stage | Status | File |
|------|--------|------|
| **StructIR** | hierarchical source IR | `Heyting/Languages/StructIR.lean` |
| **StructIR -> FlatIR** | legacy reference lowering; full `PresReflPass` (`CorrectPass`) | `Heyting/Passes/StructIRToFlatIR.lean` |
| **FlatIR** | flat instruction IR | `Heyting/Languages/FlatIR.lean` |
| **FlatIR -> FlatIR(compact)** | dense variable renaming; proved `PresReflPass` | `Heyting/Passes/FlatIRCompact.lean` |
| **FlatIR -> R1CS** | fully verified `PresReflPass` | `Heyting/Passes/FlatIRToR1CS.lean` |
| **R1CS** | backend constraint system | `Heyting/Languages/R1CS.lean` |
| **Legacy pipeline** | compatibility composition; full `PresReflPass` (`CorrectPass`) | `Heyting/Legacy/Pipeline.lean` |

Dialect witness generation supports `--auto`, `--input`, and positional
`llzk.nondet` values from `--oracle`. Use `--legacy` to select the proved
StructIR reference pipeline explicitly.

The dialect path now returns a proof-carrying whole-entry artifact. It retains
original typed module, selected entry, structural erasure certificates, exact
leaf program, witness layout, and R1CS auxiliary construction. Lean proves
original typed-source/R1CS satisfaction equivalence, executable checker
agreement, and exact canonical witness readback for every successful transport.

### Current proof status

- `FlatIR -> FlatIR(compact)` is fully verified as a `PresReflPass`.
- `FlatIR -> R1CS` is fully verified as a `PresReflPass`.
- `StructIR -> FlatIR` is fully verified as a `PresReflPass`.
- `StructIR -> FlatIR -> FlatIR(compact) -> R1CS` pipeline is fully verified as a `PresReflPass`.
- Dialect whole-entry compilation has constructive typed-source/R1CS
  satisfaction iff, direct/artifact checker agreement, and exact finite
  readback; this supplements existential pass proofs.
- Current active support file for pass-1 proofs is `Heyting/Languages/StructIRFreshen.lean`.

See `docs/GUARANTEES.md` for current status.

### Parser

LLZK parser reads MLIR textual IR and produces untyped AST.

| Component | File |
|-----------|------|
| **AST** | `Heyting/Parsers/AST.lean` |
| **Tokenizer** | `Heyting/Parsers/Tokenizer.lean` |
| **Parser** | `Heyting/Parsers/Parser.lean` |
| **Entry point** | `Heyting/Parsers/Main.lean` |

Supported constructs include felt ops, struct ops, `constrain.eq`, function calls, `llzk.nondet`, and returns. Unsupported ops are skipped with warnings.

See `docs/llzk-dialects.md` for full LLZK dialect reference and supported feature mapping.

## Building

Requires [elan](https://github.com/leanprover/elan).

```bash
lake build
lake build hey
```

> macOS 15 note: `lake cache get` may fail with `Invalid platform: Unexpected characters in platform`. First `lake build` may compile from source. See `docs/WARNING.md`.

## Usage

```bash
lake build hey
lake exe hey help
lake exe hey compile [--prime-field <field>] <input.llzk> <output>
lake exe hey compile --dialect <input.llzk> <output>
lake exe hey compile --legacy <input.llzk> <output>
lake exe hey compile --auto --oracle <oracle.json> <input.llzk> <output>
```

Or invoke binary directly at `.lake/build/bin/hey`.

### Supported prime fields

Default field is `bn254`.

| Flag | Prime | Used by |
|------|-------|---------|
| `bn254` *(default)* | 21888242871839275222246405745257275088548364400416034343698204186575808495617 | circom/snarkjs |
| `bn128` | same as bn254 (alias) | circom |
| `babybear` | 2013265921 (15 · 2²⁷ + 1) | zirgen |
| `goldilocks` | 18446744069414584321 (2⁶⁴ − 2³² + 1) | plonky2 |
| `mersenne31` | 2147483647 (2³¹ − 1) | Plonky3 |
| `koalabear` | 2130706433 (2³¹ − 2²⁴ + 1) | Plonky3 |

External binary-compatibility smoke checks are validated with `snarkjs` for `bn254`/`bn128`.
**Compatibility and witness-checking flows for other supported fields are still being investigated.**

### Example

```bash
mkdir -p out

# Binary R1CS
lake exe hey compile circuit.llzk out/system

# JSON R1CS
lake exe hey compile --json circuit.llzk out/system

# JSON R1CS + witness generation
lake exe hey compile --json --auto circuit.llzk out/system

# Nondeterministic values are a JSON array of decimal strings
lake exe hey compile --auto --oracle oracle.json circuit.llzk out/system

# Explicit field selection
lake exe hey compile --prime-field babybear circuit.llzk out/system
```

All pass theorems are generic over `F : Type [Field F]`; CLI field selection happens only at boundary.

On the legacy path, compaction matters for emitted artifacts: sparse
witness-coordinate variables from `StructIR -> FlatIR` are renamed densely
before R1CS lowering. For example,
`scripts/multiply.llzk` drops from `994` wires to `15` wires with identical
constraints and a valid `snarkjs` witness check.

## Testing

Comprehensive test suite in `tests/` directory exercises all supported LLZK features:

| Test | Features Exercised |
|------|-------------------|
| `felt_ops.llzk` | All felt operations: `add`, `sub`, `mul`, `div`, `neg`, `inv`, `const` |
| `struct_ops.llzk` | Struct operations: `new`, `readm`, `writem` |
| `function_call.llzk` | Function calls between `@compute` and `@constrain` |
| `constrain_eq.llzk` | Multiple `constrain.eq` constraint emission |
| `nondet.llzk` | Nondeterministic witness values (`llzk.nondet`) |
| `multi_struct.llzk` | Struct with 8 members (objEnv tracking) |
| `nested_calls.llzk` | Function call chains (depth 3) |
| `pub_members.llzk` | Public struct members (`llzk.pub` attribute) |

Run test suite:

```bash
# Run all tests
./tests/run_tests.sh

# Run smoke tests (includes test suite)
./scripts/smoke_cli.sh
```

Each test verifies:
- Parsing succeeds
- Dialect and legacy compilation produce R1CS output
- Witness-capable fixtures validate both witnesses with `snarkjs`
- Nonzero oracle and division-validity boundaries are exercised by smoke tests

- [x] FlatIR -> R1CS proof
- [x] StructIR language with intrinsic well-formedness
- [x] Direct executable StructIR -> FlatIR lowering
- [x] `StructIR -> FlatIR` full `PresReflPass`
- [x] pipeline full `PresReflPass`
- [x] LLZK parser and lowering to StructIR
- [x] JSON and binary R1CS / witness output
- [ ] Array support
- [ ] Verified optimization passes

## License

Apache 2.0
