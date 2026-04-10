# Heyting

A formally verified ZKP compiler, written in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

Heyting compiles constraint languages (currently a core fragment of [LLZK](https://github.com/nicboul3/llzk-lib)) down to [R1CS](https://www.rareskills.io/post/r1cs) arithmetizations, and proves that the compilation is **correct** — meaning no constraints are added or lost in translation.

## Why formal verification?

A bug in a ZKP compiler can silently break **soundness** (accepting invalid proofs) or **completeness** (rejecting valid ones). Unlike conventional compilers where bugs cause crashes or wrong outputs, ZKP compiler bugs undermine the cryptographic guarantees that the entire system relies on. Formal verification gives mathematical certainty that the compiler preserves the meaning of constraints.

## Architecture

The compiler is structured around two core abstractions:

- **Language**: a typeclass pairing a program syntax with a satisfaction relation over witnesses (`w |= p`)
- **PresReflPass**: a compiler pass equipped with a witness relation and two proofs:
  - *Reflection* (= CC~): if a witness satisfies the target, there exists a related witness satisfying the source — the compiler doesn't lose constraints (soundness)
  - *Preservation*: if a witness satisfies the source, there exists a related witness satisfying the target — the compiler doesn't add spurious constraints (completeness)

Together, these give equisatisfiability: the source and compiled programs accept the same (related) witnesses. Reflection alone is CC~ (trace-relating compiler correctness) from Abate et al. (ESOP 2020); preservation is an additional guarantee beyond CC~.

### Languages

| Language | Description | File |
|----------|-------------|------|
| **StructIR** | Structured IR with structs, functions, nesting, cross-struct calls | `Heyting/Languages/StructIR.lean` |
| **FlatIR** | Flat instruction language: felt arithmetic + equality assertions | `Heyting/Languages/FlatIR.lean` |
| **R1CS** | Rank-1 Constraint Systems (`A * B = C` over linear combinations) | `Heyting/Languages/R1CS.lean` |

See [`docs/languages.md`](docs/languages.md) for detailed descriptions of each language, their semantics, and design decisions.

### Parser

The LLZK parser reads real circuit files in MLIR textual IR format and
produces an untyped AST (`LLZK.Module`).

| Component | File |
|-----------|------|
| **AST** | `Heyting/Parser/AST.lean` |
| **Tokenizer** | `Heyting/Parser/Tokenizer.lean` |
| **Parser** | `Heyting/Parser/Parser.lean` |
| **Entry point** | `Heyting/Parser/Main.lean` |

Supported constructs: felt ops (`add`, `sub`, `mul`, `div`, `neg`, `inv`, `const`), struct ops (`new`, `readm`, `writem`), `constrain.eq`, function calls (including qualified names like `@Mod::@func`), `llzk.nondet`, and function returns. Unsupported ops are skipped with warnings.

```lean
#eval do
  let (mod, warnings) ← LLZK.parseFile "path/to/circuit.llzk"
  IO.println (LLZK.ppModule mod)
```

See `Heyting/Examples/ParserExamples.lean` for usage on 5 real LLZK test files.

### Passes

| Pass | Status | File |
|------|--------|------|
| **StructIR → FlatIR** | Fully verified (0 `sorry`, standard axioms only) | `Heyting/Passes/StructIRToFlatIR.lean` |
| **FlatIR → R1CS** | Fully verified (0 `sorry`, standard axioms only) | `Heyting/Passes/FlatIRToR1CS.lean` |

### Examples

4 validated StructIR examples in `Heyting/Examples/StructIRExamples.lean`:
- Single struct with equality constraints (Component1A)
- Felt addition (Adder)
- Felt division with non-zero constraint (Divider)
- Nested structs with cross-struct calls (Wrapper → Component1A)

Each includes `noDupReads` proofs, positive/negative satisfaction proofs, and full pipeline compilation output.

5 parser examples in `Heyting/Examples/ParserExamples.lean`:
- Constraint emission (`emit_pass.llzk` — 5 structs)
- Nondet + constraints (`nondet_preservation.llzk` — 1 struct)
- Circom circuits (`circomlib.llzk` — 2 structs, qualified calls)
- Felt arithmetic (`felt_arith_pass.llzk` — free functions, correctly skipped)
- Struct operations (`structs_pass.llzk` — 25 structs, templates skipped)

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake build          # build the library
lake build heytingc # build the compiler binary
```

> **macOS 15 (darwin 24.x) note:** `lake cache get` may fail with `Invalid platform: Unexpected characters in platform`. This is a known Lake 5.0.0 / Reservoir API incompatibility — the first `lake build` will compile from source (~30 min). See [`docs/WARNING.md`](docs/WARNING.md) §6 for details and the `heytingc` linker workaround if needed.

## Usage

Build the compiler binary:

```bash
lake build heytingc
```

Run it with `lake exe` (no need to reference the binary path directly):

```bash
lake exe heytingc help
lake exe heytingc json <input.llzk> <output.json>
```

Or invoke the binary directly at `.lake/build/bin/heytingc`.

### Example

```bash
mkdir -p out
lake exe heytingc json llzk-lib/test/Dialect/Constrain/emit_pass.llzk out/emit_pass.json
# Wrote R1CS JSON to out/emit_pass.json
#   Constraints: 4
#   Variables: 3
```

The output JSON has this structure:

```json
{
  "numConstraints": 4,
  "numVars": 3,
  "numAuxVars": 0,
  "constraints": [
    { "A": [...], "B": [...], "C": [...] },
    ...
  ]
}
```

Each constraint is an R1CS triple `A * B = C` over linear combinations of field elements.
Variables are tagged `varOne` (the constant 1), `var n` (input/output), or `aux n` (auxiliary).

> **Note:** The field is currently hardcoded to `ZMod 1993` (the prime field **F₁₉₉₃**).

### Compatibility with circom's JSON format

The output is **not compatible** with circom's `--json` format. Circom uses a different schema:

| | Heyting | circom |
|---|---|---|
| Top-level shape | `{numConstraints, numVars, numAuxVars, constraints: [...]}` | `{constraints: [...]}` |
| Constraint shape | `{"A": lc, "B": lc, "C": lc}` | `[lc_A, lc_B, lc_C]` (3-element array) |
| Linear combination | `[{var: {tag, index}, coeff: "repr"}, ...]` | `{"signal_index": "decimal_coeff_string", ...}` |
| Constant 1 | `{tag: "varOne"}` | signal index `"0"` |
| Coefficients | `repr` of field element (e.g. `"1"`) | decimal string of the full field element integer |

Bridging to snarkjs or other circom tooling would require a post-processing step to convert to circom's schema. This is a planned future output format.

## Roadmap

See [`docs/ROADMAP.md`](docs/ROADMAP.md) for the detailed roadmap.

- [x] FlatIR → R1CS pass (fully verified)
- [x] StructIR language (structs, functions, nesting with intrinsic well-formedness)
- [x] StructIR → FlatIR pass (fully verified)
- [x] Nested struct support (readMember/objEnv tracking)
- [x] Proof engineering: custom tactics for pass proofs
- [x] LLZK parser (read real circuit files)
- [x] AST → StructIR lowering
- [x] R1CS serialization output (`heytingc json`)
- [ ] Array support
- [ ] Optimization passes (with correctness proofs)

## License

MIT
