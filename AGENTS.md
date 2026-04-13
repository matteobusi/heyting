# Heyting — Agent Guide

AI agent reference for this codebase. Read before making changes.

## What this project is

Heyting is a **formally verified ZKP compiler** in Lean 4 + Mathlib. It compiles a core
fragment of LLZK down to R1CS and proves correctness — no constraints added or lost.

Every theorem: **0 sorries**, **standard axioms only** (`propext`, `Classical.choice`,
`Quot.sound`). Non-negotiable.

## Build

```bash
lake build        # library
lake build hey    # compiler binary
```

Requires [elan](https://github.com/leanprover/elan). Lean 4.28.0, Mathlib v4.28.0.

## Repository layout

```
Heyting/
  Core/
    Language.lean          -- Language typeclass
    Pass.lean              -- Pass, PreservingPass, ReflectingPass, PresReflPass
    TrinitaryCC.lean       -- TPσ ↔ CC~ ↔ TPτ (Abate et al.)
  Languages/
    StructIR.lean          -- Hierarchical IR (structs, calls, felt ops)
    FlatIR.lean            -- Flat instruction list (7 types)
    R1CS.lean              -- Rank-1 Constraint Systems
  Passes/
    StructIRToFlatIR.lean  -- StructIR → FlatIR (~1860 lines)
    FlatIRToR1CS.lean      -- FlatIR → R1CS (~220 lines)
    Lowering.lean          -- LLZK AST → StructIR (unverified, partial)
    Tactics.lean           -- r1cs_arith, r1cs_unfold_sat macros
  Parser/
    AST.lean               -- Untyped LLZK AST
    Tokenizer.lean         -- MLIR textual IR tokenizer
    Parser.lean            -- Recursive descent parser
    Main.lean              -- parseFile, ppModule
  Backends/
    R1CSJSON.lean          -- R1CS → JSON serialization
  Examples/
    StructIRExamples.lean  -- 4 validated examples
    LoweringExamples.lean  -- LLZK → StructIR → R1CS pipeline
    OutputExamples.lean    -- JSON output via CLI
    ParserExamples.lean    -- Parser on 5 real LLZK files
  Test/
    R1CSJSONTest.lean      -- Unit tests for R1CS JSON
  CLI.lean                 -- hey compile; prime field dispatch
  CLIArgs.lean             -- CLI argument parser
docs/
  GUARANTEES.md    -- Formal guarantees per pass (read first)
  WARNING.md       -- Assumptions, limitations, resolved issues
  languages.md     -- Language design and semantics
  ROADMAP.md       -- Development roadmap
  tactics.md       -- Tactic documentation
  cli.md           -- CLI usage and --prime-field documentation
  llzk-dialects.md -- LLZK MLIR dialect reference
  diary.md         -- Chronological session diary
  MATTEO_NOTES.md  -- Author's design notes
```

## Correctness framework

All passes implement `PresReflPass S T`:
- **`compile`**: source → target program
- **`witnessRel`**: relates source/target witnesses (per-program)
- **Reflection (= CC~)**: target sat → source sat (soundness)
- **Preservation**: source sat → target sat (completeness)

Together: equisatisfiability. All theorems are **generic over `F : Type [Field F]`**.
See `docs/GUARANTEES.md` for formal statements.

## CLI prime fields

`Heyting/CLI.lean` supports 6 fields matching `llzk-lib/lib/Util/Field.cpp`:

| Flag | Prime | Used by |
|------|-------|---------|
| `bn254` *(default)* / `bn128` | 2188…8583 (254-bit) | circom |
| `babybear` | 2013265921 (15·2²⁷+1) | zirgen |
| `goldilocks` | 18446744069414584321 (2⁶⁴−2³²+1) | plonky2 |
| `mersenne31` | 2147483647 (2³¹−1) | Plonky3 |
| `koalabear` | 2130706433 (2³¹−2²⁴+1) | Plonky3 |

Primality for bn254/bn128 and goldilocks uses `private axiom` in `CLI.lean` (too large
for `native_decide`/`norm_num`). Axioms are CLI-only — never in any proof file.

```bash
lake exe hey compile --prime-field babybear circuit.llzk out/system.json
```

## Key invariants — do not break

1. **Zero sorries.** No `sorry` in committed code.
2. **Standard axioms only.** No `axiom` in proof files. CLI `private axiom` is OK.
   Verify: `lean_verify <file> <theorem>` → `propext`, `Classical.choice`, `Quot.sound`.
3. **`lake build` must pass.** 0 errors, 0 warnings.
4. **Intrinsic well-formedness.** StructIR uses dependent types (`Fin i`, `Fin numMembers`,
   `noDupReads`). No runtime checks or fuel-based recursion.

## Working with Lean files

**Field parameterization:** Pass functions take `(F : Type) [Field F]` explicitly.
Examples/tests use `F := ZMod 1993`. Do not hardcode a prime in proof files.
`DecidableEq F`, `IntCast F` needed for lowering; `Repr F` for JSON.

**Imports:** Minimize — import specific Mathlib modules, not `import Mathlib`.

**New StructIR statement type** — add cases in:
`compileConstrainBody`, `buildWitness`, `buildVarAlloc`, `evalConstrainBody`,
`readPositions`, and all proof theorems (`preservation_body`, `reflection_direct`,
`reflection_body`, `compileConstrainBody_instrVars_bounded`, `buildWitness_preserves_below`,
`buildWitness_next_le`, `buildWitness_compileConstrainBody_next`, `buildVarAlloc_next_eq`,
`buildVarAlloc_alloc_bound`, `buildWitness_varAlloc_agree`, `buildVarAlloc_preserves_absent`,
`buildVarAlloc_acc_irrelevant`).

**New FlatIR instruction** — add to `compileInstr` (1–2 constraints), then preservation +
reflection cases via `r1cs_arith`; fall back to `linear_combination`/`field_simp`.
See `docs/tactics.md`.

**Macro hygiene:** Tactics in `Tactics.lean` cannot reference names from other files.
`StructIRToFlatIR.lean` keeps its own `VarMap` alias to avoid collisions. Pass-specific
unfolding at the call site, not in a tactic.

**Helper lemma extraction:** Cannot factor out proof code involving a recursive call to
the theorem being proved (felt-op cases in `reflection_direct`/`reflection_body`).
Non-recursive obligations can be factored (e.g. `preservation_body_peel_binop`).

## Verification checklist

1. `lean_diagnostic_messages <file>` → 0 errors
2. `lake build` → 0 errors
3. `lean_verify <file> <theorem>` → standard axioms only
4. No `sorry`: `grep -r "sorry" Heyting/` → empty

## Documentation

| File | When to update |
|------|----------------|
| `docs/GUARANTEES.md` / `docs/languages.md` | Pass behavior, new languages, correctness framework |
| `docs/WARNING.md` | New assumptions, limitations, resolutions; check before touching `assignDiv`, `noDupReads`, `objEnv` |
| `docs/cli.md` | CLI flags, supported fields |
| `docs/llzk-dialects.md` | New LLZK dialects/ops, parser work |
| `docs/diary.md` | Append session summary each session |
| `docs/ROADMAP.md` | Completing or reprioritizing roadmap items |
| `docs/tactics.md` | New tactics or proof patterns |
| `README.md` | User-facing changes |
