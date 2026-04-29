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
lake exe tests    # run #eval test suite
```

Requires [elan](https://github.com/leanprover/elan). Lean 4.28.0, Mathlib v4.28.0.

## Repository layout

```
Heyting/
  Core/
    Language.lean          -- Language typeclass
    Pass.lean              -- Pass, PreservingPass, ReflectingPass, PresReflPass
    TrinitaryCC.lean       -- TPσ ↔ CC~ ↔ TPτ (Abate et al.)
    VarIdEncoding.lean     -- Bijective Nat encoding for StructIR.VarId
  Languages/
    StructIR.lean          -- Hierarchical IR (structs, calls, felt ops, readMember)
    StructInlineIR.lean    -- Call-free IR (readMember preserved; calls inlined)
    MemberlessIR.lean      -- Flat-variable IR (no struct hierarchy; calls preserved)
    FlatIR.lean            -- Flat instruction list (7 types; no calls)
    R1CS.lean              -- Rank-1 Constraint Systems
  Passes/
    StructIRToStructInlineIR.lean  -- Pass 1: StructIR → StructInlineIR (~1400 lines)
    StructInlineIRToMemberlessIR.lean -- Pass 2: StructInlineIR → MemberlessIR (~80 lines)
    MemberlessIRToFlatIR.lean      -- Pass 3: MemberlessIR → FlatIR (~260 lines)
    FlatIRToR1CS.lean              -- Pass 4: FlatIR → R1CS (~270 lines)
    Pipeline.lean          -- 4-pass composition; compileProgram; pipelineWitness
    Lowering.lean          -- LLZK AST → StructIR (unverified, partial)
    Tactics.lean           -- r1cs_arith, r1cs_unfold_sat macros
  Parsers/
    AST.lean               -- Untyped LLZK AST
    Tokenizer.lean         -- MLIR textual IR tokenizer
    Parser.lean            -- Recursive descent parser
    Main.lean              -- parseFile, ppModule
    InputJSON.lean         -- JSON witness input parser
  Backends/
    R1CSJSON.lean          -- R1CS → JSON serialization
    R1CSBinary.lean        -- R1CS → Circom .r1cs binary
    WitnessJSON.lean       -- Witness → JSON
    WitnessBinary.lean     -- Witness → .wtns binary
    WireAssignment.lean    -- Wire index encoding
    FieldBytes.lean        -- Field-element byte serialization
  Examples/
    StructIRExamples.lean  -- 4 validated examples
    LoweringExamples.lean  -- LLZK → StructIR → R1CS pipeline
    OutputExamples.lean    -- JSON output via CLI
    ParserExamples.lean    -- Parser on 5 real LLZK files
  Test/
    R1CSJSONTest.lean      -- Unit tests for R1CS JSON
    BinaryTest.lean        -- Unit tests for R1CS/witness binary
    InputJSONTest.lean     -- Unit tests for witness input JSON
    VarIdEncodingTest.lean -- Unit tests for VarIdEncoding
    StructInlineIRTest.lean -- Structural tests for StructInlineIR
    Main.lean              -- Test entry point (lake exe tests)
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
  superpowers/     -- Design specs and implementation plans
multiply.llzk      -- Test circuit: a * b = out (2 R1CS constraints)
```

## Pipeline

The compiler runs four passes:

```
StructIR
  --[Pass 1: StructIRToStructInlineIR]--> StructInlineIR   (inline all calls)
  --[Pass 2: StructInlineIRToMemberlessIR]--> MemberlessIR  (encode VarId → Nat)
  --[Pass 3: MemberlessIRToFlatIR]---------> FlatIR         (inline calls, flatten)
  --[Pass 4: FlatIRToR1CS]-----------------> R1CS           (encode to A·B=C)
```

### Proof status per pass

| Pass | File | PresReflPass | Notes |
|------|------|:---:|-------|
| 1: StructIR → StructInlineIR | `StructIRToStructInlineIR.lean` | ✅ | Full `PresReflPass`; identity `witnessRel` |
| 2: StructInlineIR → MemberlessIR | `StructInlineIRToMemberlessIR.lean` | ⚠️ | `Pass` only; `PresReflPass` is phase-2 work |
| 3: MemberlessIR → FlatIR | `MemberlessIRToFlatIR.lean` | ⚠️ | `witnessRel` defined; no `Pass` instance yet |
| 4: FlatIR → R1CS | `FlatIRToR1CS.lean` | ✅ | Full `PresReflPass` (`CorrectPass`) |
| Pipeline (end-to-end) | `Pipeline.lean` | ⚠️ | `Pass` only; needs passes 2 & 3 done |

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

**New StructIR statement type** — add cases in both `StructIR.lean` and
`StructIRToStructInlineIR.lean`: `inlineBody`, `expandBody`, `inlineBody_props`
(frame + correctness), `inlineBody_frame`, `inlineBody_correct`, `expandBody_correct`,
and `evalConstrainBody_agree`.

**New FlatIR instruction** — add to `FlatIRToR1CS.compileInstr` (1–2 constraints),
then preservation + reflection cases via `r1cs_arith`; fall back to
`linear_combination`/`field_simp`. See `docs/tactics.md`.

**Pass 1 proof structure (`StructIRToStructInlineIR.lean`)**:
The key theorem is `expandBody_correct`: source `evalConstrainBody` ↔ target
`StructInlineIR.evalConstrainBody` after expansion. The `call` case uses:
- `inlineBody_correct` (proved by combined k-bounded strong induction `inlineBody_props`)
- `StructIR.evalConstrainBody_agree` (env-agreement for bounded-variable bodies)
- `inlineBody_frame` (positions < next unchanged after running inlined code)
- `StructInlineIR.evalConstrainBody_append` (splitting evaluation over appended lists)

**Pass 2 open question** (`StructInlineIRToMemberlessIR.lean`):
Currently compiles `readMember dest self member` to `constrainEq dest (Nat.pair self member)`.
This treats local variable `self` as if it *is* the encoded path — which is only correct if
`objEnv self` is always determined by `self` alone. The semantic gap between
StructInlineIR's `ObjEnv`-threaded `readMember` and MemberlessIR's flat `constrainEq`
must be resolved before pass 2 can be proved. See `docs/WARNING.md` §8.

**Pass 3 proof structure (`MemberlessIRToFlatIR.lean`)**:
Follow the old `StructIRToFlatIR` pattern: `compileWitness_agrees` invariant
(`∀ v, wt (vm v) = env v`), preservation/reflection by joint induction on
`(i, stmts.length)`. The `call` case inlines the callee body.

**Macro hygiene:** Tactics in `Tactics.lean` cannot reference names from other files.
Pass-specific unfolding at the call site, not in a tactic.

**Helper lemma extraction:** Cannot factor out proof code involving a recursive call to
the theorem being proved (felt-op cases in induction proofs). Non-recursive obligations
can be factored (e.g., `preservation_body_peel_binop` pattern).

## Verification checklist

1. `lean_diagnostic_messages <file>` → 0 errors
2. `lake build` → 0 errors, 0 warnings
3. `lean_verify <file> <theorem>` → standard axioms only
4. No `sorry`: `grep -r "sorry" Heyting/` → empty (only comment hits OK)
5. `lake exe tests` → 0 errors

## Documentation

| File | When to update |
|------|----------------|
| `docs/GUARANTEES.md` / `docs/languages.md` | Pass behavior, new languages, correctness framework |
| `docs/WARNING.md` | New assumptions, limitations, resolutions |
| `docs/cli.md` | CLI flags, supported fields |
| `docs/llzk-dialects.md` | New LLZK dialects/ops, parser work |
| `docs/diary.md` | Append session summary each session |
| `docs/ROADMAP.md` | Completing or reprioritizing roadmap items |
| `docs/tactics.md` | New tactics or proof patterns |
| `README.md` | User-facing changes |
