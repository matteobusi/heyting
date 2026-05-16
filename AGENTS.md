# Heyting — Agent Guide

AI agent reference for this codebase. Read before making changes.

Respond like smart caveman. Cut all filler, keep technical substance.
- Drop articles (a, an, the), filler (just, really, basically, actually).
- Drop pleasantries (sure, certainly, happy to).
- No hedging. Fragments fine. Short synonyms.
- Technical terms stay exact. Code blocks unchanged.
- Pattern: [thing] [action] [reason]. [next step].

## What this project is

**Formally verified ZKP compiler** in Lean 4 + Mathlib. Compiles LLZK → R1CS, proves correctness — no constraints added/lost.

Every theorem: **0 sorries**, **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`). Non-negotiable.

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
    VarIdEncoding.lean     -- Bijective Nat encoding for StructIR.VarId
  Languages/
    StructIR.lean          -- Hierarchical IR (structs, calls, felt ops, readMember)
    FlatIR.lean            -- Flat instruction list (7 types; no calls)
    R1CS.lean              -- Rank-1 Constraint Systems
    StructIRFreshen.lean   -- Freshening/renaming support for StructIR proofs
  Passes/
    StructIRToFlatIR.lean          -- Executable lowering + reflection proof: StructIR → FlatIR
    FlatIRCompact.lean             -- Dense FlatIR renaming; proved PresReflPass
    FlatIRToR1CS.lean              -- FlatIR → R1CS (~270 lines)
    Pipeline.lean          -- active executable pipeline; compileProgram; pipelineWitness
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
  MATTEO_NOTES.md  -- Author's design notes
  superpowers/     -- Design specs and implementation plans
multiply.llzk      -- Test circuit: a * b = out (2 R1CS constraints)
```

## Pipeline

Current executable compiler path:

```
StructIR
  --[StructIRToFlatIR]--> FlatIR
  --[FlatIRCompact]------> FlatIR
  --[FlatIRToR1CS]------------> R1CS
```

### Proof status

| Component | File | Status | Notes |
|------|------|:---:|-------|
| Executable lowering | `StructIRToFlatIR.lean` | ✅ | active executable lowering and proved `ReflectingPass` |
| Compaction pass | `FlatIRCompact.lean` | ✅ | dense renaming; full `PresReflPass` |
| Proven pass | `FlatIRToR1CS.lean` | ✅ | full `PresReflPass` (`CorrectPass`) |
| Freshening support | `StructIRFreshen.lean` | active | renaming/freshening lemmas used by pass-1 proof |
| Pipeline wrapper | `Pipeline.lean` | ✅ | executable composition and proved `ReflectingPass` |

## Correctness framework

All passes implement `PresReflPass S T`:
- **`compile`**: source → target program
- **`witnessRel`**: relates source/target witnesses (per-program)
- **Reflection (= CC~)**: target sat → source sat (soundness)
- **Preservation**: source sat → target sat (completeness)

`PresReflPass.compose` (in `Core/Pass.lean`) composes 2 passes → new `PresReflPass` with proven preservation + reflection. Composed witness chains through intermediate witness.

Together: correctness framework remains `PresReflPass`-based where proofs exist. All theorems generic over `F : Type [Field F]`.

## CLI prime fields

`Heyting/CLI.lean` supports 6 fields. For `bn254` / `bn128`, CLI uses BN128
scalar field modulus so emitted `.r1cs` / `.wtns` files are accepted by
Circom/snarkjs:

| Flag | Prime | Used by |
|------|-------|---------|
| `bn254` *(default)* / `bn128` | 2188…95617 (254-bit) | circom/snarkjs |
| `babybear` | 2013265921 (15·2²⁷+1) | zirgen |
| `goldilocks` | 18446744069414584321 (2⁶⁴−2³²+1) | plonky2 |
| `mersenne31` | 2147483647 (2³¹−1) | Plonky3 |
| `koalabear` | 2130706433 (2³¹−2²⁴+1) | Plonky3 |

bn254/bn128 + goldilocks primality via `private axiom` in `CLI.lean` (too large for `native_decide`/`norm_num`). CLI-only — never in proof files.

```bash
lake exe hey compile --prime-field babybear circuit.llzk out/system.json
```

## Key invariants — do not break

1. **Must implement `PresReflPass`.** Every pass needs instance with `compile`, `witnessRel`, `preservation`, `reflection`. Use `sorry` if proofs incomplete — instance must exist. Fundamental to correctness framework.
2. **Standard axioms only.** No `axiom` in proof files. CLI `private axiom` OK. Verify: `lean_verify <file> <theorem>` → `propext`, `Classical.choice`, `Quot.sound`.
3. **`lake build` must pass.** 0 errors, 0 warnings (linter warnings OK during development).
4. **Intrinsic well-formedness.** StructIR uses dependent types (`Fin i`, `Fin numMembers`, `noDupReads`). No runtime checks or fuel-based recursion.
5. **Zero sorries.** Fill all `sorry`. Document in comments when temporary or represent open questions.

## Working with Lean files

**Field parameterization:** Pass functions take `(F : Type) [Field F]` explicitly. Examples use `F := ZMod 1993`. Don't hardcode prime. `DecidableEq F`, `IntCast F` for lowering; `Repr F` for JSON.

**Imports:** Minimize — import specific Mathlib modules, not `import Mathlib`.

**New StructIR statement type** — add cases in `StructIR.lean` + `StructIRToStructInlineIR.lean`: `inlineBody`, `expandBody`, `inlineBody_props` (frame + correctness), `inlineBody_frame`, `inlineBody_correct`, `expandBody_correct`, `evalConstrainBody_agree`.

**New FlatIR instruction** — add to `FlatIRToR1CS.compileInstr` (1–2 constraints), then preservation + reflection cases via `r1cs_arith`; fall back to `linear_combination`/`field_simp`. See `docs/tactics.md`.

**Pass 1 proof structure (`StructIRToStructInlineIR.lean`)**:
Key theorem: `expandBody_correct`: source `evalConstrainBody` ↔ target `StructInlineIR.evalConstrainBody` after expansion. `call` case uses:
- `inlineBody_correct` (proved by combined k-bounded strong induction `inlineBody_props`)
- `StructIR.evalConstrainBody_agree` (env-agreement for bounded-variable bodies)
- `inlineBody_frame` (positions < next unchanged after running inlined code)
- `StructInlineIR.evalConstrainBody_append` (splitting evaluation over appended lists)

**Pass 2 open question** (`StructInlineIRToMemberlessIR.lean`):
Compiles `readMember dest self member` → `constrainEq dest (Nat.pair self member)`. Treats `self` as encoded path — only correct if `objEnv self` determined by `self` alone. Semantic gap must resolve before Pass 2 proof. See `docs/WARNING.md` §8.

**Pass 3 proof structure (`MemberlessIRToFlatIR.lean`)**:
Follow `StructIRToFlatIR` pattern: `compileWitness_agrees` invariant (`∀ v, wt (vm v) = env v`), preservation/reflection by joint induction on `(i, stmts.length)`. `call` case inlines callee body.

**Macro hygiene:** Tactics in `Tactics.lean` can't reference names from other files. Pass-specific unfolding at call site, not in tactic.

**Helper lemma extraction:** Can't factor proof code with recursive call to theorem being proved (felt-op cases). Non-recursive obligations can factor (e.g., `preservation_body_peel_binop` pattern).

## Verification checklist

1. `lean_diagnostic_messages <file>` → 0 errors
2. `lake build` → 0 errors, 0 warnings
3. `lean_verify <file> <theorem>` → standard axioms only
4. No `sorry`: `grep -r "sorry" Heyting/` → empty (only comment hits OK)
5. CLI smoke checks as needed (`scripts/smoke_cli.sh`)

## Documentation

| File | When to update |
|------|----------------|
| `docs/GUARANTEES.md` / `docs/languages.md` | Pass behavior, new languages, correctness framework |
| `docs/WARNING.md` | New assumptions, limitations, resolutions |
| `docs/cli.md` | CLI flags, supported fields |
| `docs/llzk-dialects.md` | New LLZK dialects/ops, parser work |
| `docs/ROADMAP.md` | Completing or reprioritizing roadmap items |
| `docs/tactics.md` | New tactics or proof patterns |
| `README.md` | User-facing changes |
