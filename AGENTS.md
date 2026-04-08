# Heyting — Agent Guide

This file is for AI agents (Claude Code, Copilot, Cursor, etc.) working
on this codebase. Read it before making changes.

## What this project is

Heyting is a **formally verified ZKP compiler** in Lean 4 + Mathlib. It
compiles constraint languages (a core fragment of LLZK) down to R1CS
arithmetizations, and proves that compilation is correct — no constraints
are added or lost.

Every theorem has **0 sorries** and **standard axioms only** (`propext`,
`Classical.choice`, `Quot.sound`). Maintaining this invariant is
non-negotiable.

## Build

```bash
lake build          # build everything
```

Requires [elan](https://github.com/leanprover/elan). Lean 4.28.0,
Mathlib v4.28.0.

## Repository layout

```
Heyting/
  Core/
    Language.lean        -- Language typeclass (Program + satisfies)
    Pass.lean            -- Pass, PreservingPass, ReflectingPass, PresReflPass
    TrinitaryCC.lean     -- TPσ ↔ CC~ ↔ TPτ (Abate et al.)
  Languages/
    StructIR.lean        -- Hierarchical IR (structs, calls, felt ops)
    FlatIR.lean          -- Flat instruction list (7 instruction types)
    R1CS.lean            -- Rank-1 Constraint Systems
  Passes/
    StructIRToFlatIR.lean  -- StructIR → FlatIR (largest file, ~1860 lines)
    FlatIRToR1CS.lean      -- FlatIR → R1CS (~220 lines)
    Tactics.lean           -- r1cs_arith, r1cs_unfold_sat macros
  Examples/
    StructIRExamples.lean  -- 4 validated examples with satisfaction proofs
docs/
  GUARANTEES.md    -- Formal guarantees per pass (read this first)
  WARNING.md       -- Assumptions, limitations, resolved issues
  languages.md     -- Language design and semantics
  ROADMAP.md       -- Development roadmap
  tactics.md       -- Tactic documentation
  llzk-dialects.md -- LLZK MLIR dialect reference
  diary.md         -- Chronological session diary
  MATTEO_NOTES.md  -- Author's design notes on compiler correctness
```

## Correctness framework

All passes implement `PresReflPass S T` which bundles:

- **`compile`**: source program → target program
- **`witnessRel`**: relates source and target witnesses (per-program)
- **Reflection (= CC~)**: target satisfiable → source satisfiable
  (soundness; this is trace-relating compiler correctness from Abate et al.)
- **Preservation**: source satisfiable → target satisfiable
  (completeness; additional guarantee beyond CC~)

**CC~ is reflection alone, not preservation + reflection.** Preservation
is a separate property. Together they give equisatisfiability.

See `docs/GUARANTEES.md` for the full formal statements.

## Key invariants — do not break these

1. **Zero sorries.** Every theorem must be fully proved. Never introduce
   `sorry` in committed code. Use `sorry` only as a temporary placeholder
   during development, and replace it before finishing.

2. **Standard axioms only.** No `axiom` declarations, no `native_decide`,
   no `Decidable.decide` on undecidable props. Verify with
   `lean_verify <file> <theorem_name>` — should show only `propext`,
   `Classical.choice`, `Quot.sound`.

3. **`lake build` must pass.** Zero errors, zero warnings (linter
   warnings from Mathlib's `weak.linter` are configured in `lakefile.toml`).

4. **Intrinsic well-formedness.** StructIR uses dependent types to make
   ill-formed programs unrepresentable (`Fin i` for call targets,
   `Fin numMembers` for member access, `noDupReads` on modules). Do not
   add runtime well-formedness checks or fuel-based recursion.

## Working with the Lean files

### Imports

Minimize imports. Do not import `Mathlib` wholesale — import specific
modules (e.g., `Mathlib.Tactic.Ring`, `Mathlib.Tactic.LinearCombination`).
After changing imports, run `lake build` to rebuild.

### Proof patterns in StructIRToFlatIR

The pass proofs use well-founded recursion on `(i, stmts.length)` with
9-way case splits. Key invariants maintained inductively:

- **`WitnessCoherent acc varMap env`**: `∀ v, acc (varMap v) = env v`
- **`VarMapBound varMap next`**: `∀ v, varMap v < next`
- **`0 < next`** and **`acc 0 = 0`**

When adding a new StructIR statement type, you need cases in:
`compileConstrainBody`, `buildWitness`, `buildVarAlloc`,
`evalConstrainBody`, `readPositions`, plus all proof theorems
(`preservation_body`, `reflection_direct`, `reflection_body`,
`compileConstrainBody_instrVars_bounded`, `buildWitness_preserves_below`,
`buildWitness_next_le`, `buildWitness_compileConstrainBody_next`,
`buildVarAlloc_next_eq`, `buildVarAlloc_alloc_bound`,
`buildWitness_varAlloc_agree`, `buildVarAlloc_preserves_absent`,
`buildVarAlloc_acc_irrelevant`).

### Proof patterns in FlatIRToR1CS

When adding a new FlatIR instruction:

1. Add the case to `compileInstr` (1 or 2 R1CS constraints).
2. Add preservation case: unfold + `r1cs_arith`.
3. Add reflection case: unfold + `r1cs_arith`.
4. If `r1cs_arith` fails, close manually with `linear_combination`,
   `ring`, or `field_simp`.

See `docs/tactics.md` for detailed patterns.

### Lean 4 macro hygiene

Lean 4 macro hygiene renames cross-namespace identifiers (e.g.,
`compileInstr` becomes `compileInstr✝`). This means:

- Tactics in `Tactics.lean` cannot reference names from other files.
- Importing `Tactics.lean` into `StructIRToFlatIR.lean` creates `VarMap`
  name collisions. The pass keeps its own `VarMap` type alias.
- Pass-specific unfolding must happen at the call site, not in a tactic.

### Helper lemma extraction

Helper lemmas **cannot** factor out proof code that involves a recursive
call to the theorem being proved. The felt-op cases in `reflection_direct`
and `reflection_body` look identical but each makes a recursive call —
they cannot be extracted into a shared helper.

Non-recursive proof obligations (like the head-case in
`preservation_body`) can be factored out (see
`preservation_body_peel_binop`).

## Verification checklist

After any change to `.lean` files:

1. Check diagnostics: `lean_diagnostic_messages <file>` → 0 errors
2. Full build: `lake build` → 0 errors
3. Axiom check: `lean_verify <file> <theorem>` → standard axioms only
4. No `sorry` in committed code: `grep -r "sorry" Heyting/` → empty

## Documentation

- `docs/GUARANTEES.md` — formal guarantees (theorem statements + proof intuition)
- `docs/languages.md` — language definitions, semantics, pass descriptions
- `docs/tactics.md` — custom tactic documentation
- `docs/ROADMAP.md` — development roadmap
- `docs/WARNING.md` — warnings, assumptions, and known limitations (resolved and active); check here before making design decisions that touch `assignDiv`, `noDupReads`, or `objEnv`
- `docs/llzk-dialects.md` — LLZK MLIR dialect reference (tier 1–3 dialects, op signatures); consult when adding new StructIR statement types or planning parser work
- `docs/diary.md` — chronological session diary; read for context on past decisions and what has already been tried
- `README.md` — project overview

Update relevant docs when making changes:
- `GUARANTEES.md` / `languages.md` — when changing pass behavior, adding languages, or modifying the correctness framework
- `WARNING.md` — when introducing new assumptions, discovering limitations, or resolving existing ones
- `llzk-dialects.md` — when adding support for new LLZK dialects or ops
- `diary.md` — append a session summary at the end of each working session
- `ROADMAP.md` — when completing roadmap items or adjusting priorities
