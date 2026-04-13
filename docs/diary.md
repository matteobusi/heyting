# Session Diary

Chronological summaries of working sessions on Heyting.

---

## Sessions 1–12 — 2026-04-03 to 2026-04-08 (archived)

Brief summary of what was established:

- **S1–2:** FlatIR extended (add/sub/mul/div/neg/const), FlatIR→R1CS pass fully verified (0 sorry, standard axioms). `assignDiv` two-constraint encoding (forces src2 invertible).
- **S3:** StructIR defined with intrinsic well-formedness (dependent types, no fuel). Structs indexed topologically; `call` restricted to `Fin i`.
- **S4–5:** StructIR→FlatIR pass implemented and preservation proved. Reflection 80% done.
- **S6:** Correctness framework redesigned following Abate et al. (CC~). 0 sorries across full pipeline.
- **S7–8:** Meaningful `witnessRel` (`∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)`). Added `readPositions`/`noDupReads`. `reflection_direct` proved. Moved to `PresReflPass`. 0 warnings.
- **S9:** Fixed `readMember`/`objEnv` semantic bug for nested structs. Updated 4 functions + ~8 proof lemmas. Added Wrapper+Component1A example.
- **S10:** Docs updated. Created `Heyting/Passes/Tactics.lean` (`r1cs_arith`, `r1cs_unfold_sat`, generic coherence helpers). Created `docs/ROADMAP.md`.
- **S11:** Optimized Mathlib imports. LLZK parser (`Parser/AST`, `Tokenizer`, `Parser`, `Main`) on `feature/llzk-parser`. Tested on 5 real LLZK files.
- **S12:** AST → StructIR lowering (`Passes/Lowering.lean`): topo sort, SSA map, `noDupReads` check. Full pipeline LLZK→StructIR→FlatIR→R1CS working. `LoweringExamples.lean` added.

---

## Session 13 — 2026-04-10

**Goals:** Phase 2b — JSON output backend + CLI entry point.

**What we did:**
1. Created `Heyting/Backends/R1CSJSON.lean` — `varIdToJson`, `linCombToJson`, `constraintToJson`, `systemToJson`, `saveR1CSJson`, `SystemSummary`, `summarize`.
2. Created `Heyting/CLI.lean` — `compileToJson` (full pipeline), `parseArgs`, `runCommand`, `main`. Initially used `ZMod 1993` as default field.
3. Created `Heyting/Examples/OutputExamples.lean` — two `#eval` examples (emit_pass.llzk → 4 constraints, circom_isZero.llzk → 10 constraints).
4. Created `Heyting/Test/R1CSJSONTest.lean` — unit tests for `summarize` and `systemToJson`.
5. Full `lake build` passes: 0 errors, 0 warnings.

**Design decisions:** `SystemSummary F` without typeclass constraints in structure header. `set_option linter.style.nativeDecide false` for `Nat.Prime 1993`.

---

## Session 14 — 2026-04-13

**Goals:** Multi-field CLI support matching `llzk-lib/lib/Util/Field.cpp`; documentation update.

**What we did:**
1. Refactored `Heyting/CLI.lean` — `compileToJson` now generic: `(F : Type) [Field F] [DecidableEq F] [IntCast F] [Repr F] (fieldName : String)`. Added `--prime-field` dispatch for 6 fields: bn254 (default)/bn128, babybear, goldilocks, mersenne31, koalabear. `private axiom` for bn254/bn128/goldilocks primality.
2. Added `prime? : Option String` to `Heyting/CLIArgs.lean`.
3. Fixed `Heyting/Examples/OutputExamples.lean` — replaced nonexistent `compileToJsonZ1993` with `compileToJson (F := ZMod p) "F1993"`.
4. Rewrote `AGENTS.md` — updated layout, field parameterization section, `private axiom` policy.
5. Updated all docs: `README.md`, `docs/cli.md`, `docs/WARNING.md` (§7), `docs/GUARANTEES.md`, `docs/languages.md`, `docs/ROADMAP.md`.
6. Full `lake build`: 1182 jobs, 0 errors, 0 warnings.

**Axiom policy:** All 6 CLI fields use `private axiom` in `CLI.lean` only. Pass proofs unaffected.
