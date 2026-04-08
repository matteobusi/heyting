# Session Diary

Chronological summaries of working sessions on Heyting.

---

## Session 1 — 2026-04-03

**Goals:** Project onboarding, documentation, LLZK research.

**What we did:**
1. Read the entire codebase (5 source files, all compiling, 0 sorries).
2. Wrote a proper README.md (architecture, build instructions, roadmap). License: MIT.
3. Researched LLZK MLIR dialects thoroughly — cloned the `llzk-lib` repo, cataloged all 13 core dialects + backend dialects. Wrote `docs/llzk-dialects.md` as a reference.
4. Identified incremental path: expand `felt` ops -> `struct` -> `function` -> `array`.
5. Planned and began implementing `assignSub`, `assignNeg`, `assignDiv` in FlatIR with R1CS compilation proofs.
6. Documented the `assignDiv` reflection limitation in `docs/WARNING.md`.

**Current state:** Expanding FlatIR with new felt operations and proving the extended pass correct.

---

## Session 2 — 2026-04-03

**Goals:** Complete preservation and reflection proofs for the multi-constraint FlatIR-to-R1CS pass.

**What we did:**
1. Fixed all remaining proof errors in `FlatIRToR1CS.lean` after the multi-constraint refactor (`compileInstr` returning `List (Constraint F)`, `compileProgram` using `flatMap`).
2. Completed the `assignDiv` reflection proof — the two-constraint encoding (`src2 * dest = src1` + `src2 * aux = 1`) now fully proves both `src2 ≠ 0` and `dest = src1 * src2⁻¹`.
3. Key proof patterns discovered:
   - For sub/neg cases: `ring_nf at h_all; exact h_all.symm` handles the `-` vs `+ -1 *` mismatch.
   - For mul: after simp, `h_all` is a conjunction; use `.1` to extract the constraint equation.
   - For div: destructure with `obtain ⟨h_c1, h_c2, _⟩`, only `rw [h_one]` on `h_c2` (the one with `varOne`), then `field_simp` to clear the inverse.
   - `linarith` doesn't work on general fields (needs ordered rings); use `linear_combination`, `ring_nf + exact`, or `simp_all` instead.
4. Verified: 0 errors, 0 sorries, only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
5. Updated `docs/WARNING.md` — marked the `assignDiv` reflection limitation as resolved.

**Current state:** FlatIR-to-R1CS pass is fully verified for all 7 instruction types. Ready to extend with structs/functions or target more LLZK dialects.

---

## Session 3 — 2026-04-03

**Goals:** Define StructIR language (structs + functions + felt) as the higher-level IR above FlatIR.

**What we did:**
1. Studied LLZK's `struct` and `function` dialects in depth via `llzk-lib/test/Transforms/InlineStructs/` — analyzed how flattening and inlining work on nested struct hierarchies.
2. Decided on architecture: `StructIR → FlatIR → R1CS`, with StructIR capturing the full hierarchy (multi-struct modules with nesting, `@compute` and `@constrain` functions, cross-struct calls).
3. Initial implementation used fuel-bounded recursion for cross-struct calls. Identified that this was unsound (silent `True` on fuel exhaustion).
4. Refactored to **intrinsic well-formedness** via dependent types:
   - Structs indexed `0..n-1` in topological order (leaves first, main last)
   - `call` targets typed `Fin i` — callee index must be < current struct index
   - Members indexed by `Fin numMembers` — invalid member access unrepresentable
   - `evalConstrainBody` terminates by structural recursion on `(i, stmts.length)` — no fuel
   - `Module` is a dependent function `(i : Fin n) → StructDef n i F`
5. Created `Heyting/Examples/StructIRExamples.lean` with encodings of LLZK test cases.
6. Decided: non-native field ops (pow, bitwise) are not worth formalizing now — real LLZK circuits use only field-native ops.
7. Verified: `lake build` passes, 0 errors, 0 sorries across all files.

**Current state:** StructIR types and semantics defined and validated with examples. Next: implement the `StructIR → FlatIR` pass (inlining + flattening) with `CorrectPass` proof.

---

## Session 4 — 2026-04-03

**Goals:** Implement the StructIR → FlatIR compilation pass.

**What we did:**
1. Created `Heyting/Passes/StructIRToFlatIR.lean` — full compilation pass with counter-based fresh variable allocation.
2. Key design: each felt op/readMember gets a unique FlatIR variable ID from a monotonically increasing counter.
3. Proved 5 helper lemmas and 8 of 9 statement cases in `preservation_body`.

**Remaining sorries (3):** `preservation_body` call case, `CorrectPass.preservation`, `CorrectPass.reflection`.

**Current state:** StructIR → FlatIR pass compiles, validated on examples. Proofs ~80% complete. 3 sorries remain.

---

## Session 5 — 2026-04-03

**Goals:** Complete remaining proofs in the StructIR → FlatIR pass.

**What we did:**
1. Proved the `preservation_body` call case. Added `0 < next` and `acc 0 = 0` as tracked invariants.
2. Proved `CorrectPass.preservation` fully.
3. Implemented `reflection_body` — 8 of 10 cases proved.

**Current state:** Preservation fully verified (0 sorry). Reflection: 2 sorry (readMember coherence + initial coherence).

---

## Session 6 — 2026-04-04

**Goals:** Redesign correctness framework following Abate et al.; eliminate remaining sorries.

**What we did:**
1. Redesigned `CorrectPass` — removed `extractWitness`, reflection now takes `compileWitness(w)` not arbitrary target witness.
2. Adapted both passes. New `reflection_body` uses `flatW = buildWitness(...)` — both sorries resolved by construction.
3. Verified: 0 errors, 0 sorries, standard axioms only across entire pipeline.

**Current state:** Entire StructIR → FlatIR → R1CS pipeline fully verified. 0 sorry across all files.

---

## Session 7 — 2026-04-07

**Goals:** Meaningful witnessRel and complete PresReflPass proof with relational witness.

**What we did:**
1. Identified that `witnessRel = True` breaks reflection — any satisfiable target yields unrelated source witness.
2. Designed meaningful `witnessRel`: `∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)`.
3. Added `readPositions` function and `noDupReads : Nodup` field to `StructIR.Module`.
4. Wrote `reflection_direct` theorem: proves `evalConstrainBody` using `wt` directly.
5. Fixed `compileProgram` to emit zero-initialization constraints.

**Current state:** 2 sorry remain (`buildVarAlloc_preserves_absent`, `reflection_direct`).

---

## Session 8 — 2026-04-07

**Goals:** Complete remaining 2 sorries; optimize compilation; update documentation.

**What we did:**
1. Proved `buildVarAlloc_preserves_absent` and `reflection_direct`.
2. Added helper `buildVarAlloc_acc_irrelevant`.
3. Optimized: minimized imports, removed all 13 `set_option maxHeartbeats`, fixed all ~35 linter warnings.
4. Updated `Core/Pass.lean` framework with separate `PreservingPass`, `ReflectingPass`, `PresReflPass` classes.

**Current state:** Full pipeline verified with meaningful `witnessRel`. 0 sorry, 0 warnings.

---

## Session 9 — 2026-04-07

**Goals:** Fix readMember/objEnv semantic bug for nested struct support.

**What we did:**
1. Fixed `readMember` case in 4 functions to update `objEnv` with `objEnv.update dest (path ++ [member.val])`:
   - `evalConstrainBody`, `readPositions` in `StructIR.lean`
   - `buildWitness`, `buildVarAlloc` in `StructIRToFlatIR.lean`
2. Restructured `readPositions` from `let` bindings to direct case-split (Lean's `unfold`/`simp` with `let` bindings in recursive functions is unreliable).
3. Fixed all affected proofs (~8 lemmas in StructIRToFlatIR.lean).
4. Added nested struct example (Component1A + Wrapper) with noDupReads, positive and negative satisfaction proofs, and compilation output.
5. Verified: 0 errors, 0 sorries, standard axioms only, full build passes.

**Current state:** Nested struct semantics fully correct. 4 examples verified. 0 sorry, 0 warnings.

---

## Session 10 — 2026-04-07

**Goals:** Update docs, proof engineering (custom tactics), roadmap.

**What we did:**
1. Updated all docs (`languages.md`, `WARNING.md`, `diary.md`, `MATTEO_NOTES.md`, `llzk-dialects.md`, `README.md`) to reflect current state after Session 9.
2. Analyzed proof patterns across both passes — identified 8 recurring patterns.
3. Created `Heyting/Core/Tactics.lean` with generic proof helpers:
   - `witnessCoherent_update_generic` — unifies the 6 per-operation coherence update lemmas
   - `witnessCoherent_update_binop` / `witnessCoherent_update_unop` — convenience wrappers for binary/unary ops
   - `varMapBound_update`, `varMapBound_succ`, `poz_succ`, `acc_zero_update` — counter/bound maintenance
   - `VarMap.update_self/ne`, `LocalEnv.update_self'/ne'` — `@[simp]` lemmas for environment updates
4. Created `docs/ROADMAP.md` with detailed 6-phase plan: proof engineering → practical I/O (parser + R1CS output) → language extensions (arrays) → optimization passes → verified backend → paper.
5. All 0 axioms on new theorems. Full build passes (3112 jobs, 0 errors).

**Current state:** Docs fully up-to-date. Tactics file provides generic proof infrastructure for future passes. Roadmap charts path to practical use.
