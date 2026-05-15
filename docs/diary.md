# Session Diary

Working session summaries for Heyting.

---

## Sessions 1–12 — 2026-04-03 to 2026-04-08 (archived)

Brief summary:

- **S1–2:** FlatIR extended (add/sub/mul/div/neg/const), FlatIR→R1CS fully verified (0 sorry, standard axioms). `assignDiv` two-constraint encoding (forces src2 invertible).
- **S3:** StructIR with intrinsic well-formedness (dependent types, no fuel). Structs topologically indexed; `call` restricted to `Fin i`.
- **S4–5:** StructIR→FlatIR pass, preservation proved. Reflection 80%.
- **S6:** Correctness framework redesigned per Abate et al. (CC~). 0 sorries across pipeline.
- **S7–8:** Meaningful `witnessRel` (`∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)`). Added `readPositions`/`noDupReads`. `reflection_direct` proved. Moved to `PresReflPass`. 0 warnings.
- **S9:** Fixed `readMember`/`objEnv` semantic bug for nested structs. 4 functions + ~8 proof lemmas updated. Wrapper+Component1A example added.
- **S10:** Docs update. `Heyting/Passes/Tactics.lean` created (`r1cs_arith`, `r1cs_unfold_sat`, coherence helpers). `docs/ROADMAP.md` created.
- **S11:** Optimized Mathlib imports. LLZK parser (`Parser/AST`, `Tokenizer`, `Parser`, `Main`) on `feature/llzk-parser`. Tested on 5 real LLZK files.
- **S12:** AST → StructIR lowering (`Passes/Lowering.lean`): topo sort, SSA map, `noDupReads` check. Full LLZK→StructIR→FlatIR→R1CS pipeline working. `LoweringExamples.lean` added.

---

## Session 13 — 2026-04-10

**Goals:** Phase 2b — JSON output backend + CLI entry point.

**Done:**
1. `Heyting/Backends/R1CSJSON.lean` — `varIdToJson`, `linCombToJson`, `constraintToJson`, `systemToJson`, `saveR1CSJson`, `SystemSummary`, `summarize`.
2. `Heyting/CLI.lean` — `compileToJson` (full pipeline), `parseArgs`, `runCommand`, `main`. Default `ZMod 1993`.
3. `Heyting/Examples/OutputExamples.lean` — 2 `#eval` examples (emit_pass.llzk → 4 constraints, circom_isZero.llzk → 10).
4. `Heyting/Test/R1CSJSONTest.lean` — unit tests for `summarize` and `systemToJson`.
5. `lake build`: 0 errors, 0 warnings.

**Decisions:** `SystemSummary F` without typeclass constraints in structure header. `set_option linter.style.nativeDecide false` for `Nat.Prime 1993`.

---

## Session 14 — 2026-04-13

**Goals:** Multi-field CLI support matching `llzk-lib/lib/Util/Field.cpp`; docs update.

**Done:**
1. Refactored `Heyting/CLI.lean` — `compileToJson` generic: `(F : Type) [Field F] [DecidableEq F] [IntCast F] [Repr F] (fieldName : String)`. `--prime-field` dispatch for 6 fields: bn254 (default)/bn128, babybear, goldilocks, mersenne31, koalabear. `private axiom` for bn254/bn128/goldilocks primality.
2. `prime? : Option String` to `Heyting/CLIArgs.lean`.
3. Fixed `Heyting/Examples/OutputExamples.lean` — replace nonexistent `compileToJsonZ1993` with `compileToJson (F := ZMod p) "F1993"`.
4. Rewrote `AGENTS.md` — updated layout, field parameterization, `private axiom` policy.
5. Updated all docs: `README.md`, `docs/cli.md`, `docs/WARNING.md` (§7), `docs/GUARANTEES.md`, `docs/languages.md`, `docs/ROADMAP.md`.
6. `lake build`: 1182 jobs, 0 errors, 0 warnings.

**Axiom policy:** All 6 CLI fields use `private axiom` in `CLI.lean` only. Pass proofs unaffected.

---

## Session 15 — 2026-04-13

**Goals:** Witness generation — interpret `@compute` bodies to produce StructIR witnesses.

**Done:**
1. `Heyting/Core/ComputingLanguage.lean` — `ComputingLanguage` typeclass extending `Language` with `Input : Type` and `computeWitness : Program → Input → Option (Witness V F)`. Returns `Option` for div-by-zero.
2. Added to `Heyting/Languages/StructIR.lean`:
   - `ComputeState F` — interpreter state: `env`, `objEnv`, `acc` (witness accumulator), `nextPath` (for `newStruct`).
   - `evalComputeBody` — definitional interpreter for `ComputeStmt` lists. Termination by `(i, stmts.length)`, matching `evalConstrainBody`. `feltDiv` returns `none` on zero divisor; `writeMember` updates witness accumulator; `newStruct` allocates fresh `InstancePath`s; `call` recurses and merges callee state.
   - `initComputeState` — initial state from `List F` of public inputs.
   - `computeWitness` — top-level: runs `evalComputeBody` on main struct, returns `some acc` or `none`.
   - `computeWitnessCorrect` — correctness stub (`sorry`): `computeWitness m inputs = some w → satisfies w m`. Open.
   - `ComputingLanguage` instance for StructIR (`Input := List F`, requires `[DecidableEq F]`).
3. Updated `Heyting/CLI.lean` — `--auto` flag implemented: calls `computeWitness`, writes `<output>.witness.json`. Full witness serialization (through `compileWitness`) left as follow-up.
4. Fixed `Heyting/Examples/OutputExamples.lean` — `compileToJson` call passes `false` for `autoWitness`.
5. Updated `docs/GUARANTEES.md` — §Witness generation documenting `ComputingLanguage`, `evalComputeBody`, `computeWitnessCorrect`, interpreter composition with `PresReflPass` chain.
6. `lake build`: 1183 jobs, 0 errors, 0 warnings (1 expected sorry warning on `computeWitnessCorrect`).

**Decisions:**
- `ComputingLanguage` separate typeclass (not merged into `Language`) to keep `Language` minimal. Only StructIR implements.
- `newStruct` uses `nextPath : Nat` counter in `ComputeState` for fresh `InstancePath`s (`[nextPath]`). Counter starts at 1 (0 reserved for root `self` at path `[]`).
- `call` in compute merges callee's `acc` and `nextPath` into caller's state (callee writes visible to caller, matching LLZK).
- `computeWitnessCorrect` is only `sorry` in codebase. Structurally analogous to `preservation_body` in `StructIRToFlatIR` but compute→constrain direction. Proof strategy: induction on statement lists maintaining coherence invariant between `ComputeState.acc` and `evalConstrainBody` witness access.

---

## Session 16 — 2026-04-13

**Goals:** `Heyting/Passes/Pipeline.lean` — composed `PresReflPass` and end-to-end witness chain StructIR→R1CS.

**Done:**
1. Created `Heyting/Passes/Pipeline.lean`:
   - `compileProgram` — composes `StructIRToFlatIR.compileProgram` + `FlatIRToR1CS.compileProgram`.
   - `compileWitnessFlat` — wrapper around `StructIRToFlatIR.compileWitness` with canonical initial state (same as `preservation`). Returns `FlatIR.Witness F`.
   - `compileWitness` — chains `compileWitnessFlat` + `FlatIRToR1CS.compileWitness` → `R1CS.Witness F` from `StructIR.Witness F`.
   - `extractWitness` — backward: `R1CS.Witness F → StructIR.Witness F`.
   - `witnessRel` — composed: ∃ intermediate FlatIR witness related by both sub-pass relations.
   - `CorrectPass` — `PresReflPass (StructIR.Language n F) (R1CS.Language F)` instance. Preservation + reflection by 2-step composition. Standard axioms only.
   - `pipelineWitness` — chains `StructIR.computeWitness` + `compileWitness` → `Option (R1CS.Witness F)` from public inputs.
   - `pipelineWitnessCorrect` — correctness theorem (sorry, from `StructIR.computeWitnessCorrect`).
2. Updated `Heyting/CLI.lean`:
   - `import Heyting.Passes.Pipeline`.
   - `compileToJson` calls `Pipeline.compileProgram` (single step) instead of manual chain.
   - `--auto` calls `Pipeline.pipelineWitness`, obtains `R1CS.Witness F`. Placeholder JSON updated.
3. `lake build`: 1184 jobs, 0 errors, 0 warnings. Sorries: 2 (`StructIR.computeWitnessCorrect`, `Pipeline.pipelineWitnessCorrect`).
4. `lean_verify Pipeline.CorrectPass` → standard axioms only.

**Decisions:**
- `pipelineWitnessCorrect` kept as sorry instead of indirect proof through existential `preservation`. Requires unfolding preservation proof construction to equate existentially-produced witness with `compileWitnessFlat m ws`. Trivial once `computeWitnessCorrect` filled.
- `compileWitnessFlat` uses same let-bindings (`initVarMap`, `initNext`, `initObjEnv`) as `preservation` proof in `StructIRToFlatIR` for definitional equality.

---

## Session 17 — 2026-04-13

**Goals:** Close sorries — add `Pipeline.compileWitnessCorrect`, remove stale `pipelineWitnessCorrect`/`computeWitnessCorrect`.

**Done:**
1. Added `Pipeline.compileWitnessCorrect` to `Heyting/Passes/Pipeline.lean`:
   - Statement: `StructIR.satisfies ws m → R1CS.satisfies (compileWitness m ws) (compileProgram m)`
   - Proof: 2-step, no sorries, standard axioms.
     - **Step 1** (StructIR→FlatIR): replicate `StructIRToFlatIR.preservation` argument using `preservation_body` + `compileWitness_preserves_below`. Names concrete witness `compileWitnessFlat m ws`.
     - **Step 2** (FlatIR→R1CS): inline `FlatIRToR1CS.preservation` — per-instruction case split + `r1cs_arith` — applied to `compileWitness m ws` directly.
   - Axioms: `propext`, `Classical.choice`, `Quot.sound`.
2. Removed `pipelineWitnessCorrect` from `Pipeline.lean`. Module docstring updated.
3. Removed `computeWitnessCorrect` and `### Soundness stub` from `Heyting/Languages/StructIR.lean`. Note: `computeWitnessCorrect` is semantic property about specific interpreter — not provable from types alone. Correct statement is `Pipeline.compileWitnessCorrect` (compilation direction, provable from existing lemmas).
4. Updated `Heyting/Core/ComputingLanguage.lean` docstring — references to `computeWitnessCorrect` replaced with `Pipeline.compileWitnessCorrect`.
5. Fixed line-length lint warning (>100 chars) in `ComputingLanguage` docstring.
6. `lake build`: 1184 jobs, 0 errors, 0 warnings. Zero sorries.

**Invariants:**
- Zero sorries: `grep -r "sorry" Heyting/` → empty (only comment in `Lowering.lean`).
- `Pipeline.compileWitnessCorrect` verified `lean_verify`.
- `pipelineWitness` (runtime) kept in `Pipeline.lean`, used by `CLI.lean --auto`.

---

## Session 18 — 2026-04-13

**Goals:** Thread `{llzk.pub}` I/O wire distinction through full pipeline: Parser→AST→StructIR→R1CS→JSON.

**Done:**
1. **`Parser/AST.lean`** — `isPublic : Bool` field on `LLZK.MemberDecl`. Docstring updated.
2. **`Parser/Parser.lean`** — Replaced silent `skipAttributes` in `parseMemberDecl` with:
   - `scanBracesForPub` (private, partial): scans tokens inside `{ ... }` for `.keyword "llzk.pub"`.
   - `parseIsPub : Parser Bool`: `true` iff `{llzk.pub}` attribute block present.
   - `skipAttributes` redefined as thin wrapper over `parseIsPub`.
   - `parseMemberDecl` sets `isPublic ← parseIsPub`, stores in AST node.
3. **`Languages/StructIR.lean`** — `isPublic : Bool` on `StructIR.MemberDecl`. No theorem changes (no proof destructs `MemberDecl`).
4. **`Languages/R1CS.lean`** — `numPublicInputs : Nat` on `R1CS.System`. `R1CS.satisfies` untouched.
5. **`Passes/Lowering.lean`** — `lowerMembers` threads `m.isPublic` into `StructIR.MemberDecl`.
6. **`Passes/FlatIRToR1CS.lean`** — `compileProgram` gets optional `numPublicInputs : Nat := 0` (default 0). `PresReflPass` instance uses default, proofs unaffected.
7. **`Passes/Pipeline.lean`** — `compileProgram` computes `numPub` from main struct's `isPublic` members via `List.countP`, struct-update syntax `{ (FlatIRToR1CS.compileProgram ...) with numPublicInputs := numPub }`. All proofs compile unchanged (`R1CS.satisfies` never inspects `numPublicInputs`).
8. **`Backends/R1CSJSON.lean`** — `SystemSummary` and `summarize` include `numPublicInputs`. `summaryToJson` emits `"numPublicInputs"`. `ppSystem` header shows public inputs.
9. **`Examples/StructIRExamples.lean`** — All `StructIR.MemberDecl` constructions updated to `isPublic := false`.
10. **`Test/R1CSJSONTest.lean`** — `dummySys` updated with `numPublicInputs := 0`.

**Invariants:** Zero sorries. Standard axioms only. `lake build`: 1186 jobs, 0 errors, 0 new warnings.

---

## Session 20 — 2026-04-14

**Goals:** Separate tests from `lake build` — tests run only via `lake exe tests`.

**Done:**
1. **`Heyting.lean`** — Removed `Heyting.Examples.*` and `Heyting.Test.*` imports. Barrel covers only verified library (languages, passes, backends, CLI).
2. **`Heyting/Test/Main.lean`** (new) — Entry point for `tests` executable. Imports all test/example modules; `main = pure ()`. `#eval` blocks in those modules fire at elaboration time.
3. **`lakefile.toml`** — Added `[[lean_exe]] name = "tests" root = "Heyting.Test.Main"`. `defaultTargets` remains `["Heyting"]` — `lake build` never touches tests.

**Verification:**
- `lake build` → 1183 jobs, 0 errors, 0 new warnings (pre-existing `longLine` warning in `StructIRToFlatIR.lean` unchanged).
- `lake exe tests` → all `#eval` blocks pass: 3 R1CS JSON, 13 InputJSON, 4 StructIR examples, 5 parser, 3 lowering, 2 output.

**Invariants:** Zero sorries, standard axioms. `lake build` = library+CLI only; tests opt-in.

---

## Session 21 — 2026-05-05

**Goals:** Additive deterministic checked-execution semantics layer, equivalence to `satisfies` for 1 language, Pass 3 stuttering-simulation scaffolding.

**Done:**
1. **Core checked semantics** `Heyting/Core/CheckedSemantics.lean`:
   - `Result Step := success trace | failure checkedPrefix failed`
   - `Result.prepend`, `Result.appendPrefix`, `Result.seq`
   - simulation: `TraceStutter`, `BiTraceStutter`, `ResultRel`.
2. **FlatIR checked executor** `Heyting/Languages/FlatIRChecked.lean`:
   - `checkStep` checks 1 instruction deterministically.
   - `evalChecked` left-to-right, returns success trace or first failure with checked prefix.
   - `checkedSuccess` (`evalChecked w prog = .success prog`).
3. **Equivalence bridge for FlatIR**:
   - `evalChecked_success_iff_satisfies`
   - `checkedSuccess_iff_satisfies`
   - corollaries `checkedSuccess_of_satisfies`, `satisfies_of_checkedSuccess`.
4. **Pass 3 checked-simulation scaffold** `Heyting/Passes/MemberlessIRToFlatIRChecked.lean`:
   - source/target checked-step/trace aliases
   - step relation shape for statement/instruction classes
   - `checkedTraceRel`, `forwardSimulationStatement`, `backwardSimulationStatement` signatures
   - base lemmas: `checkedTraceRel_nil`, `stepRel_feltAdd_assignAdd`.
5. **Integrated into barrel** (`Heyting.lean`) with additive imports; no existing pass/pipeline proof interfaces changed.

**Verification:**
- Targeted builds: `lake build Heyting.Core.Pass`, `Heyting.Languages.FlatIR`, `Heyting.Passes.MemberlessIRToFlatIR`, `Heyting.Languages.FlatIRChecked`, `Heyting.Passes.MemberlessIRToFlatIRChecked`.
- Final: `lake build` passed.

**Impact:** Pass sorries unchanged (1: 2, 2: 4, 3: 3). No new axioms. No theorem changes in existing files.

**Follow-up (same day):** Removed `call` from `MemberlessIR.Stmt`. Updated `MemberlessIR` semantics, `MemberlessIRToFlatIR` compilation/witness helpers, docs (`README.md`, `AGENTS.md`, `docs/languages.md`, `docs/GUARANTEES.md`, `docs/PASS3_PRESERVATION_ROADMAP.md`). MemberlessIR now intrinsically call-free.

---

## Session 19 — 2026-04-14

**Goals:** R1CS witness JSON output — close placeholder gap in `CLI.lean`. Planning: wire-index layout, `var`/`aux` namespace separation, JSON witness array first format, `.wtns` binary deferred.

**Done:**
1. **`Backends/R1CSJSON.lean`** — Fixed `var`/`aux` namespace conflation in `countVars`:
   - `countRegVars` (`.var n` only), kept `countAuxVars`.
   - `countVars` = `1 + countRegVars + countAuxVars` (total wires including `varOne`).
   - `SystemSummary`: `numRegVars` and `numAuxVars` separate (dropped ambiguous `numVars`).
   - `summaryToJson` emits `"numWires"`, `"numRegVars"`, `"numAuxVars"`, `"numPublicInputs"`.
   - `ppSystem` shows `N wires (R regular, A aux)`.
2. **`Backends/WireAssignment.lean`** (new):
   - `WireAssignment.Sizes` — `numRegVars`, `numAuxVars`.
   - `Sizes.numWires` = `1 + numRegVars + numAuxVars`.
   - `fromConstraints` / `fromSystem` — build `Sizes` by scanning constraints.
   - `encode : Sizes → VarId → Nat` — `varOne ↦ 0`, `var n ↦ n+1`, `aux n ↦ numRegVars+1+n`.
   - `decode : Sizes → Nat → Option VarId` — inverse within range.
   - Future: `encode_injective`, `decode_encode`.
3. **`Backends/WitnessJSON.lean`** (new):
   - `witnessToArray wa w` — maps wire index `i` to `w (decode wa i)` for `i` in `0..numWires-1`.
   - `witnessToJson wa w` — JSON `{ "numWires": n, "witness": ["f0", "f1", ...] }`.
   - `systemWitnessToJson sys w` — derives wire assignment from `sys`.
   - `saveWitnessJson sys w path` — writes file.
4. **`CLI.lean`** — `import Heyting.Backends.WitnessJSON`. Replaced placeholder stub with `WitnessJSON.saveWitnessJson r1csSystem wr witnessPath`.
5. **`Test/R1CSJSONTest.lean`** — Updated to match new `SystemSummary` fields.

**Wire layout (documented in `WireAssignment.lean`):**
```
index 0                         → varOne
index 1 .. numRegVars           → var 0 .. var (numRegVars-1)
index numRegVars+1 .. total-1   → aux 0 .. aux (numAuxVars-1)
```

**Verifiability notes:**
- Verified chain: `StructIR.satisfies ws m → R1CS.satisfies (compileWitness m ws) (compileProgram m)` [proved, S17]. New serializer adds unverified IO layer.
- `encode`/`decode` injectivity theorems future targets in `WireAssignment.lean`.
- `lowering` gap (LLZK→StructIR) is genuine unverified interface; `evalComputeBody` is ground truth for `@compute` semantics.

**Invariants:** Zero sorries. Standard axioms. `lake build`: 1188 jobs, 0 errors, 0 warnings.

---

## Session 21 — 2026-04-14

**Goals:** Circom binary output — `.r1cs` and `.wtns` formats.

**Done:**
1. **`Backends/FieldBytes.lean`** — `FieldBytes` typeclass: `fieldSize : Nat`, `toLeBytes : F → ByteArray`, `primeLeBytes : ByteArray`. LE helpers: `u32LE`, `u64LE`, `natLeBytes`, `sectionHeader`, `fileHeader`. `set_option linter.dupNamespace false in`.
2. **`Backends/R1CSBinary.lean`** (new) — Circom `.r1cs`:
   - `linCombBytes` — sort by wire index, write `[nTerms][wireId || coeff]` per term.
   - `constraintBytes` — A, B, C in sequence.
   - `headerSectionBody` — fieldSize, prime, nWires, nPubOut=0, nPubIn, nPrvIn, nLabels, mConstraints.
   - `constraintsSectionBody`, `wire2LabelSectionBody` (identity map).
   - `systemToBinary` — 3 sections with framing; `saveR1CSBinary` writes file.
3. **`Backends/WitnessBinary.lean`** (new) — Circom `.wtns`:
   - `headerSectionBody` — n8, prime, nWitness.
   - `dataSectionBody` — dense array via `WitnessJSON.witnessToArray`, each element LE-encoded.
   - `witnessToBinary` — 2 sections; `saveWitnessBinary` writes file.
4. **`CLI.lean`** — `import Heyting.Backends.R1CSBinary`, `WitnessBinary`. `private instance : FieldBytes (ZMod P)` for all 6 fields. Renamed `compileToJson` → `compileAndSave`, `useJson : Bool`. Default: `.r1cs` binary (+ `.wtns` if witness requested). `--json` flag writes JSON.
5. **`Examples/OutputExamples.lean`** — Updated to `compileAndSave` with `useJson := true`; `FieldBytes (ZMod 1993)` instance (2-byte elements).
6. **`Test/BinaryTest.lean`** (new) — 7 `#eval` checks: `.r1cs` magic/version/nSections, `.r1cs` 145 bytes (1-constraint, 3-var, fieldSize=1), `.wtns` magic/version/nSections, `.wtns` 49 bytes, `natLeBytes`/`u32LE`/`u64LE` correctness.
7. **`Test/Main.lean`** — `import Heyting.Test.BinaryTest`.
8. **`Heyting.lean`** — `FieldBytes`, `R1CSBinary`, `WitnessBinary` added to barrel.

**Verification:** `lake build`: 1186 jobs, 0 errors, 0 warnings. `lake exe tests`: 23 checks pass (16 existing + 7 binary). Zero sorries. Standard axioms.

---

## Session 17 — 2026-04-15

**Goals:** Continue 3-pass pipeline refactor (StructIR → MemberlessIR → FlatIR → R1CS). Fix wrong-witness bug (`[1,0,0,0,6,6]`).

**Done:**
1. Fixed `LoweringExamples.lean` — stale `StructIRToFlatIR.compileProgram` → `Pipeline.compileProgram (F := F)`. Removed unused `import Heyting.Passes.FlatIRToR1CS`.
2. Cleaned `CLI.lean` — removed stale `import Heyting.Passes.StructIRToFlatIR` and `FlatIRToR1CS` (CLI already used `Pipeline`).
3. Deleted `Heyting/Passes/StructIRToFlatIR.lean` (1863 lines). Updated `Heyting.lean` barrel — remove import, add `Heyting.Passes.Pipeline`.
4. `lake build`: 0 errors, 5 expected sorry warnings (4 in new passes, 1 in Pipeline's reflection sorry-chain).
5. **Diagnosed wrong-witness root cause** — 2 bugs:
   - **Bug A**: `initComputeState` seeded `acc([], k) = inputs[k]` at compute-param positions, but `satisfies` reads via constrain-param indices. `@constrain(%self, %a, %b)` expects `a` at `w([], 1)`, `b` at `w([], 2)`, while `@compute(%a, %b)` stored at `([], 0)`, `([], 1)`. Offset `constrain.numParams − compute.numParams` = 1 missing.
   - **Bug B**: `StructIRToMemberlessIR.compileModuleWitness` initialized accumulator `fun _ => 0` — param slots never explicitly written, appeared as 0 in MemberlessIR witness.
6. Fixed `StructIR.initComputeState` — now takes `paramOffset : Nat`, seeds `acc([], slot)` only when `slot ≥ paramOffset`, using `inputs[slot - paramOffset]`. `computeWitness` computes `offset = constrain.numParams - compute.numParams`.
7. Fixed `StructIRToMemberlessIR.compileModuleWitness` — initial accumulator pre-seeded: `initAcc k = if k < constrain.numParams then ws([], k) else 0`.
8. **Verified fix** — `hey compile --json --input input.json multiply.llzk out/multiply` produces `["1", "6", "2", "3", "6"]` (out=6, a=2, b=3, ab=6), satisfies both R1CS constraints:
   - `(a=2) * (b=3) = (ab=6)` ✓
   - `(out=6) * 1 = (ab=6)` ✓

**Remaining:** 4 sorries in `StructIRToMemberlessIR.lean` and `MemberlessIRToFlatIR.lean` (preservation + reflection passes 1 and 2).

---

## Session 22 — 2026-04-29

**Goals:** Fill sorries. Consolidate WIP from `.worktrees/`.

**Done:**
1. **Worktree consolidation.** Two feature worktrees — `.worktrees/struct-inline-pipeline-refactor` (uncommitted, 1 sorry left) and `.worktrees/inline-first-pipeline` (older, more sorries). Selected former as canonical WIP, copied untracked+modified files back, removed both worktrees (`git worktree remove --force`), deleted stale branches.
2. **Pipeline refactor adopted.** 4-stage pipeline with new intermediate IR: `StructIR → StructInlineIR → MemberlessIR → FlatIR → R1CS`. `StructInlineIR` (`Heyting/Languages/StructInlineIR.lean`, 216 lines) — flat-member IR without `call`. New passes: `StructIRToStructInlineIR.lean` (~1260 lines, inlining + alpha-renaming), `StructInlineIRToMemberlessIR.lean` (82 lines, `Nat.pair`/`Equiv.listNatEquivNat` encoding from `Heyting/Core/VarIdEncoding.lean`).
3. **Filled last sorry** — `StructIRToStructInlineIR.expandBody_correct` call case. Helper `StructIR.evalConstrainBody_agree`: if 2 envs/objEnvs agree at positions `< bound` and body references only vars `< bound`, constrain-body evaluations equivalent. Call case: (a) split target with `StructInlineIR.evalConstrainBody_append`; (b) match callee to inlined block via `inlineBody_correct` + `evalConstrainBody_irrel`; (c) apply IH on tail with `next := na` at post-ic state, bridged via agreement lemma + `inlineBody_frame`.
4. **Verification:**
   - `grep -r "sorry" Heyting/ --include="*.lean"` → empty (only literal string in comment in `Passes/Lowering.lean`).
   - `lake build` → 1191 jobs, 0 errors. Pre-existing stylistic warnings only.
   - `lake build hey` → success.
   - `lean_verify` on `expandBody_correct`, `preservation`, `reflection`, `evalConstrainBody_agree` → standard axioms only.

**Layout added:**
- `Heyting/Core/VarIdEncoding.lean`
- `Heyting/Languages/StructInlineIR.lean`
- `Heyting/Passes/StructIRToStructInlineIR.lean`
- `Heyting/Passes/StructInlineIRToMemberlessIR.lean`
- `Heyting/Test/StructInlineIRTest.lean`, `Heyting/Test/VarIdEncodingTest.lean`
- `docs/superpowers/plans/`, `docs/superpowers/specs/`

**Not yet done:**
- New `StructIRToStructInlineIR` / `StructInlineIRToMemberlessIR` passes have `Pass` instances but `PresReflPass` remains phase-2 work — `Pipeline.lean` only declares `Pass`, not full `PresReflPass`. (Equisatisfiability for 4-pass pipeline requires composing sub-pass `PresReflPass` instances; only pass 1 fully done.)
- Pre-existing style warnings in `StructIRToStructInlineIR.lean` (4 `show` vs `change`, unused simp args).

---

## Session 23 — 2026-04-29 (afternoon)

**Goals:** Redesign Pass 2 (`StructInlineIRToMemberlessIR`) under Option 2 (drop `readMember`; pre-populate `mw` via witness replay) — prove `PresReflPass`. Reach stable WIP checkpoint.

**Done:**
1. **MemberlessIR semantics change.** `evalBody` for felt ops now **assertion** (`env dest = env src1 + env src2`) not **update** (`env.update dest`). Aligns with R1CS (felt ops = constraints, not assignments) and makes Option 2 preservation tractable: `menv` fixed (= `mw`) throughout, need only show `mw` satisfies all asserted equations.
2. **StructInlineIR.Module extended.** `isSSA : ∀ i, (constrainDests (structs i).constrain.body).Nodup` alongside existing `noDupReads`. Both needed for Pass 2: `isSSA` for preservation (single-assignment ⇒ intermediate env = final witness), `noDupReads` for reflection (unique-read ⇒ `buildReadMap` injective).
3. **Pass 2 rewritten:**
   - `compileStmt`: drops `readMember` entirely (previously spurious `constrainEq dest (Nat.pair self member)` — semantically incorrect).
   - `compileWitnessBody`: threads env+ObjEnv through body like `evalConstrainBody`, updates `acc` at each written slot (felt ops compute; `readMember dest self member` stores `ws(objEnv self, member)`).
   - `compileWitness`: seeds `initAcc = fun k => ws([], k)` matching `initEnv` so `acc = env` invariant starts true.
   - `buildReadMap` + `extractWitness`: backward MemberlessIR→StructInlineIR via ObjEnv replay.
   - `witnessRel m ws mw := mw = compileWitness m ws`.
4. **Key invariant proved:** `compileWitnessBody_agrees` — if `∀ k, acc k = env k` initially, then `compileWitnessBody ws env objEnv stmts acc k = (runState ws env objEnv stmts).1 k` for all k. `mw` equals final StructInlineIR env at every slot. Standard axioms only.
5. **Pass 1 compile updated.** `StructIRToStructInlineIR.compile` produces `Module` with 2 well-formedness proofs. `compile_noDupReads`, `compile_isSSA` left as `sorry` — structural induction over `expandBody`/`inlineBody` not completed.
6. **Pass 2 `preservation`/`reflection`: sorry.** Proofs need connecting step-local env values to final witness — depends on SSA + def-before-use. Mechanical but needs infrastructure.

**Verification:**
- `lake build` → 0 errors, 4 sorry warnings (compile_noDupReads, compile_isSSA, preservation, reflection).
- `lake build hey` → CLI builds.
- `lake exe tests` → all pass (examples use `#eval!` to bypass sorry-dependent evaluation).
- `multiply.llzk` → 2 R1CS constraints (`a*b = out`).

**Sorries (4):**
- `StructIRToStructInlineIR.compile_noDupReads` — needs `readPositions_inlineBody_eq`/`readPositions_expandBody_eq`.
- `StructIRToStructInlineIR.compile_isSSA` — induction showing `inlineBody`/`expandBody` preserve dest-uniqueness.
- `StructInlineIRToMemberlessIR.preservation` — SSA + DBU machinery linking step-local and final env.
- `StructInlineIRToMemberlessIR.reflection` — `buildReadMap` injectivity via `m.noDupReads`.

**Next:** complete 4 proofs. All mechanical structural inductions (~200 lines each). No design questions blocking.
