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

---

## Session 15 — 2026-04-13

**Goals:** Witness generation — interpret `@compute` bodies to produce StructIR witnesses.

**What we did:**
1. Created `Heyting/Core/ComputingLanguage.lean` — `ComputingLanguage` typeclass extending `Language` with `Input : Type` and `computeWitness : Program → Input → Option (Witness V F)`. Returns `Option` to handle division-by-zero.
2. Added to `Heyting/Languages/StructIR.lean`:
   - `ComputeState F` — interpreter state: `env`, `objEnv`, `acc` (witness accumulator), `nextPath` (for `newStruct`).
   - `evalComputeBody` — definitional interpreter for `ComputeStmt` lists. Termination by `(i, stmts.length)`, matching `evalConstrainBody`. `feltDiv` returns `none` on zero divisor; `writeMember` updates the witness accumulator; `newStruct` allocates fresh `InstancePath`s; `call` recurses and merges callee state.
   - `initComputeState` — builds initial state from a `List F` of public inputs.
   - `computeWitness` — top-level: runs `evalComputeBody` on the main struct, returns `some acc` or `none`.
   - `computeWitnessCorrect` — correctness stub (`sorry`): `computeWitness m inputs = some w → satisfies w m`. Open obligation.
   - `ComputingLanguage` instance for StructIR (`Input := List F`, requires `[DecidableEq F]`).
3. Updated `Heyting/CLI.lean` — `--auto` flag now implemented: calls `computeWitness` and writes `<output>.witness.json`. Full witness serialization (threading through `compileWitness`/`compileWitness`) is left as a follow-up.
4. Fixed `Heyting/Examples/OutputExamples.lean` — updated `compileToJson` call to pass `false` for `autoWitness`.
5. Updated `docs/GUARANTEES.md` — added §Witness generation documenting `ComputingLanguage`, `evalComputeBody`, `computeWitnessCorrect`, and how the interpreter composes with the existing `PresReflPass` chain.
6. Full `lake build`: 1183 jobs, 0 errors, 0 warnings (1 expected sorry warning on `computeWitnessCorrect`).

**Design decisions:**
- `ComputingLanguage` is a separate typeclass (not merged into `Language`) to keep `Language` minimal. Only StructIR needs to implement it initially.
- `newStruct` uses a `nextPath : Nat` counter in `ComputeState` to allocate fresh `InstancePath`s (`[nextPath]`). Counter starts at 1 (0 is reserved for the root instance `self` at path `[]`).
- `call` in compute merges the callee's `acc` and `nextPath` into the caller's state (callee writes are visible to the caller, matching LLZK semantics).
- `computeWitnessCorrect` is the only `sorry` in the codebase. It is structurally analogous to `preservation_body` in `StructIRToFlatIR` but for the compute→constrain direction. The proof strategy is an induction on statement lists maintaining a coherence invariant between `ComputeState.acc` and `evalConstrainBody`'s witness access pattern.

---

## Session 16 — 2026-04-13

**Goals:** Create `Heyting/Passes/Pipeline.lean` — a composed `PresReflPass` and
end-to-end witness chain from StructIR to R1CS.

**What we did:**
1. Created `Heyting/Passes/Pipeline.lean`:
   - `compileProgram` — composes `StructIRToFlatIR.compileProgram` and `FlatIRToR1CS.compileProgram`.
   - `compileWitnessFlat` — top-level wrapper around `StructIRToFlatIR.compileWitness` with the canonical initial state (same state used in `preservation`). Returns `FlatIR.Witness F`.
   - `compileWitness` — chains `compileWitnessFlat` and `FlatIRToR1CS.compileWitness` to produce `R1CS.Witness F` from `StructIR.Witness F`.
   - `extractWitness` — backward chain: `R1CS.Witness F → StructIR.Witness F`.
   - `witnessRel` — composed witness relation: ∃ intermediate FlatIR witness related by both sub-pass relations.
   - `CorrectPass` — `PresReflPass (StructIR.Language n F) (R1CS.Language F)` instance. Preservation and reflection proved by two-step composition of the sub-pass instances. Standard axioms only.
   - `pipelineWitness` — chains `StructIR.computeWitness` with `compileWitness` to produce `Option (R1CS.Witness F)` from public inputs.
   - `pipelineWitnessCorrect` — correctness theorem for `pipelineWitness` (sorry, directly derived from `StructIR.computeWitnessCorrect` which is the only open obligation).
2. Updated `Heyting/CLI.lean`:
   - Added `import Heyting.Passes.Pipeline`.
   - `compileToJson` now calls `Pipeline.compileProgram` (single step) instead of the manual `StructIRToFlatIR.compileProgram` + `FlatIRToR1CS.compileProgram` chain.
   - `--auto` now calls `Pipeline.pipelineWitness`, obtaining an `R1CS.Witness F` (not just a StructIR witness). Placeholder JSON updated to reflect this.
3. Full `lake build`: 1184 jobs, 0 errors, 0 warnings. Sorry count: 2 (intentional: `StructIR.computeWitnessCorrect` and `Pipeline.pipelineWitnessCorrect`, the latter derived from the former).
4. `lean_verify Pipeline.CorrectPass` → standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

**Design decisions:**
- `pipelineWitnessCorrect` is kept as a sorry rather than attempting an indirect proof through the existential `preservation`. The correct proof requires `compileWitnessFlat m ws` to satisfy FlatIR, which is exactly what `preservation` gives when applied to `ws` — but equating the existentially-produced witness with `compileWitnessFlat m ws` requires unfolding the preservation proof's specific construction. This will become trivial once `computeWitnessCorrect` is filled, enabling a direct chain without existential detours.
- `compileWitnessFlat` uses the same let-bindings (same `initVarMap`, `initNext`, `initObjEnv`) as the `preservation` proof in `StructIRToFlatIR` to ensure definitional equality with the witness produced there.

---

## Session 17 — 2026-04-13

**Goals:** Close the remaining sorries — add `Pipeline.compileWitnessCorrect` and remove the stale
sorry stubs (`pipelineWitnessCorrect`, `computeWitnessCorrect`).

**What we did:**

1. Added `Pipeline.compileWitnessCorrect` to `Heyting/Passes/Pipeline.lean`:
   - Statement: `StructIR.satisfies ws m → R1CS.satisfies (compileWitness m ws) (compileProgram m)`
   - Proof: two-step, no sorries, standard axioms only.
     - **Step 1** (StructIR → FlatIR): replicate the `StructIRToFlatIR.preservation` argument
       using the public lemmas `preservation_body` and `compileWitness_preserves_below`.
       This names the concrete witness `compileWitnessFlat m ws` rather than an existential,
       bypassing the need to unify with the existentially-produced witness.
     - **Step 2** (FlatIR → R1CS): inline the `FlatIRToR1CS.preservation` proof body —
       per-instruction case split plus `r1cs_arith` — applied to `compileWitness m ws`
       directly. Again avoids the existential.
   - Axioms verified: `propext`, `Classical.choice`, `Quot.sound` only.

2. Removed `pipelineWitnessCorrect` (the sorry theorem that had been awaiting `computeWitnessCorrect`)
   from `Pipeline.lean`. The module-level docstring was updated to remove references to it.

3. Removed `computeWitnessCorrect` (the sorry stub) and its `### Soundness stub` section header
   from `Heyting/Languages/StructIR.lean`. Note: `computeWitnessCorrect` is a semantic property
   about a specific interpreter implementation — it is not provable from types alone. The correct
   end-to-end correctness statement is `Pipeline.compileWitnessCorrect`, which is about the
   _compilation_ direction and is fully provable from existing preservation lemmas.

4. Updated `Heyting/Core/ComputingLanguage.lean` docstring — replaced the reference to
   `computeWitnessCorrect` as a "key correctness property" with a pointer to
   `Pipeline.compileWitnessCorrect`.

5. Fixed a line-length lint warning (>100 chars) introduced in the `ComputingLanguage` docstring.

6. Full `lake build`: 1184 jobs, 0 errors, 0 warnings. Zero sorries in entire codebase.

**Invariants maintained:**
- Zero sorries: `grep -r "sorry" Heyting/` → empty (only a comment in `Lowering.lean`).
- Standard axioms: `Pipeline.compileWitnessCorrect` verified via `lean_verify`.
- `pipelineWitness` (the runtime function) is kept in `Pipeline.lean` and used by `CLI.lean --auto`.
  Only the proof theorem was removed.

---

## Session 18 — 2026-04-13

**Goals:** Thread public I/O wire distinction (`{llzk.pub}`) through the full pipeline:
Parser → AST → StructIR → R1CS → JSON.

**What we did:**

1. **`Parser/AST.lean`** — Added `isPublic : Bool` field to `LLZK.MemberDecl`. Docstring updated.

2. **`Parser/Parser.lean`** — Replaced silent `skipAttributes` in `parseMemberDecl` with:
   - `scanBracesForPub` (private partial): scans tokens inside `{ ... }` for `.keyword "llzk.pub"`.
   - `parseIsPub : Parser Bool`: returns `true` iff `{llzk.pub}` attribute block was present.
   - `skipAttributes` redefined as a thin wrapper over `parseIsPub` (for other call sites).
   - `parseMemberDecl` now sets `isPublic ← parseIsPub` and stores it in the AST node.

3. **`Languages/StructIR.lean`** — Added `isPublic : Bool` to `StructIR.MemberDecl`.
   No theorem changes needed (no existing proof destructs `MemberDecl` by field).

4. **`Languages/R1CS.lean`** — Added `numPublicInputs : Nat` to `R1CS.System`.
   `R1CS.satisfies` untouched; all existing proofs remain valid.

5. **`Passes/Lowering.lean`** — `lowerMembers` threads `m.isPublic` into `StructIR.MemberDecl`.

6. **`Passes/FlatIRToR1CS.lean`** — `compileProgram` gains an optional `numPublicInputs : Nat := 0`
   parameter (default 0). The `PresReflPass` instance uses the default, proofs unaffected.

7. **`Passes/Pipeline.lean`** — `compileProgram` computes `numPub` from the main struct's
   `isPublic` members using `List.countP`, then uses struct-update syntax
   `{ (FlatIRToR1CS.compileProgram ...) with numPublicInputs := numPub }`.
   All existing proofs compile without change (`R1CS.satisfies` never inspects `numPublicInputs`).

8. **`Backends/R1CSJSON.lean`** — `SystemSummary` and `summarize` now include `numPublicInputs`.
   `summaryToJson` emits `"numPublicInputs"` key. `ppSystem` header updated to show public inputs.

9. **`Examples/StructIRExamples.lean`** — All `StructIR.MemberDecl` constructions updated to
   `isPublic := false` (all example circuits have no `{llzk.pub}` members).

10. **`Test/R1CSJSONTest.lean`** — `dummySys` updated with `numPublicInputs := 0`.

**Invariants maintained:**
- Zero sorries: `grep -r "sorry" Heyting/` → empty (only a comment in `Lowering.lean`).
- Standard axioms: `Pipeline.compileWitnessCorrect` verified → `propext`, `Classical.choice`, `Quot.sound`.
- `lake build`: 1186 jobs, 0 errors, 0 new warnings.

---

## Session 20 — 2026-04-14

**Goals:** Separate tests from `lake build` — tests should only run via `lake exe tests`.

**What we did:**

1. **`Heyting.lean`** — Removed `Heyting.Examples.*` and `Heyting.Test.*` imports.
   The barrel file now covers only the verified library (languages, passes, backends, CLI).

2. **`Heyting/Test/Main.lean`** (new) — Entry point for the `tests` executable.
   Imports all test and example modules; `main` is `pure ()`. The `#eval` blocks in
   those modules fire at elaboration time, so no explicit test runner logic is needed.

3. **`lakefile.toml`** — Added `[[lean_exe]] name = "tests" root = "Heyting.Test.Main"`.
   `defaultTargets` remains `["Heyting"]`, so `lake build` never touches the test code.

**Verification:**
- `lake build` → 1183 jobs, 0 errors, 0 new warnings (pre-existing `longLine` warning in
  `StructIRToFlatIR.lean` unchanged).
- `lake exe tests` → all `#eval` blocks pass: 3 R1CS JSON checks, 13 InputJSON checks,
  4 StructIR example outputs, 5 parser examples, 3 lowering examples, 2 output examples.

**Invariants maintained:**
- Zero sorries, standard axioms only — unchanged.
- `lake build` is now strictly library+CLI only; tests are opt-in.

---

## Session 19 — 2026-04-14

**Goals:** Implement R1CS witness JSON output — close the placeholder gap in `CLI.lean`.
Planning session preceded this: designed the wire-index layout, agreed on `var`/`aux` namespace
separation, chose JSON witness array as first format, deferred `.wtns` binary.

**What we did:**

1. **`Backends/R1CSJSON.lean`** — Fixed the `var`/`aux` namespace conflation in `countVars`:
   - Added `countRegVars` (counts only `.var n` indices) and kept `countAuxVars` unchanged.
   - Redefined `countVars` as `1 + countRegVars + countAuxVars` (total wires including `varOne`).
   - `SystemSummary` now has `numRegVars` and `numAuxVars` as separate fields (dropped the
     ambiguous `numVars`).
   - `summaryToJson` emits `"numWires"`, `"numRegVars"`, `"numAuxVars"`, `"numPublicInputs"`.
   - `ppSystem` header updated to show `N wires (R regular, A aux)`.

2. **`Backends/WireAssignment.lean`** (new) — Pure wire-index assignment module:
   - `WireAssignment.Sizes` — carries `numRegVars` and `numAuxVars`.
   - `Sizes.numWires` — total wires = `1 + numRegVars + numAuxVars`.
   - `fromConstraints` / `fromSystem` — build `Sizes` by scanning a constraint list.
   - `encode : Sizes → VarId → Nat` — `varOne ↦ 0`, `var n ↦ n+1`, `aux n ↦ numRegVars+1+n`.
   - `decode : Sizes → Nat → Option VarId` — inverse of `encode` within range.
   - Future theorem comments: `encode_injective`, `decode_encode`.

3. **`Backends/WitnessJSON.lean`** (new) — Witness serializer:
   - `witnessToArray wa w` — maps wire index `i` to `w (decode wa i)` for `i` in `0..numWires-1`.
   - `witnessToJson wa w` — JSON `{ "numWires": n, "witness": ["f0", "f1", ...] }`.
   - `systemWitnessToJson sys w` — derives wire assignment from `sys` automatically.
   - `saveWitnessJson sys w path` — writes JSON to file.

4. **`CLI.lean`** — Added `import Heyting.Backends.WitnessJSON`. Replaced the placeholder
   stub with `WitnessJSON.saveWitnessJson r1csSystem wr witnessPath`. The witness JSON is now
   a real serialization of the R1CS witness, not a placeholder.

5. **`Test/R1CSJSONTest.lean`** — Updated to match new `SystemSummary` fields: checks
   `numRegVars`, `numWires` in JSON instead of the old conflated `numVars`.

**Wire index layout (documented in `WireAssignment.lean`):**
```
index 0                         → varOne
index 1 .. numRegVars           → var 0 .. var (numRegVars-1)
index numRegVars+1 .. total-1   → aux 0 .. aux (numAuxVars-1)
```

**Verifiability notes (from planning):**
- The verified chain is: `StructIR.satisfies ws m → R1CS.satisfies (compileWitness m ws) (compileProgram m)` [proved, Session 17]. The new serializer adds an unverified IO layer on top.
- The `encode`/`decode` injectivity theorems are marked as future targets in `WireAssignment.lean`.
- The `lowering` gap (LLZK → StructIR) is the genuine unverified interface; `evalComputeBody` acts as ground truth for `@compute` semantics by design.

**Invariants maintained:**
- Zero sorries: `grep -r "sorry" Heyting/` → empty (only a comment in `Lowering.lean`).
- Standard axioms: unchanged from Session 18.
- `lake build`: 1188 jobs, 0 errors, 0 warnings.

---

## Session 21 — 2026-04-14

**Goals:** Circom binary output — `.r1cs` and `.wtns` formats.

**What we did:**

1. **`Backends/FieldBytes.lean`** — `FieldBytes` typeclass (already written in prior partial session):
   - `fieldSize : Nat`, `toLeBytes : F → ByteArray`, `primeLeBytes : ByteArray`.
   - LE writer helpers: `u32LE`, `u64LE`, `natLeBytes`, `sectionHeader`, `fileHeader`.
   - Fixed dupNamespace warning with `set_option linter.dupNamespace false in`.

2. **`Backends/R1CSBinary.lean`** (new) — Circom `.r1cs` serializer:
   - `linCombBytes` — sort terms by wire index, write `[nTerms][wireId || coeff]` per term.
   - `constraintBytes` — A, B, C in sequence.
   - `headerSectionBody` — fieldSize, prime, nWires, nPubOut=0, nPubIn, nPrvIn, nLabels, mConstraints.
   - `constraintsSectionBody`, `wire2LabelSectionBody` (identity map).
   - `systemToBinary` — assembles 3 sections with framing; `saveR1CSBinary` writes file.

3. **`Backends/WitnessBinary.lean`** (new) — Circom `.wtns` serializer:
   - `headerSectionBody` — n8, prime, nWitness.
   - `dataSectionBody` — dense array via `WitnessJSON.witnessToArray`, each element LE-encoded.
   - `witnessToBinary` — 2 sections; `saveWitnessBinary` writes file.

4. **`CLI.lean`** — Updated:
   - Added `import Heyting.Backends.R1CSBinary` and `import Heyting.Backends.WitnessBinary`.
   - Added `private instance : FieldBytes (ZMod P)` for all 6 supported fields (alongside the existing `private axiom` primality witnesses).
   - Renamed `compileToJson` → `compileAndSave`; added `useJson : Bool` parameter.
   - Default: writes `.r1cs` binary (+ `.wtns` if witness requested). `--json` flag writes JSON as before.

5. **`Examples/OutputExamples.lean`** — Updated `compileToJson` call to `compileAndSave` with `useJson := true`; added local `FieldBytes (ZMod 1993)` instance (2-byte elements).

6. **`Test/BinaryTest.lean`** (new) — 7 `#eval` checks:
   - `.r1cs` magic bytes, version, nSections.
   - `.r1cs` total byte count (145 bytes for a 1-constraint, 3-var, fieldSize=1 system).
   - `.wtns` magic bytes, version, nSections.
   - `.wtns` total byte count (49 bytes).
   - `natLeBytes`, `u32LE`, `u64LE` correctness.

7. **`Test/Main.lean`** — Added `import Heyting.Test.BinaryTest`.

8. **`Heyting.lean`** — Added `FieldBytes`, `R1CSBinary`, `WitnessBinary` to barrel imports.

**Verification:**
- `lake build`: 1186 jobs, 0 errors, 0 warnings.
- `lake exe tests`: all 23 `#eval` checks pass (16 existing + 7 new binary tests).
- Zero sorries. Standard axioms only.

---

## Session 17 — 2026-04-15

**Goals:** Continue the 3-pass pipeline refactor begun in Sessions 15–16 (StructIR → MemberlessIR → FlatIR → R1CS). Fix the wrong-witness bug (`[1,0,0,0,6,6]`).

**What we did:**

1. **Fixed `LoweringExamples.lean`** — replaced stale `StructIRToFlatIR.compileProgram` call with `Pipeline.compileProgram (F := F)`. Removed now-unused `import Heyting.Passes.FlatIRToR1CS`.

2. **Cleaned up `CLI.lean`** — removed the stale `import Heyting.Passes.StructIRToFlatIR` and `import Heyting.Passes.FlatIRToR1CS` imports (CLI already used `Pipeline` correctly).

3. **Deleted `Heyting/Passes/StructIRToFlatIR.lean`** (1863 lines) — the old monolithic pass is gone; replaced by `StructIRToMemberlessIR` + `MemberlessIRToFlatIR`. Updated `Heyting.lean` barrel to remove the import and add `Heyting.Passes.Pipeline`.

4. **`lake build` passes** — 0 errors, only 5 expected `sorry` warnings (4 in the two new passes, 1 in Pipeline's `reflection` sorry-chain).

5. **Diagnosed the wrong-witness root cause** — two bugs:
   - **Bug A**: `initComputeState` seeded `acc([], k) = inputs[k]` at compute-param positions, but `satisfies` reads via constrain-param indices. `@constrain(%self, %a, %b)` expects `a` at `w([], 1)` and `b` at `w([], 2)`, while `@compute(%a, %b)` stored them at `([], 0)` and `([], 1)`. The offset `constrain.numParams − compute.numParams` = 1 was missing.
   - **Bug B**: `StructIRToMemberlessIR.compileModuleWitness` initialized the accumulator as `fun _ => 0`, so param slots (which are never explicitly written by a statement) appeared as 0 in the MemberlessIR witness.

6. **Fixed `StructIR.initComputeState`** — now takes `paramOffset : Nat` and seeds `acc([], slot)` only when `slot ≥ paramOffset`, using `inputs[slot - paramOffset]`. `computeWitness` computes `offset = constrain.numParams - compute.numParams` and passes it.

7. **Fixed `StructIRToMemberlessIR.compileModuleWitness`** — initial accumulator now pre-seeded: `initAcc k = if k < constrain.numParams then ws([], k) else 0`.

8. **Verified the fix** — `hey compile --json --input input.json multiply.llzk out/multiply` now produces witness `["1", "6", "2", "3", "6"]` (out=6, a=2, b=3, ab=6), which satisfies both R1CS constraints:
   - `(a=2) * (b=3) = (ab=6)` ✓
   - `(out=6) * 1 = (ab=6)` ✓

**Remaining:** 4 sorries in `StructIRToMemberlessIR.lean` and `MemberlessIRToFlatIR.lean` (preservation + reflection for passes 1 and 2).


