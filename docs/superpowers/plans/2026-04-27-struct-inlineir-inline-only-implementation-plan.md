# StructInlineIR Inline-Only Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `StructInlineIR` call-free while preserving `readMember` and `VarId` witness semantics, and align pass boundaries so `StructIR -> StructInlineIR` is inlining-only.

**Architecture:** Keep `StructInlineIR` as a path-aware constrain IR (`VarId = InstancePath × Nat`) with no call constructor. Implement pass 1 as call inlining with identity witness relation, and keep witness-space transition/read flattening concerns in pass 2. Preserve clear proof boundaries by proving pass 1 first, then adapting pass 2 contracts.

**Tech Stack:** Lean 4.28.0, Mathlib v4.28.0, Lake build/test tooling, existing `Pass`/`PresReflPass` framework in `Heyting/Core/Pass.lean`.

---

## File Structure and Responsibilities

- `Heyting/Languages/StructInlineIR.lean`
  - Source of truth for call-free StructInlineIR statement language and semantics.
- `Heyting/Passes/StructIRToStructInlineIR.lean`
  - Call inlining only; no witness-space change.
- `Heyting/Passes/StructInlineIRToMemberlessIR.lean`
  - Read elimination / witness-space transition boundary.
- `Heyting/Passes/Pipeline.lean`
  - Composition/witness relation wiring across updated pass contracts.
- `Heyting/Test/StructInlineIRTest.lean`
  - Language-level and pass-boundary-focused regression checks.
- `Heyting/Test/Main.lean`
  - Test harness import updates if new tests are introduced.

### Task 1: Make StructInlineIR Intrinsically Call-Free

**Files:**
- Modify: `Heyting/Languages/StructInlineIR.lean`
- Test: `Heyting/Test/StructInlineIRTest.lean`

- [ ] **Step 1: Write failing test proving StructInlineIR has no call constructor**

Add a compile-time shape check in `Heyting/Test/StructInlineIRTest.lean` that enumerates constructors used by pattern matching and intentionally fails if a `call` case is required.

```lean
import Heyting.Languages.StructInlineIR

open StructInlineIR

example {n : Nat} {F : Type} (s : ConstrainStmt n F) :
    True := by
  cases s with
  | feltAdd _ _ _ => trivial
  | feltSub _ _ _ => trivial
  | feltMul _ _ _ => trivial
  | feltDiv _ _ _ => trivial
  | feltNeg _ _ => trivial
  | feltConst _ _ => trivial
  | readMember _ _ _ => trivial
  | constrainEq _ _ => trivial
```

- [ ] **Step 2: Run test to verify RED state if language still exposes calls**

Run: `lake env lean Heyting/Test/StructInlineIRTest.lean`

Expected RED signal (if still wrong): either missing coverage due to additional constructors or mismatch against expected statement API.

- [ ] **Step 3: Implement minimal language change in StructInlineIR**

In `Heyting/Languages/StructInlineIR.lean`, ensure `ConstrainStmt` contains only:
- `feltAdd`, `feltSub`, `feltMul`, `feltDiv`, `feltNeg`, `feltConst`, `readMember`, `constrainEq`

No `call` constructor should exist.

- [ ] **Step 4: Run test to verify GREEN state**

Run: `lake env lean Heyting/Test/StructInlineIRTest.lean`

Expected: pass with no new diagnostics.

- [ ] **Step 5: Commit**

```bash
git add Heyting/Languages/StructInlineIR.lean Heyting/Test/StructInlineIRTest.lean
git commit -m "refactor: make StructInlineIR intrinsically call-free"
```

### Task 2: Align StructIR->StructInlineIR Pass to Inlining-Only Contract

**Files:**
- Modify: `Heyting/Passes/StructIRToStructInlineIR.lean`
- Test: `Heyting/Test/StructInlineIRTest.lean`

- [ ] **Step 1: Write failing pass-boundary test (identity witness intent)**

Add a minimal theorem skeleton asserting witness relation is identity at pass 1 boundary:

```lean
example {n : Nat} {F : Type} [Field F]
    (m : StructIR.Module (n + 1) F) (w : StructIR.Witness F) :
    StructIRToStructInlineIR.witnessRel m w w := by
  -- should reduce to reflexivity
  simp [StructIRToStructInlineIR.witnessRel]
```

- [ ] **Step 2: Run test to verify RED state if pass boundary drifted**

Run: `lake env lean Heyting/Test/StructInlineIRTest.lean`

Expected RED signal (if broken): theorem not solvable by simple reduction.

- [ ] **Step 3: Implement minimal pass alignment**

Update `Heyting/Passes/StructIRToStructInlineIR.lean` so:
- compile logic only handles call inlining/substitution/renaming.
- no witness-space encoding logic is introduced.
- `witnessRel` is definitional identity (`wi = ws`).

- [ ] **Step 4: Run test to verify GREEN state**

Run: `lake env lean Heyting/Test/StructInlineIRTest.lean`

Expected: pass.

- [ ] **Step 5: Commit**

```bash
git add Heyting/Passes/StructIRToStructInlineIR.lean Heyting/Test/StructInlineIRTest.lean
git commit -m "refactor: enforce inline-only contract for StructIRToStructInlineIR"
```

### Task 3: Rebound Pass 2 to Read-Elimination/Witness-Transition Responsibility

**Files:**
- Modify: `Heyting/Passes/StructInlineIRToMemberlessIR.lean`
- Modify: `Heyting/Passes/Pipeline.lean`

- [ ] **Step 1: Write failing theorem-style test for pass-2 witness relation contract**

Add an internal sanity theorem (in file or test) that witness relation is the first point where encoding appears:

```lean
example {n : Nat} {F : Type} [Field F]
    (m : StructInlineIR.Module (n + 1) F)
    (w : StructInlineIR.Witness F) :
    StructInlineIRToMemberlessIR.witnessRel m w (StructInlineIRToMemberlessIR.compileWitness m w) := by
  simp [StructInlineIRToMemberlessIR.witnessRel]
```

- [ ] **Step 2: Run targeted check to verify RED state if contract is missing**

Run: `lake env lean Heyting/Passes/StructInlineIRToMemberlessIR.lean`

Expected RED signal (if missing): unresolved names or unsatisfied witness relation theorem.

- [ ] **Step 3: Implement minimal pass-2 contract cleanup**

In `Heyting/Passes/StructInlineIRToMemberlessIR.lean`:
- keep pass-2 as the location of read elimination and encoding bridge.
- make witness relation explicit and local to pass 2.
- avoid introducing call semantics.

In `Heyting/Passes/Pipeline.lean`:
- ensure composition uses pass-1 identity relation and pass-2 encoding relation boundary.

- [ ] **Step 4: Run targeted checks to verify GREEN state**

Run:
- `lake env lean Heyting/Passes/StructInlineIRToMemberlessIR.lean`
- `lake env lean Heyting/Passes/Pipeline.lean`

Expected: both pass.

- [ ] **Step 5: Commit**

```bash
git add Heyting/Passes/StructInlineIRToMemberlessIR.lean Heyting/Passes/Pipeline.lean
git commit -m "refactor: move witness-space transition concerns to pass 2"
```

### Task 4: Prove/Restore Correctness Boundaries Without Reintroducing Sorry

**Files:**
- Modify: `Heyting/Passes/StructIRToStructInlineIR.lean`
- Modify: `Heyting/Passes/StructInlineIRToMemberlessIR.lean`

- [ ] **Step 1: Add failing theorem skeleton(s) for selected correctness boundary**

Prefer proving pass 1 first:

```lean
-- in StructIRToStructInlineIR.lean
theorem preservation ... := by
  -- placeholder to enter RED state; do not use sorry
  fail_if_success exact True.intro
```

and similarly for reflection if in-scope this iteration.

- [ ] **Step 2: Run file check to confirm RED state**

Run: `lake env lean Heyting/Passes/StructIRToStructInlineIR.lean`

Expected: theorem unresolved/failing (explicit RED).

- [ ] **Step 3: Implement minimal proofs to GREEN for chosen scope**

Implement real proofs (no `sorry`) for whichever theorem set is in scope:
- Pass 1 preservation/reflection first.
- Pass 2 theorem scaffolding only if immediately provable under new boundary.

- [ ] **Step 4: Re-run file checks to verify GREEN state**

Run:
- `lake env lean Heyting/Passes/StructIRToStructInlineIR.lean`
- `lake env lean Heyting/Passes/StructInlineIRToMemberlessIR.lean`

Expected: pass with no theorem holes.

- [ ] **Step 5: Commit**

```bash
git add Heyting/Passes/StructIRToStructInlineIR.lean Heyting/Passes/StructInlineIRToMemberlessIR.lean
git commit -m "proof: reestablish pass correctness boundaries without sorry"
```

### Task 5: Project Verification and Regression Gate

**Files:**
- Verify: workspace-wide changes

- [ ] **Step 1: Run project build gate**

Run: `lake build`

Expected: build succeeds.

- [ ] **Step 2: Run sorry scan gate**

Run: `rg "sorry" Heyting`

Expected: no actual `sorry` terms in Lean code (comments may appear and should be reviewed).

- [ ] **Step 3: Run targeted test gate**

Run:
- `lake env lean Heyting/Test/StructInlineIRTest.lean`
- `lake env lean Heyting/Test/VarIdEncodingTest.lean`

Expected: both pass.

- [ ] **Step 4: Run axiom gate for newly proved declarations**

Run `lean_verify` for each newly introduced/modified correctness theorem in pass files.

Expected: only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) when applicable.

- [ ] **Step 5: Final commit for verification/docs touch-ups**

```bash
git add Heyting/Test/StructInlineIRTest.lean Heyting/Test/VarIdEncodingTest.lean
git commit -m "test: verify inline-only StructInlineIR and pass-boundary invariants"
```

## Self-Review

- Spec coverage check:
  - call-free StructInlineIR covered by Task 1
  - pass-1 inline-only + identity witness covered by Task 2
  - pass-2 witness-space/read elimination boundary covered by Task 3
  - correctness/proof recovery covered by Task 4
  - verification checklist covered by Task 5
- Placeholder scan: no TBD/TODO placeholders left in steps.
- Type consistency: all references use existing module/type names in current branch (`StructInlineIR`, `StructIRToStructInlineIR`, `StructInlineIRToMemberlessIR`, `Pipeline`).
