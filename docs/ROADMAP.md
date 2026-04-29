# Heyting Roadmap

Development phases. ✅ = complete; 🔄 = in progress; ⬜ = not started.

---

## Phase 1: Proof Engineering ✅

**Goal:** Make pass proofs easier to write and maintain.

| Task | Status |
|------|--------|
| Custom R1CS tactics (`Passes/Tactics.lean`) | ✅ |
| Pass-internal helper lemmas | ✅ |
| Refactor existing proofs to use helpers | ✅ |
| Document proof patterns (`docs/tactics.md`) | ✅ |

---

## Phase 2: Practical I/O ✅

**Goal:** Read real LLZK circuit files and produce real R1CS output.

### 2a. LLZK Parser ✅

| Task | Status |
|------|--------|
| Tokenizer (`Parsers/Tokenizer.lean`) | ✅ |
| Recursive descent parser (`Parsers/Parser.lean`) | ✅ |
| Untyped AST (`Parsers/AST.lean`) | ✅ |
| Multi-section file support | ✅ |
| Unsupported op skipping with warnings | ✅ |
| Tested on 5 real LLZK files from `llzk-lib/test/` | ✅ |

### 2a′. AST → StructIR Lowering ✅

Unverified `partial` lowering with `Except String` error propagation.

| Task | Status |
|------|--------|
| Topo sort + Fin index assignment | ✅ |
| Member type/index assignment | ✅ |
| SSA → variable mapping | ✅ |
| `noDupReads` / `isSSA` / `isDefBeforeUse` validation | ✅ |

### 2b. R1CS Output ✅

| Task | Status |
|------|--------|
| JSON output (`Backends/R1CSJSON.lean`) | ✅ |
| CLI entry point `hey compile` | ✅ |
| Multi-field support (`--prime-field`, 6 fields) | ✅ |
| Witness JSON output | ✅ |
| R1CS binary format (Circom `.r1cs`) | ✅ |
| Witness binary format (`.wtns`) | ✅ |
| Unit tests (`Test/R1CSJSONTest.lean`, `BinaryTest.lean`) | ✅ |

---

## Phase 2.5: Complete the PresReflPass chain 🔄

**Goal:** Prove passes 2 and 3, composing the full end-to-end `PresReflPass`.

### Current status

| Pass | File | PresReflPass |
|------|------|:---:|
| 1: StructIR → StructInlineIR | `StructIRToStructInlineIR.lean` | ✅ |
| 2: StructInlineIR → MemberlessIR | `StructInlineIRToMemberlessIR.lean` | ⚠️ `Pass` only |
| 3: MemberlessIR → FlatIR | `MemberlessIRToFlatIR.lean` | ⚠️ `Pass` only |
| 4: FlatIR → R1CS | `FlatIRToR1CS.lean` | ✅ |
| Pipeline | `Pipeline.lean` | ⚠️ `Pass` only |

### 2.5a. Resolve Pass 2 semantic gap

**Blocker:** `readMember dest self member` → `constrainEq dest (Nat.pair self member)`
treats local variable `self` as if it *is* the encoded path. This is only correct when
`objEnv self` is determined by `self` alone. Design question: does StructInlineIR (after
call inlining) guarantee this? If not, a different compilation strategy is needed.
See `docs/WARNING.md` §8.

**Tasks:**
- Decide: is the current `constrainEq` strategy correct, or does Pass 2 need redesign?
- Prove (or redesign + prove) `StructInlineIRToMemberlessIR.PresReflPass`.

### 2.5b. Prove Pass 3 (`MemberlessIRToFlatIR`)

The proof structure mirrors the old `StructIRToFlatIR` pass:
- `compileWitness_agrees` invariant: `∀ v, wt (vm v) = env v`
- Preservation + reflection by induction on `(i, stmts.length)`
- `call` case: callee invariant via IH; frame for outer `vm` unchanged

Estimated complexity: ~600–900 lines.

### 2.5c. Wire up pipeline `PresReflPass`

Once 2.5a and 2.5b are done, `Pipeline.CorrectPipeline` follows by composing the four
sub-pass instances (preservation: forward chain; reflection: reverse chain).

---

## Phase 3: Language Extensions ⬜

### 3a. Array Support

| Task | Complexity |
|------|------------|
| `ArrayType` in `MemberDecl` | Low |
| `readArray`/`writeArray` statements | Medium |
| Array flattening in StructIR→StructInlineIR | Medium |
| Proofs for array cases | High |

### 3b. Polymorphism / Generics

LLZK's `poly` dialect allows parametric structs. Lower priority — most circuits can be
monomorphized first.

### 3c. Control Flow

LLZK uses `scf` for bounded loops. Loops in constraint generation are circuit-size-fixed,
so they can be unrolled.

---

## Phase 4: Optimization Passes ⬜

Verified optimization passes (dead constraint elimination, constant folding, CSE, linear
combination merging). Each would be a separate `PresReflPass`.

---

## Phase 5: Verified Backend ⬜

Formalize a prover (Groth16 or Plonk) or verify a generated prover's specification.

---

## Phase 6: Paper / Publication ⬜

Workshop paper (FMBC) after Phase 2.5 complete; conference paper (CAV/ESOP/S&P) after
Phase 4.
