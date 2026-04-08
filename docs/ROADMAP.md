# Heyting Roadmap

Detailed plan for the next phases of development. The verified core
(StructIR → FlatIR → R1CS) is complete. The focus now shifts to making
Heyting practical: parsing real inputs, producing real outputs, and
extending the language coverage.

---

## Phase 1: Proof Engineering (current)

**Goal:** Make pass proofs easier to write and maintain.

**Status:** Started in Session 10, major progress in Session 12.

| Task | Status | Notes |
|------|--------|-------|
| Custom R1CS tactics (`Passes/Tactics.lean`) | Done | `r1cs_arith`, `r1cs_unfold_sat` |
| Pass-internal helper lemmas | Done | Generic `witnessCoherent_update_from_sat`, `preservation_body_peel_binop`, multi-pattern binop merging |
| Refactor existing proofs to use helpers | Done | StructIRToFlatIR reduced from 2010 → 1861 lines; 6 coherence lemmas → 1, 4 binop cases merged |
| Document proof patterns | Done | See `docs/tactics.md` |

**Impact:** Adding a new felt operation (e.g., `feltPow`) should require only:
1. The instruction case in 4 functions (compile, buildWitness, buildVarAlloc, eval)
2. One `satisfiesInstr` proof (in the FlatIR→R1CS pass)
3. The `buildWitness_preserves_below` + coherence plumbing is now generic

---

## Phase 2: Practical I/O

**Goal:** Read real LLZK circuit files and produce real R1CS output.

### 2a. LLZK Parser ✅

Parse LLZK MLIR textual IR into an untyped AST. This is the first stage
of the bridge between the verified core and real-world ZKP circuits.

**Status:** Complete (Lean 4 native parser, Option A).

| Task | Status | Notes |
|------|--------|-------|
| LLZK textual IR tokenizer | Done | `Heyting/Parser/Tokenizer.lean` — handles `%ssa`, `@sym`, `!type`, int literals, keywords, punctuation |
| Recursive descent parser | Done | `Heyting/Parser/Parser.lean` — modules, structs, functions, felt ops, struct ops, constrain.eq, calls, nondet |
| Untyped AST definition | Done | `Heyting/Parser/AST.lean` — `LLZK.Module`, `StructDef`, `FuncDef`, `Stmt` (17 variants) |
| Pretty-printer & stats | Done | `Heyting/Parser/Main.lean` — `ppModule`, `countStmts` |
| Qualified name support | Done | Handles `@Mod::@func` in function.call |
| Multi-section files | Done | Splits on `// -----`, parses each section, merges structs |
| Unsupported op skipping | Done | `constrain.in`, `arith.*`, `array.*`, bitwise ops → skip with warnings |

**Tested on 5 real LLZK files from `llzk-lib/test/Dialect/`:**
- `emit_pass.llzk` — 5 structs, 20 stmts
- `nondet_preservation.llzk` — 1 struct, 9 stmts
- `circomlib.llzk` — 2 structs, 42 stmts (with qualified calls)
- `felt_arith_pass.llzk` — free functions only (correctly skipped)
- `structs_pass.llzk` — 25 structs, 81 stmts (with template params skipped)

### 2a′. AST → StructIR Lowering ✅

Lower the untyped `LLZK.Module` AST into typed `StructIR.Module`. This
requires resolving struct references to `Fin` indices, assigning member
indices, and verifying `noDupReads`.

**Status:** Complete (Session 12). Unverified `partial` lowering pass with `Except String` error propagation.

| Task | Complexity | Notes |
|------|------------|-------|
| Struct dependency resolution | Medium | Done — Kahn's BFS topological sort, `Fin` index assignment |
| Member type/index assignment | Medium | Done — `lowerMembers`, `buildMemberIndex` |
| SSA → variable mapping | Medium | Done — `buildSSAMap` assigns monotonic `Nat` indices |
| `noDupReads` validation | Medium | Done — decidable `List.Nodup` check at runtime |
| Error reporting for unsupported patterns | Low | Done — `Except String` propagation |

### 2b. R1CS Output

Serialize `R1CS.System` to a standard format.

| Task | Complexity | Notes |
|------|------------|-------|
| R1CS binary format (Circom-compatible) | Low | Standard `.r1cs` format: header + constraints |
| JSON output | Low | For debugging/inspection |
| Witness format | Low | Map `R1CS.VarId` → integer indices |
| Variable naming | Low | Carry names through for debugging |

**Standard format:** The [Circom `.r1cs` binary format](https://github.com/iden3/r1csfile) is widely supported (SnarkJS, Rapidsnark, etc.). Alternatively, the JSON format from SnarkJS.

---

## Phase 3: Language Extensions

### 3a. Array Support

Add `array` dialect support to StructIR. Arrays appear in many real circuits
(e.g., lookup tables, permutation arguments).

| Task | Complexity | Notes |
|------|------------|-------|
| `ArrayType` in `MemberDecl` | Low | `array : Fin n → MemberType` |
| `readArray`/`writeArray` statements | Medium | Index expressions, bounds |
| Array flattening in StructIR→FlatIR | Medium | Unroll to individual felt reads |
| Proofs for array cases | High | New cases in all proof lemmas |

### 3b. Polymorphism / Generics

LLZK's `poly` dialect allows parametric structs. This is lower priority —
most circuits can be monomorphized.

### 3c. Control Flow

LLZK uses MLIR's `scf` dialect for loops and conditionals. Loops in
constraint generation are bounded (circuit size is fixed), so they can
be unrolled. Not needed for initial circuits.

---

## Phase 4: Optimization Passes

**Goal:** Verified optimization passes that reduce constraint count without
changing semantics.

| Optimization | Impact | Complexity | Notes |
|-------------|--------|------------|-------|
| Dead constraint elimination | Medium | Low | Remove unconstrained variables |
| Constant folding | Medium | Low | Evaluate constant expressions at compile time |
| Common subexpression elimination | High | Medium | Reuse computed values |
| Linear combination merging | High | Medium | Merge compatible R1CS constraints |

Each optimization would be a separate `PresReflPass` with its own
preservation and reflection proofs.

---

## Phase 5: Verified Backend

**Goal:** Generate verified provers and verifiers from R1CS.

This is the "close the loop" phase — not just a verified compiler, but a
verified toolchain.

| Task | Complexity | Notes |
|------|------------|-------|
| Groth16 prover formalization | Very High | Requires elliptic curve arithmetic in Lean |
| Verification equation proof | Very High | `e(A, B) = e(α, β) · e(vk, γ) · e(C, δ)` |
| Trusted setup formalization | High | CRS generation |
| Alternative: Plonk/STARK backend | Very High | Different arithmetization |

**Alternative approach:** Rather than formalizing the full prover, generate
an executable prover in a lower-level language (Rust/C) and verify the
*specification* (relation between R1CS satisfaction and proof validity)
in Lean. This is more tractable.

---

## Phase 6: Paper / Publication

**Goal:** Publish the results.

| Venue | Focus | Timeline |
|-------|-------|----------|
| Workshop paper (FMBC, etc.) | Framework + verified pipeline | After Phase 2 |
| Conference paper (CAV, ESOP, S&P) | Full toolchain + case studies | After Phase 4 |

**Key contributions to highlight:**
1. First formally verified ZKP compiler (StructIR → R1CS)
2. Trace-relating correctness framework adapted to ZKP witnesses
3. Intrinsic well-formedness via dependent types (no fuel, no well-formedness predicates)
4. Meaningful witness relation (not trivial `True`)
5. Custom proof tactics for pass automation

---

## Suggested Order for Next Sessions

1. ~~**Session 11:** Refactor `StructIRToFlatIR.lean` proofs to use `Core/Tactics.lean`~~ Done (Session 12)
2. ~~**Session 12:** Build LLZK parser~~ Done — Lean 4 native parser on `feature/llzk-parser`
3. ~~**Next:** AST → StructIR lowering (`Heyting/Passes/Lowering.lean`)~~ Done (Session 12)
4. **Then:** R1CS output (Circom `.r1cs` binary format)
5. **Then:** Test full pipeline on a real circuit (e.g., IsZero from circomlib)
6. **Later:** Array support in StructIR
7. **Later:** Optimization passes, paper writing
