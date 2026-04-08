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

### 2a. LLZK Parser

Parse LLZK MLIR textual IR into `StructIR.Module`. This is the bridge
between the verified core and real-world ZKP circuits.

| Task | Complexity | Notes |
|------|------------|-------|
| LLZK textual IR tokenizer | Medium | MLIR syntax: `%var`, `@name`, types, blocks |
| Struct/function parser | Medium | Parse `struct.def`, `function.def`, member decls |
| Constrain body parser | Low | Map `felt.*` → `feltAdd` etc., `constrain.eq` → `constrainEq` |
| `Module` builder | Medium | Topological sort, `Fin` index assignment, `noDupReads` check |
| SSA normalization | Low | Ensure each `readMember` is unique (or transform duplicates) |

**Approach options:**
- **Option A: Lean 4 native parser** — write a parser combinator in Lean. Pro: everything stays in Lean, can potentially verify the parser. Con: more work, MLIR syntax is complex.
- **Option B: External tool** — Python/Rust tool that parses LLZK and emits a `.lean` file with the `Module` definition. Pro: faster to build, leverage existing MLIR tooling. Con: trusted boundary.
- **Option C: JSON intermediate** — external tool emits JSON, Lean reads JSON and builds `Module`. Pro: clean separation. Con: two steps.

**Recommendation:** Start with Option B (external Python script) for quick validation, then move to Option A for a verified pipeline if pursuing the paper angle.

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

1. **Session 11:** Refactor `StructIRToFlatIR.lean` proofs to use `Core/Tactics.lean`
2. **Session 12:** Build LLZK parser (Option B: Python script → `.lean` module)
3. **Session 13:** R1CS output (Circom `.r1cs` binary format)
4. **Session 14:** Test on a real circuit (e.g., Fibonacci, simple hash)
5. **Session 15:** Array support in StructIR
6. **Session 16+:** Optimization passes, paper writing
