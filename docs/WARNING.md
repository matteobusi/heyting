# Warnings, Assumptions, Known Limitations

Trade-offs, assumptions, incomplete guarantees.

---

## Resolved Issues (archived)

Fully resolved. Kept for history.

| # | Issue | File | Resolution |
|---|-------|------|------------|
| 1 | `assignDiv` reflection — single constraint conditional on `src2 ≠ 0` | `FlatIRToR1CS.lean` | Two-constraint encoding: `src2 * dest = src1` + `src2 * aux(src2) = 1`. `aux` added to `R1CS.VarId`; `compileWitness` maps `aux v` → `(w v)⁻¹`. Proof unconditional. |
| 2 | Fuel-bounded recursion in `evalConstrainBody` — fuel=0 vacuously `True` | `StructIR.lean` | Intrinsic well-formedness: structs indexed topologically, `call` targets typed `Fin i`, members typed `Fin numMembers`. Termination by structural recursion on `(i, stmts.length)`. |
| 3 | `witnessRel = True` — reflection vacuous | `StructIRToFlatIR.lean` | Meaningful relation `∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)` via `buildVarAlloc`. Added `readPositions`/`noDupReads`. Zero-init prefix for reflection. |
| 4 | `readMember` didn't update `objEnv[dest]` — nested struct calls used wrong path | `StructIR.lean`, `StructIRToFlatIR.lean` | All 4 functions (`evalConstrainBody`, `readPositions`, `compileWitness`, `buildVarAlloc`) do `objEnv.update dest (path ++ [member.val])`. `readPositions` restructured from `let` bindings to direct case-split for reliable `simp` reduction. |

---

## 5. NoDuplicateReads assumption

**Date:** 2026-04-07
**Status:** Active
**Affects:** `Heyting/Languages/StructIR.lean`, `Heyting/Passes/StructIRToFlatIR.lean`

Module carries `noDupReads` field requiring `readPositions` (list of all `(path, member)` read during `@constrain` body traversal) has no duplicates. SSA-like well-formedness: each struct member read at most once.

**Why needed:** Reflection requires `buildVarAlloc` assigns each `(path, member)` to exactly one FlatIR variable. Without NoDuplicateReads, member could be read twice into different FlatIR variables, and `buildVarAlloc_preserves_absent` (ensures later allocations don't overwrite earlier) would fail.

**Scope:** Reasonable assumption for well-formed LLZK programs (struct members typically read once into local). Reads same member twice can be trivially transformed to read once and reuse local.

**Impact:** Programs violating NoDuplicateReads cannot be `Module` — fail at construction (`noDupReads` proof obligation unsatisfiable).

---

## 6. `lake cache get` fails on macOS 15 (darwin24.6.0) — Active

**Date:** 2026-04-10
**Status:** Active — upstream Lake/Reservoir bug
**Affects:** Fresh checkouts; `lake build hey` on machines without pre-built oleans

**Symptom:**
```
error: failed to GET URL, error 400; received:
{"error":{"status":400,"message":"Invalid platform: Unexpected characters in platform"}}
```

**Cause:** Lake 5.0.0 sends full `uname -r`-based platform string (`arm64-apple-darwin24.6.0`) verbatim to Reservoir API. Dots in minor version (`24.6.0`) rejected by Reservoir input validation. Lake bug — fixed in later releases but not in v4.28.0's bundled Lake.

**Impact:** `lake cache get` silently falls back to source build. First full `lake build` (library only) takes ~30 min on modern Mac. Incremental builds fast.

**Workaround:** None needed for library. For `lake build hey`, native compilation of all transitively imported Mathlib modules required. Cache doesn't deliver `.c.o` files (only oleans), so linker may fail with `undefined symbol: initialize_mathlib_Mathlib_Tactic_*`. See fix below.

---

## 7. `private axiom` for large CLI prime fields — Active

**Date:** 2026-04-13
**Status:** Active — intentional design
**Affects:** `Heyting/CLI.lean` only

CLI supports 6 prime fields matching `llzk-lib/lib/Util/Field.cpp`. Primality for `bn254`/`bn128` (254-bit) and `goldilocks` (Pseudo-Mersenne, not form `norm_num` handles) can't be verified at elaboration by `native_decide`/`norm_num`. Declared via `private axiom`:

```lean
private axiom BN254_prime : Fact (Nat.Prime BN254_p)
private axiom GOLDILOCKS_prime : Fact (Nat.Prime GOLDILOCKS_p)
-- etc.
```

**Axiom isolation:** All 6 prime axioms `private` in `CLI.lean`, never imported into `PresReflPass` proof files. `lean_verify` on any pass theorem shows only 3 standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Fields with axiomatic primality:**
- `bn254` / `bn128`: same 254-bit prime — too large for `native_decide`
- `goldilocks`: 2⁶⁴ − 2³² + 1 — not recognized by `norm_num`'s Mersenne extension

**Fields with decidable primality:**
- `babybear`: 2013265921 — `native_decide`/`norm_num` work
- `mersenne31`: 2147483647 — 2³¹ − 1 Mersenne prime
- `koalabear`: 2130706433 — `native_decide`/`norm_num` work

For uniformity, all 6 use `private axiom` in CLI. Keeps code uniform, avoids two-tier treatment with separate proofs for smaller fields.

**Impact on verified theorems:** None. Pass correctness theorems generic over `F : Type [Field F]`, independent of specific prime.

---

**Linker fix for `undefined symbol: initialize_mathlib_Mathlib_Tactic_HigherOrder` (and similar):**

If `lake build hey` fails with `ld64.lld: error: undefined symbol: initialize_mathlib_Mathlib_Tactic_*`, cause is cache stub `.c.o.export` file with no symbols. Compile minimal stub and overwrite:

```bash
# Find missing module's .c.o.export path, e.g. for HigherOrder:
EXPORT=.lake/packages/mathlib/.lake/build/ir/Mathlib/Tactic/HigherOrder.c.o.export
MODULE=initialize_mathlib_Mathlib_Tactic_HigherOrder

cat > /tmp/stub.c << EOF
#include <stdint.h>
typedef struct lean_object lean_object;
lean_object* ${MODULE}(uint8_t builtin) {
  extern lean_object* lean_io_result_mk_ok(lean_object*);
  extern lean_object* lean_box(size_t);
  return lean_io_result_mk_ok(lean_box(0));
}
EOF

xcrun clang -target arm64-apple-macos12 -o "$EXPORT" -c /tmp/stub.c \
  -I "$(lean --print-prefix)/include"

lake build hey
```

Replace `HigherOrder` and `initialize_mathlib_Mathlib_Tactic_HigherOrder` with whatever module name appears in linker error. Repeat for each missing symbol.

---

## 8. Pass 2 semantic gap: `readMember` → `constrainEq` — Historical

**Date:** 2026-04-29
**Status:** Historical note from removed intermediate pipeline
**Affects:** old `Heyting/Passes/StructInlineIRToMemberlessIR.lean`

### Issue

`StructInlineIRToMemberlessIR.compileStmt` compiles:

```
readMember dest self member  →  constrainEq dest (Nat.pair self member)
```

In StructInlineIR, `readMember dest self member` reads `w(objEnv self, member)` into `env[dest]` (reads from witness at path tracked by `objEnv self`) and updates `objEnv[dest] := objEnv self ++ [member]`. Path given by `objEnv self`, not value of local `self`.

In MemberlessIR, `constrainEq dest k` asserts `menv[dest] = menv[k]`. So `constrainEq dest (Nat.pair self member)` asserts witness at `dest` equals witness at `Nat.pair self member` — treats `self` (local var ID, `Nat`) as if it *encodes the path*.

This is only correct if `objEnv self` equals `VarIdEncoding.decode (Nat.pair self 0).1` — i.e., `self` encodes its ObjEnv path. After call inlining (Pass 1), StructInlineIR local var IDs not necessarily contiguous or path-encoding.

### Impact

This blocked old intermediate pipeline. It does not block current active direct executable path.

### Options

1. **Redesign Pass 2 compilation.** Instead of `constrainEq dest (Nat.pair self member)`, pre-compute concrete `InstancePath` for each `readMember` site during compilation and encode as `VarIdEncoding.encode (path, member)`. Requires threading `objEnv` state through compilation (as `compileWitness` already does). `constrainEq` target becomes concrete `Nat` constant, not variable lookup.

2. **Strengthen StructInlineIR well-formedness.** Add module-level invariant: after inlining, each local variable's ObjEnv path determined by its ID. Strong structural property may not hold generally.

3. **Change MemberlessIR semantics.** Add `readSlot` notion mapping `(selfVarId, memberIdx)` to slot, matching StructInlineIR semantics more directly. Changes MemberlessIR language design.

Option 1 most straightforward: compilation mirrors `compileWitness` (threads `ObjEnv` state), encoding becomes static embedding rather than variable reference.
