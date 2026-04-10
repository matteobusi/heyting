# Warnings, Assumptions, and Known Limitations

Tracking design decisions that involve trade-offs, assumptions, or incomplete guarantees.

---

## 1. `assignDiv` reflection — RESOLVED

**Date:** 2026-04-03
**Resolved:** 2026-04-03
**Affects:** `Heyting/Passes/FlatIRToR1CS.lean`

**Original issue:** The initial R1CS encoding of `assignDiv dest src1 src2` used a single constraint `src2 * dest = src1`. This correctly encodes `dest = src1 / src2` **only when `src2 ≠ 0`**, making reflection conditional.

**Resolution:** `compileInstr` now returns `List (Constraint F)` and emits two constraints for division:
1. `src2 * dest = src1` — encodes the division
2. `src2 * aux(src2) = 1` — forces `src2` to be invertible (hence non-zero)

An `aux : Nat → VarId` constructor was added to `R1CS.VarId`, and `compileWitness` maps `aux v` to `(w v)^-1`. Both preservation and reflection now hold unconditionally. Verified with `lean_verify`: no sorry, no custom axioms.

---

## 2. StructIR semantics uses fuel-bounded recursion — RESOLVED

**Date:** 2026-04-03
**Resolved:** 2026-04-03
**Affects:** `Heyting/Languages/StructIR.lean`

**Original issue:** Cross-struct `@constrain` calls were evaluated with a `fuel : Nat` parameter. When fuel ran out, constraints were vacuously `True`, making the semantics unsound for deeply nested programs.

**Resolution:** Replaced fuel-based recursion with **intrinsic well-formedness** via dependent types:
- Structs are indexed `0..n-1` in topological (dependency) order
- `call` targets are typed `Fin i` (callee index must be < current struct index)
- Members are indexed by `Fin numMembers`
- `evalConstrainBody` terminates by structural recursion on `(i, stmts.length)`

Cyclic calls, missing struct references, and missing member references are now **unrepresentable** by construction. No fuel, no silent failures, no well-formedness predicates needed.

---

## 3. StructIR → FlatIR pass: `witnessRel = True` — RESOLVED

**Date:** 2026-04-03
**Resolved:** 2026-04-07
**Affects:** `Heyting/Passes/StructIRToFlatIR.lean`

**Original issue:** The initial `CorrectPass` framework used a trivial witness relation (`witnessRel = True`). While provable, reflection was vacuous — any satisfiable target program could yield an unrelated source witness.

**Resolution:** Introduced a meaningful witness relation via `buildVarAlloc`:

```
witnessRel p ws wt := ∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)
```

This ties source and target witnesses together at all read positions through the variable allocation map. Required three supporting changes:

1. **`readPositions` + `noDupReads`** — the `Module` now carries a well-formedness field asserting that all `(path, member)` reads are unique (SSA-like condition).
2. **Zero-initialization constraints** — `compileProgram` emits `assignConst v 0` for `v < initNext` at the start of the compiled program.
3. **`reflection_direct`** — a backward simulation theorem working directly with `wt`.

Verified: 0 sorry, standard axioms only.

---

## 4. readMember/objEnv bug — RESOLVED

**Date:** 2026-04-07
**Resolved:** 2026-04-07
**Affects:** `Heyting/Languages/StructIR.lean`, `Heyting/Passes/StructIRToFlatIR.lean`

**Original issue:** `readMember dest self member` read `w(objEnv self, member.val)` into `env[dest]` but did NOT update `objEnv[dest]`. When `dest` was later passed to a `call`, the callee received `objEnv dest = []` (default) instead of the correct nested path. This broke nested struct semantics.

**Resolution:** All 4 functions that handle `readMember` now update `objEnv`:
- `evalConstrainBody`: `objEnv.update dest (path ++ [member.val])`
- `readPositions`: restructured from `let` bindings to direct case-split for clean `unfold`/`simp` interaction
- `buildWitness`: same update
- `buildVarAlloc`: same update

Additionally, `readPositions` was restructured from `let (stmtReads, objEnv') := match ...` to a direct case-split, because Lean's `unfold`/`simp` interaction with `let` bindings in recursive functions is unreliable for proof reduction.

Verified: nested struct example works correctly. 0 errors, 0 sorries.

---

## 5. NoDuplicateReads assumption

**Date:** 2026-04-07
**Status:** Active assumption
**Affects:** `Heyting/Languages/StructIR.lean`, `Heyting/Passes/StructIRToFlatIR.lean`

The `Module` structure carries a `noDupReads` field requiring that `readPositions` (the list of all `(path, member)` pairs read during `@constrain` body traversal) has no duplicates. This is an SSA-like well-formedness assumption: each struct member is read at most once.

**Why it's needed:** Reflection requires that the variable allocation map (`buildVarAlloc`) assigns each `(path, member)` to exactly one FlatIR variable. Without NoDuplicateReads, a member could be read twice into different FlatIR variables, and `buildVarAlloc_preserves_absent` (which ensures later allocations don't overwrite earlier ones) would fail.

**Scope:** This is a reasonable assumption for well-formed LLZK programs (struct members are typically read once into a local). If a program reads the same member twice, it can be trivially transformed to read once and reuse the local variable.

**Impact:** Programs that violate NoDuplicateReads cannot be represented as a `Module` — they fail at construction time (the `noDupReads` proof obligation is unsatisfiable).

---

## 6. `lake cache get` fails on macOS 15 (darwin24.6.0) — Active

**Date:** 2026-04-10
**Status:** Active — upstream Lake/Reservoir bug
**Affects:** Fresh checkouts; `lake build heytingc` on machines without pre-built oleans

**Symptom:**
```
error: failed to GET URL, error 400; received:
{"error":{"status":400,"message":"Invalid platform: Unexpected characters in platform"}}
```

**Cause:** Lake 5.0.0 sends the full `uname -r`-based platform string (`arm64-apple-darwin24.6.0`) verbatim to the Reservoir API. The dots in the minor version (`24.6.0`) are rejected by Reservoir's input validation. This is a Lake bug — fixed in later Lake releases but not in v4.28.0's bundled Lake.

**Impact:** `lake cache get` silently falls back to building from source. The first full `lake build` (library only, no executable) takes ~30 minutes on a modern Mac. Subsequent incremental builds are fast.

**Workaround:** None needed for the library. For `lake build heytingc` (the executable), native compilation of all transitively imported Mathlib modules is required. Because the cache doesn't deliver `.c.o` files even when it works (it delivers oleans only), the linker may fail with `undefined symbol: initialize_mathlib_Mathlib_Tactic_*`. See the fix below.

**Linker fix for `undefined symbol: initialize_mathlib_Mathlib_Tactic_HigherOrder` (and similar):**

If `lake build heytingc` fails with an `ld64.lld: error: undefined symbol: initialize_mathlib_Mathlib_Tactic_*` error, the cause is a cache stub `.c.o.export` file with no symbols. Compile a minimal stub and overwrite it:

```bash
# Find the missing module's .c.o.export path, e.g. for HigherOrder:
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

lake build heytingc
```

Replace `HigherOrder` and `initialize_mathlib_Mathlib_Tactic_HigherOrder` with whatever module name appears in the linker error. Repeat for each missing symbol.
