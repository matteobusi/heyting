# Warnings, Assumptions, and Known Limitations

Tracking design decisions that involve trade-offs, assumptions, or incomplete guarantees.

---

## Resolved Issues (archived)

The following issues were identified and fully resolved. Kept here for historical context.

| # | Issue | File | Resolution |
|---|-------|------|------------|
| 1 | `assignDiv` reflection — single constraint was conditional on `src2 ≠ 0` | `FlatIRToR1CS.lean` | Two-constraint encoding: `src2 * dest = src1` + `src2 * aux(src2) = 1`. `aux` added to `R1CS.VarId`; `compileWitness` maps `aux v` to `(w v)⁻¹`. Proof now unconditional. |
| 2 | Fuel-bounded recursion in `evalConstrainBody` — fuel=0 was vacuously `True` | `StructIR.lean` | Replaced with intrinsic well-formedness: structs indexed topologically, `call` targets typed `Fin i`, members typed `Fin numMembers`. Termination by structural recursion on `(i, stmts.length)`. |
| 3 | `witnessRel = True` — reflection was vacuous | `StructIRToFlatIR.lean` | Meaningful relation `∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)` via `buildVarAlloc`. Added `readPositions`/`noDupReads`. Zero-init prefix for reflection. |
| 4 | `readMember` didn't update `objEnv[dest]` — nested struct calls used wrong path | `StructIR.lean`, `StructIRToFlatIR.lean` | All 4 functions (`evalConstrainBody`, `readPositions`, `compileWitness`, `buildVarAlloc`) now do `objEnv.update dest (path ++ [member.val])`. `readPositions` restructured from `let` bindings to direct case-split for reliable `simp` reduction. |

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
**Affects:** Fresh checkouts; `lake build hey` on machines without pre-built oleans

**Symptom:**
```
error: failed to GET URL, error 400; received:
{"error":{"status":400,"message":"Invalid platform: Unexpected characters in platform"}}
```

**Cause:** Lake 5.0.0 sends the full `uname -r`-based platform string (`arm64-apple-darwin24.6.0`) verbatim to the Reservoir API. The dots in the minor version (`24.6.0`) are rejected by Reservoir's input validation. This is a Lake bug — fixed in later Lake releases but not in v4.28.0's bundled Lake.

**Impact:** `lake cache get` silently falls back to building from source. The first full `lake build` (library only, no executable) takes ~30 minutes on a modern Mac. Subsequent incremental builds are fast.

**Workaround:** None needed for the library. For `lake build hey` (the executable), native compilation of all transitively imported Mathlib modules is required. Because the cache doesn't deliver `.c.o` files even when it works (it delivers oleans only), the linker may fail with `undefined symbol: initialize_mathlib_Mathlib_Tactic_*`. See the fix below.

---

## 7. `private axiom` for large CLI prime fields — Active

**Date:** 2026-04-13
**Status:** Active — intentional design decision
**Affects:** `Heyting/CLI.lean` only

The CLI supports 6 prime fields matching `llzk-lib/lib/Util/Field.cpp`. The primality facts
for `bn254`/`bn128` (254-bit prime) and `goldilocks` (Pseudo-Mersenne, but not the specific
form `norm_num` handles) cannot be verified at elaboration time by `native_decide` or
`norm_num`. Rather than blocking the CLI, their primality is declared via `private axiom`:

```lean
private axiom BN254_prime : Fact (Nat.Prime BN254_p)
private axiom GOLDILOCKS_prime : Fact (Nat.Prime GOLDILOCKS_p)
-- etc.
```

**Axiom isolation:** All 6 prime axioms are declared with `private` in `CLI.lean` and are
never imported into any `PresReflPass` proof file. Running `lean_verify` on any pass theorem
shows only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Fields whose primality is axiomatic:**
- `bn254` / `bn128`: same 254-bit prime — too large for `native_decide` in reasonable time
- `goldilocks`: 2⁶⁴ − 2³² + 1 — not recognized by `norm_num`'s Mersenne prime extension

**Fields whose primality is decidable:**
- `babybear`: 2013265921 — could use `native_decide` or `norm_num`
- `mersenne31`: 2147483647 — recognized as 2³¹ − 1 Mersenne prime
- `koalabear`: 2130706433 — could use `native_decide` or `norm_num`

For uniformity, all 6 fields use `private axiom` in the CLI. This keeps the code uniform
and avoids a two-tier treatment that would require separate proofs for the smaller fields.

**Impact on verified theorems:** None. The pass correctness theorems are generic over
`F : Type [Field F]` and do not depend on any specific prime.

---

**Linker fix for `undefined symbol: initialize_mathlib_Mathlib_Tactic_HigherOrder` (and similar):**

If `lake build hey` fails with an `ld64.lld: error: undefined symbol: initialize_mathlib_Mathlib_Tactic_*` error, the cause is a cache stub `.c.o.export` file with no symbols. Compile a minimal stub and overwrite it:

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

lake build hey
```

Replace `HigherOrder` and `initialize_mathlib_Mathlib_Tactic_HigherOrder` with whatever module name appears in the linker error. Repeat for each missing symbol.

---

## 8. Pass 2 semantic gap: `readMember` → `constrainEq` — Active

**Date:** 2026-04-29
**Status:** Active design question — blocks `PresReflPass` for Pass 2
**Affects:** `Heyting/Passes/StructInlineIRToMemberlessIR.lean`

### The issue

`StructInlineIRToMemberlessIR.compileStmt` currently compiles:

```
readMember dest self member  →  constrainEq dest (Nat.pair self member)
```

In StructInlineIR, `readMember dest self member` reads `w(objEnv self, member)` into
`env[dest]` (i.e., reads from the witness at the path tracked by `objEnv self`) and
updates `objEnv[dest] := objEnv self ++ [member]`. The key point: the path is given by
`objEnv self`, not by the value of the local variable `self`.

In MemberlessIR, `constrainEq dest k` asserts `menv[dest] = menv[k]`. So
`constrainEq dest (Nat.pair self member)` asserts that the witness value at slot `dest`
equals the witness value at slot `Nat.pair self member` — treating `self` (a local
variable ID, a `Nat`) as if it *encodes the path*.

This is only correct if `objEnv self` (the instance path currently stored for local
variable `self`) equals `VarIdEncoding.decode (Nat.pair self 0).1` — that is, if the
integer `self` encodes the path the ObjEnv has for it. After call inlining (Pass 1),
local variable IDs in StructInlineIR are not necessarily contiguous or path-encoding.

### Impact

Until this gap is resolved, neither preservation nor reflection can be proved for Pass 2.
The `Pass` instance is present but `PresReflPass` obligations are deferred.

### Options

1. **Redesign Pass 2 compilation.** Instead of `constrainEq dest (Nat.pair self member)`,
   pre-compute a concrete `InstancePath` for each `readMember` site during compilation and
   encode it as `VarIdEncoding.encode (path, member)`. This requires threading `objEnv`
   state through the compilation (as `compileWitness` already does). The `constrainEq`
   target becomes a concrete `Nat` constant, not a variable lookup.

2. **Strengthen StructInlineIR well-formedness.** Add a module-level invariant asserting
   that after inlining, each local variable's ObjEnv path is determined by its ID. This
   would be a strong structural property that may not hold in general.

3. **Change the MemberlessIR semantics.** Give MemberlessIR a separate `readSlot` notion
   that maps `(selfVarId, memberIdx)` to a slot, matching the StructInlineIR semantics
   more directly. This changes MemberlessIR's language design.

Option 1 is the most straightforward: the compilation mirrors what `compileWitness` already
does (it threads `ObjEnv` state), and the encoding becomes a static embedding rather than
a variable reference.
