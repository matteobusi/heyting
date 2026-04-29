# Formal Guarantees

This document details the formally verified guarantees provided by each
compiler pass. Every theorem listed as ✅ is machine-checked in Lean 4
with **0 sorries** and **standard axioms only** (`propext`,
`Classical.choice`, `Quot.sound`).

## Framework: `PresReflPass`

All passes target `PresReflPass S T` (defined in
`Heyting/Core/Pass.lean`), which bundles three components:

- **`compile`** — translates source programs to target programs.
- **`witnessRel`** — a relation connecting source and target witnesses,
  parameterized by the source program.
- **Reflection** (= CC~, trace-relating compiler correctness from Abate et
  al.) — if a target witness satisfies the compiled program, there exists
  a *related* source witness satisfying the source program. This is the
  core soundness guarantee: the compiler does not lose any constraints.
- **Preservation** — if a source witness satisfies the source program,
  there exists a *related* target witness satisfying the compiled program.
  This is a completeness guarantee beyond CC~: the compiler does not add
  spurious constraints.

Together, reflection and preservation give **equisatisfiability**: the
compiled program is satisfiable if and only if the source program is,
and witnesses on each side are connected through `witnessRel`.

### Field genericity

All pass instances are **generic over `F : Type [Field F]`** — the
theorems hold for any field, not just a specific prime. No `axiom`
appears in any pass proof file.

---

## Current pipeline

```
StructIR
  --[Pass 1: StructIRToStructInlineIR]----> StructInlineIR   ✅ PresReflPass
  --[Pass 2: StructInlineIRToMemberlessIR]-> MemberlessIR    ⚠️  Pass only
  --[Pass 3: MemberlessIRToFlatIR]---------> FlatIR          ⚠️  Pass only
  --[Pass 4: FlatIRToR1CS]-----------------> R1CS            ✅ PresReflPass
```

The end-to-end `Pipeline.Pass` instance composes all four passes but
only has a `Pass` instance (not `PresReflPass`) until passes 2 and 3 are
fully proved.

---

## Pass 1: StructIR → StructInlineIR ✅

**Source:** `Heyting/Passes/StructIRToStructInlineIR.lean`

### Languages

| | Language | Variable ID | Program type | Satisfaction |
|---|---|---|---|---|
| **Source** | `StructIR.Language n F` | `InstancePath × Nat` | `Module (n+1) F` — hierarchy of `n+1` struct definitions | `evalConstrainBody` on main struct's `@constrain` body |
| **Target** | `StructInlineIR.Language n F` | `InstancePath × Nat` (same) | `Module (n+1) F` — same index structure, but all `call` statements inlined | `evalConstrainBody` on main struct's `@constrain` body |

StructInlineIR retains `readMember`, `ObjEnv`, and the `VarId = InstancePath × Nat`
witness space from StructIR, but the `call` statement is absent — the
statement type has no `call` constructor. Every cross-struct call is
expanded in-place during compilation.

### Witness relation

```
witnessRel _m ws wi := wi = ws
```

The witness is unchanged (identity relation). Both source and target use
the same `VarId` space and the same `satisfies` seeding (`env k = w([], k)`).

### Compilation (`compileStruct`)

For each struct, `expandBody` walks the source constrain body and
replaces every `call target args` with:

1. A `feltConst zv 0` for a fresh zero-initialised slot `zv`.
2. The callee body, alpha-renamed so all its destination slots are fresh
   (via `inlineBody` with monotone counter `next` and substitution maps
   `valSubst`/`objSubst`).
3. Recursively expanded tail (the rest of the caller body).

Non-call statements pass through unchanged, preserving their local
variable IDs exactly.

### Key lemmas

- **`inlineBody_next_ge`**: the counter only increases.
- **`inlineBody_frame`**: running inlined code does not modify slots
  below `next` (proved by k-bounded strong induction `inlineBody_props`).
- **`inlineBody_correct`**: source `evalConstrainBody` ↔ inlined
  `StructInlineIR.evalConstrainBody` under the variable substitution
  (proved jointly with frame in `inlineBody_props`).
- **`evalConstrainBody_agree`**: if two source environments agree at all
  positions `< bound` and the body only references variables `< bound`,
  the evaluations are equivalent. Used in the `expandBody_correct` call
  case to bridge the post-inline state back to the original.
- **`expandBody_correct`**: the top-level iff between source and target
  evaluation.

### Preservation and reflection

Both follow from `expandBody_correct` applied at `maxVarBody + 1`:

```lean
preservation : StructIR.satisfies ws m → StructInlineIR.satisfies ws (compile m)
reflection   : StructInlineIR.satisfies wi (compile m) → StructIR.satisfies wi m
```

**Instance:** `StructIRToStructInlineIR.CorrectPass` — full `PresReflPass`.

---

## Pass 2: StructInlineIR → MemberlessIR ⚠️

**Source:** `Heyting/Passes/StructInlineIRToMemberlessIR.lean`

### Languages

| | Language | Variable ID | Program type | Satisfaction |
|---|---|---|---|---|
| **Source** | `StructInlineIR.Language n F` | `InstancePath × Nat` | `Module (n+1) F` — call-free, `readMember` present | `evalConstrainBody` with `ObjEnv` threading |
| **Target** | `MemberlessIR.instLanguage n F` | `Nat` | `Module (n+1) F` — no `readMember`, `call` still present | `evalBody` over flat `Nat` slots |

### Compilation

`readMember dest self member` → `constrainEq dest (Nat.pair self member)`.
All other statements pass through with identity variable IDs.

### Witness relation

```
witnessRel _m ws mw := ∀ k, mw k = ws (VarIdEncoding.decode k)
```

where `VarIdEncoding.encode : VarId → Nat` uses `Nat.pair` +
`Equiv.listNatEquivNat` to biject `InstancePath × Nat` onto `Nat`.
The forward witness is `mw k = ws (decode k)` and the backward witness
is `ws vid = mw (encode vid)`.

### Status and open obligation

The `Pass` instance is provided; `PresReflPass` obligations (preservation
and reflection) are **deferred** (phase-2 work).

**Semantic gap:** The compilation of `readMember` requires that at the
point of evaluation, local variable `self` carries enough information to
recover the full `ObjEnv self` path. This is only correct when StructInlineIR
programs have the property that `objEnv v` is determined by `v` alone.
Resolving this gap is the core obligation for proving pass 2. See
`docs/WARNING.md` §8.

---

## Pass 3: MemberlessIR → FlatIR ⚠️

**Source:** `Heyting/Passes/MemberlessIRToFlatIR.lean`

### Languages

| | Language | Variable ID | Program type | Satisfaction |
|---|---|---|---|---|
| **Source** | `MemberlessIR.instLanguage n F` | `Nat` | `Module (n+1) F` — flat felt ops + `call` | `evalBody` with recursive call inlining |
| **Target** | `FlatIR.Language F` | `Nat` | `List (Instr F)` — 7 instruction types, no calls | `∀ instr ∈ prog, satisfiesInstr w instr` |

### Compilation

`compileBody` walks the main struct's body:
- Felt ops → one FlatIR `assign*` instruction, allocating a fresh slot
  from a monotone counter.
- `constrainEq` → `assertEq (vm src1) (vm src2)`.
- `call` → recursively compile the callee body with a callee-local
  `VarMap` seeded from the call arguments; counter is shared (monotone
  across the whole compilation).

Variable allocation: `VarMap : LocalVar → FlatIR.VarId` translates
MemberlessIR local vars to FlatIR slots. Initial map is the identity on
`0..numParams-1`; the counter starts at `max numParams 1`.

### Witness relation

```
witnessRel m mw wt := wt = compileModuleWitness m mw
```

### Status

`witnessRel`, `compileWitness`, `extractWitness`, `buildVarMap` are all
defined. `PresReflPass` obligations (preservation and reflection) are
**deferred** (phase-2 work). The proof structure mirrors the old
`StructIRToFlatIR` pass: `compileWitness_agrees` invariant
(`∀ v, wt (vm v) = env v`), induction on `(i, stmts.length)`.

---

## Pass 4: FlatIR → R1CS ✅

**Source:** `Heyting/Passes/FlatIRToR1CS.lean`

### Languages

| | Language | Variable ID | Program type | Satisfaction |
|---|---|---|---|---|
| **Source** | `FlatIR.Language F` | `Nat` | `List (Instr F)` | `∀ instr ∈ prog, satisfiesInstr w instr` |
| **Target** | `R1CS.Language F` | `varOne \| var Nat \| aux Nat` | `System F` — list of `A·B = C` constraints | `w varOne = 1 ∧ ∀ c ∈ constraints, sat c` |

### Compilation

Each FlatIR instruction maps to one or two R1CS constraints:

| Instruction | R1CS constraint(s) |
|---|---|
| `assignAdd dest src1 src2` | `(src1 + src2) · 1 = dest` |
| `assignSub dest src1 src2` | `(src1 − src2) · 1 = dest` |
| `assignMul dest src1 src2` | `src1 · src2 = dest` |
| `assignNeg dest src` | `src · (−1) = dest` |
| `assignConst dest c` | `c · 1 = dest` |
| `assertEq src1 src2` | `src1 · 1 = src2` |
| `assignDiv dest src1 src2` | `src2 · dest = src1` and `src2 · aux(src2) = 1` |

The div encoding uses two constraints: the first captures the division
relation, and the second forces `src2 ≠ 0` by requiring an auxiliary
inverse variable.

### Witness relation

```
witnessRel _p ws wt := ∀ v, wt (.var v) = ws v
```

### Preservation and reflection

Both proved by case analysis on each instruction type. Single-constraint
instructions close via `r1cs_arith`. The div case additionally uses
`field_simp` with the non-zero hypothesis derived from
`src2 · aux(src2) = 1`.

**Instance:** `FlatIRToR1CS.CorrectPass` — full `PresReflPass`.

---

## End-to-end pipeline

`Pipeline.compileProgram` chains all four passes. The composed
`witnessRel` existentially quantifies over intermediate witnesses:

```lean
witnessRel m ws wr :=
  ∃ wi mw wf,
    StructIRToStructInlineIR.witnessRel m ws wi ∧
    StructInlineIRToMemberlessIR.witnessRel (compile1 m) wi mw ∧
    MemberlessIRToFlatIR.witnessRel (compile12 m) mw wf ∧
    FlatIRToR1CS.witnessRel (compile123 m) wf wr
```

Once passes 2 and 3 have `PresReflPass` instances, the full pipeline
`PresReflPass` follows by composition:
- **Preservation**: chain the four sub-pass preservation proofs.
- **Reflection**: chain the four sub-pass reflection proofs in reverse.

---

## Witness generation: `computeWitness`

**Source:** `Heyting/Languages/StructIR.lean`

`computeWitness` is a definitional interpreter for the `@compute` bodies
stored in every `StructDef`. It is *not* a compiler pass — it is an
entry point that produces a StructIR witness from public inputs, which
then flows into the `PresReflPass` chain.

**Status:** The interpreter (`evalComputeBody`) is fully defined and
elaborates correctly. The correctness theorem
`computeWitness m inputs = some w → StructIR.satisfies w m` is an
open obligation (no proof, no sorry — it simply does not exist yet).
