# Formal Guarantees

This document details the formally verified guarantees provided by each
compiler pass. Every theorem listed below is machine-checked in Lean 4
with **0 sorries** and **standard axioms only** (`propext`,
`Classical.choice`, `Quot.sound`).

## Framework: `PresReflPass`

All passes are instances of `PresReflPass S T` (defined in
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

---

## Pass 1: StructIR → FlatIR

**Source:** `Heyting/Passes/StructIRToFlatIR.lean`

### Languages

| | Language | Variable ID | Program type | Satisfaction |
|---|---|---|---|---|
| **Source** | `StructIR.Language n F` | `InstancePath × Nat` | `Module (n+1) F` — hierarchy of `n+1` struct definitions indexed topologically | `evalConstrainBody` on the main struct's `@constrain` body |
| **Target** | `FlatIR.Language F` | `Nat` | `List (Instr F)` — 7 instruction types: add, sub, mul, div, neg, const, assertEq | `∀ instr ∈ prog, satisfiesInstr w instr` |

StructIR models LLZK's hierarchical constraint system: structs contain
member fields and a `@constrain` body of felt operations, equality
assertions, member reads, and cross-struct calls. Structs are indexed by
`Fin (n+1)` in topological order, with `call` restricted to `Fin i`
(callees have smaller index), ensuring acyclicity by construction.

FlatIR is a straight-line list of assignments and assertions over natural
number variables, with no nesting or control flow.

### Compilation (`compileProgram`)

The compiler walks the main struct's `@constrain` body and recursively
inlines all cross-struct calls:

- **Felt ops** (add, sub, mul, div, neg, const) → one FlatIR `assign*`
  instruction, targeting a fresh variable from a monotonic counter.
- **`constrainEq a b`** → FlatIR `assertEq (varMap a) (varMap b)`.
- **`readMember dest path member`** → no FlatIR instruction emitted;
  the witness construction handles value injection.
- **`call target`** → recursively compile the callee's body, mapping
  callee parameters to the caller's variables.
- **Zero-init prefix** → `assignConst v 0` for each `v < initNext`,
  constraining parameter positions to zero (needed for reflection).

Variable allocation is counter-based: each felt op or readMember gets
the current counter value and increments it. This handles non-SSA
programs correctly (a local reassigned twice gets two distinct FlatIR
variables).

### Witness relation (`witnessRel`)

```
witnessRel p ws wt :=
  ∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)
```

where `varAlloc` is computed by `buildVarAlloc`, which mirrors the
compiler's traversal and records which FlatIR variable holds the value
of each `(instancePath, memberIndex)` pair at `readMember` sites.

The condition `varAlloc vid ≠ 0` restricts agreement to positions
actually read by the program — unread positions default to 0 in the
allocation map, and `initNext ≥ 1` ensures all real allocations are
positive.

**Requires `NoDuplicateReads`:** The source module must satisfy
`noDupReads` (each `(path, member)` read at most once). This is an SSA
well-formedness condition. Without it, `extractWitness` could assign
inconsistent values to the same StructIR variable.

### Preservation (completeness)

```lean
preservation :
  ∀ ws p, StructIR.satisfies ws p →
    ∃ wt, witnessRel p ws wt ∧ FlatIR.satisfies wt (compile p)
```

**Guarantee:** If a StructIR witness `ws` satisfies the module, there
exists a FlatIR witness `wt` — specifically `wt = buildWitness(ws)` —
that both (a) agrees with `ws` at all read positions and (b) satisfies
every compiled FlatIR instruction. This ensures the compiler does not
add spurious constraints that reject valid witnesses.

**Proof strategy:** The target witness `wt` is *constructed* by
`buildWitness`, which mirrors the compiler's traversal and evaluates
each StructIR operation to set the corresponding FlatIR variable.
The proof maintains a `WitnessCoherent wt varMap env` invariant:
`∀ v, wt (varMap v) = env v`, linking FlatIR variable values to the
StructIR local environment at each step. Each felt op updates both
`varMap` and `env` consistently, and the invariant is preserved through
calls and readMember operations. The zero-init prefix is satisfied
because `buildWitness` preserves values below the counter
(`buildWitness_preserves_below`).

### Reflection (= CC~, soundness)

```lean
reflection :
  ∀ wt p, FlatIR.satisfies wt (compile p) →
    ∃ ws, witnessRel p ws wt ∧ StructIR.satisfies ws p
```

**Guarantee:** If a FlatIR witness `wt` satisfies the compiled program,
there exists a StructIR witness `ws` — specifically
`ws = extractWitness(p, wt)` — that both (a) agrees with `wt` at all
read positions and (b) satisfies the original StructIR module. This is
CC~ (trace-relating compiler correctness): the compiler did not drop any
constraints, so anything satisfiable in FlatIR was already satisfiable
in StructIR.

**Proof strategy:** The source witness is `extractWitness(p, wt)`, which
reads FlatIR variable values back through the `buildVarAlloc` map
(`ws vid = wt (varAlloc vid)`). The witness relation holds
*definitionally* by this construction. Source satisfaction is proved by
`reflection_direct`, which uses `wt` directly (not `buildWitness`) and
maintains `WitnessCoherent wt varMap env` inductively. Initial coherence
comes from the zero-init prefix: `wt v = 0` for all parameter positions,
matching the initial environment `env = fun _ => 0`. Each felt op
extracts its satisfaction equation from FlatIR and updates the coherence
invariant. The `noDupReads` condition ensures that at `readMember` sites,
`extractWitness` assigns the correct value.

---

## Pass 2: FlatIR → R1CS

**Source:** `Heyting/Passes/FlatIRToR1CS.lean`

### Languages

| | Language | Variable ID | Program type | Satisfaction |
|---|---|---|---|---|
| **Source** | `FlatIR.Language F` | `Nat` | `List (Instr F)` | `∀ instr ∈ prog, satisfiesInstr w instr` |
| **Target** | `R1CS.Language F` | `varOne \| var Nat \| aux Nat` | `System F` — a list of `A·B = C` constraints | `w varOne = 1 ∧ ∀ c ∈ constraints, (evalLinComb w A) * (evalLinComb w B) = (evalLinComb w C)` |

R1CS (Rank-1 Constraint System) is the standard arithmetization format
for ZKP backends (Groth16, Marlin, etc.). Each constraint is a
bilinear equation `⟨A, w⟩ · ⟨B, w⟩ = ⟨C, w⟩` over linear combinations
of witness variables.

### Compilation (`compileProgram`)

Each FlatIR instruction maps to one or two R1CS constraints:

| Instruction | R1CS constraint(s) | Encoding |
|---|---|---|
| `assignAdd dest src1 src2` | 1 | `(src1 + src2) · 1 = dest` |
| `assignSub dest src1 src2` | 1 | `(src1 - src2) · 1 = dest` |
| `assignMul dest src1 src2` | 1 | `src1 · src2 = dest` |
| `assignNeg dest src` | 1 | `src · (-1) = dest` |
| `assignConst dest c` | 1 | `c · 1 = dest` |
| `assertEq src1 src2` | 1 | `src1 · 1 = src2` |
| `assignDiv dest src1 src2` | 2 | `src2 · dest = src1` and `src2 · aux(src2) = 1` |

The div encoding uses two constraints: the first captures the division
relation, and the second forces `src2` to be invertible (hence non-zero)
by requiring the existence of an auxiliary variable `aux(src2)` such
that `src2 · aux(src2) = 1`.

### Witness relation (`witnessRel`)

```
witnessRel _p ws wt := ∀ v, wt (.var v) = ws v
```

The R1CS witness extends the FlatIR witness: every FlatIR variable `v`
maps to R1CS variable `.var v` with the same value. The relation is
independent of the program — it simply requires that the target witness
embeds the source witness.

### Compilation witness (`compileWitness`)

For preservation, the target witness is:

```
compileWitness w = fun
  | .varOne => 1
  | .var v  => w v
  | .aux v  => (w v)⁻¹
```

It sets `varOne = 1`, preserves FlatIR values, and provides auxiliary
inverse witnesses needed by the div encoding.

### Preservation (completeness)

```lean
preservation :
  ∀ ws p, FlatIR.satisfies ws p →
    ∃ wt, (∀ v, wt (.var v) = ws v) ∧ R1CS.satisfies wt (compile p)
```

**Guarantee:** If a FlatIR witness `ws` satisfies every instruction,
then `compileWitness(ws)` satisfies the R1CS system and agrees with
`ws` on all program variables. This ensures the compiler does not add
spurious constraints that reject valid witnesses.

**Proof strategy:** Case analysis on each instruction type. For
single-constraint instructions (add, sub, mul, neg, const, assertEq),
the proof unfolds both sides to a field equation and closes with
`r1cs_arith` (a custom tactic trying `linear_combination`,
`ring_nf`, `field_simp`, `aesop`). The div case requires handling two
constraints separately: the division equation uses `field_simp` with the
non-zero hypothesis, and the invertibility constraint follows from
`w(src2) · (w(src2))⁻¹ = 1`.

### Reflection (= CC~, soundness)

```lean
reflection :
  ∀ wt p, R1CS.satisfies wt (compile p) →
    ∃ ws, (∀ v, wt (.var v) = ws v) ∧ FlatIR.satisfies ws p
```

**Guarantee:** If an R1CS witness `wt` satisfies the compiled system,
then the FlatIR witness `extractWitness(wt) = fun v => wt (.var v)`
satisfies every original instruction. This is CC~: the compiler did not
drop any constraints, so every satisfying R1CS assignment corresponds to
a valid FlatIR execution.

**Proof strategy:** Case analysis on each instruction type, extracting
the R1CS satisfaction equations and converting them back to FlatIR
semantics. The div case is the most involved: the invertibility
constraint `src2 · aux = 1` proves `src2 ≠ 0`, and then `field_simp`
converts `src2 · dest = src1` into `dest = src1 · src2⁻¹`.

---

## End-to-end pipeline

By composing both passes, we get a verified pipeline from StructIR to
R1CS. Given a StructIR module `m`:

1. `StructIRToFlatIR.compileProgram m` produces a flat program.
2. `FlatIRToR1CS.compileProgram (StructIRToFlatIR.compileProgram m)`
   produces an R1CS system.

**Reflection (CC~) at each stage** guarantees soundness: if the R1CS
system is satisfiable, the original StructIR module is satisfiable.
**Preservation at each stage** guarantees completeness: if the StructIR
module is satisfiable, the R1CS system is satisfiable.

Together: the R1CS system is satisfiable **if and only if** the original
StructIR module is satisfiable, with witnesses related through the
composition of `witnessRel` relations.
