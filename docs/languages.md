# Languages in Heyting

Heyting models ZKP compilation as a chain of **languages** connected by **correct passes**. Each language defines a program syntax and a satisfaction relation (`w |= p`), and each pass proves that compilation preserves and reflects that relation.

The current pipeline is:

```
StructIR  --->  StructInlineIR  --->  MemberlessIR  --->  FlatIR  --->  R1CS
(structs,       (call-free;            (no readMember;      (flat          (A * B = C
 calls,          readMember             calls still          felt ops,      constraint
 readMember)     preserved)             present)             assertions)    system)
```

---

## Core Abstractions

All languages and passes are **generic over the field `F : Type [Field F]`**. Examples and
tests instantiate `F := ZMod 1993` (a small prime, fast `native_decide`). The CLI selects
a concrete field at the boundary via `--prime-field`; no proof-bearing code is
parameterized on a specific prime.

### Language (`Heyting/Core/Language.lean`)

```lean
class Language (V : Type) (F : Type) [Field F] where
  Program : Type
  satisfies : Witness V F -> Program -> Prop
```

A language is parameterized by:
- `V`: the type of variable identifiers (how witnesses are indexed)
- `F`: the field type (e.g., a prime field)

`satisfies w p` means witness `w` satisfies the constraints of program `p`.

### Pass and PresReflPass (`Heyting/Core/Pass.lean`)

```lean
class Pass (S : Language Vs Fs) (T : Language Vt Ft) where
  compile : S.Program → T.Program
  witnessRel : S.Program → Witness Vs Fs → Witness Vt Ft → Prop

class PreservingPass extends Pass where
  preservation : ∀ ws p, S.satisfies ws p →
    ∃ wt, witnessRel p ws wt ∧ T.satisfies wt (compile p)

class ReflectingPass extends Pass where
  reflection : ∀ wt p, T.satisfies wt (compile p) →
    ∃ ws, witnessRel p ws wt ∧ S.satisfies ws p

class PresReflPass extends PreservingPass, ReflectingPass
```

A `PresReflPass` establishes **equisatisfiability**: source and compiled programs accept
the same (related) witnesses. Reflection (= CC~) is soundness; preservation is completeness.

This formulation follows the trace-relating compiler correctness framework of Abate et al.
("Trace-Relating Compiler Correctness and Secure Compilation", ESOP 2020). The trinitarian
equivalence (TPσ ↔ CC~ ↔ TPτ) is proved in `Heyting/Core/TrinitaryCC.lean`.

---

## R1CS (`Heyting/Languages/R1CS.lean`)

**Variable type**: `R1CS.VarId` — tagged union of `varOne` (constant 1), `var n` (program variables), and `aux n` (auxiliary variables introduced by `assignDiv`).

**Program**: A list of constraints, each of the form `A * B = C` where `A`, `B`, `C` are linear combinations over variables.

**Satisfaction**: A witness `w` satisfies an R1CS system if `w varOne = 1` and every constraint `A * B = C` holds under `w`.

R1CS is the standard arithmetization target for ZKP backends (Groth16, Plonk, etc.).

---

## FlatIR (`Heyting/Languages/FlatIR.lean`)

**Variable type**: `Nat` — simple integer identifiers.

**Program**: A flat list of instructions over a field `F`:

| Instruction | Semantics |
|-------------|-----------|
| `assignAdd dest src1 src2` | `w[dest] = w[src1] + w[src2]` |
| `assignSub dest src1 src2` | `w[dest] = w[src1] - w[src2]` |
| `assignMul dest src1 src2` | `w[dest] = w[src1] * w[src2]` |
| `assignDiv dest src1 src2` | `w[src2] ≠ 0` and `w[dest] = w[src1] * w[src2]⁻¹` |
| `assignNeg dest src` | `w[dest] = -w[src]` |
| `assignConst dest c` | `w[dest] = c` |
| `assertEq src1 src2` | `w[src1] = w[src2]` |

**Satisfaction**: A witness satisfies a FlatIR program if it satisfies every instruction.

FlatIR has no `call` statement and no struct hierarchy. It is the output of
`MemberlessIRToFlatIR` (Pass 3) and the input to `FlatIRToR1CS` (Pass 4).

---

## MemberlessIR (`Heyting/Languages/MemberlessIR.lean`)

**Variable type**: `Nat` — flat natural number slots.

**Program**: A `Module (n+1) F` — a collection of `Func` definitions indexed topologically.
Each `Func` has `numParams : Nat` and `body : List (Stmt n i F)`.

**Statements**:

| Statement | Effect on `evalBody` |
|-----------|----------------------|
| Felt ops (add/sub/mul/div/neg/const) | Update `env[dest]` |
| `constrainEq src1 src2` | Assert `env[src1] = env[src2]` |
| `call target args` | Recurse into callee body with args-seeded env |

There is no `readMember` — struct member access has been erased. There is no
`ObjEnv` threading. The witness is `Nat → F`.

**Satisfaction**: `evalBody m mainIdx initEnv (m mainIdx).body` where
`initEnv k = w k` (the witness seeds the initial environment).

MemberlessIR sits between StructInlineIR and FlatIR. Pass 2
(`StructInlineIRToMemberlessIR`) eliminates struct-member access. Pass 3
(`MemberlessIRToFlatIR`) inlines the remaining `call` statements and
produces a flat list.

---

## StructInlineIR (`Heyting/Languages/StructInlineIR.lean`)

**Variable type**: `VarId = InstancePath × Nat` — same as StructIR.

**Program**: A `Module (n+1) F` — a collection of `StructDef` definitions, each with a
`ConstrainFunc` body. Call-free by construction: the `ConstrainStmt` type has no `call`
constructor.

**Statements**:

| Statement | Effect on `evalConstrainBody` |
|-----------|-------------------------------|
| Felt ops (add/sub/mul/div/neg/const) | Update `env[dest]` |
| `readMember dest self member` | `env[dest] = w(objEnv self, member)`; update `objEnv[dest]` |
| `constrainEq src1 src2` | Assert `env[src1] = env[src2]` |

No `call` statement. Every cross-struct dependency has been inlined into the caller's body
by Pass 1 (`StructIRToStructInlineIR`).

**Evaluation** uses the same `ObjEnv` threading as StructIR: `readMember` reads from the
witness `w` using the current instance path and updates `objEnv[dest]` to
`objEnv self ++ [member]` for subsequent nested accesses.

**Satisfaction**: same seeding as StructIR — `env k = w([], k)` for the main struct.

**Witness**: `VarId → F`, same as StructIR. The witness space does not change at Pass 1.

StructInlineIR sits between StructIR and MemberlessIR. It cleanly separates two concerns:
- Pass 1 handles **call inlining** (StructIR → StructInlineIR), leaving `readMember` intact.
- Pass 2 handles **readMember elimination** (StructInlineIR → MemberlessIR), changing the witness space.

---

## StructIR (`Heyting/Languages/StructIR.lean`)

StructIR is the highest-level language in the pipeline. It captures LLZK's `struct`,
`function`, `felt`, and `constrain` dialects.

**Variable type**: `VarId = InstancePath × Nat` where `InstancePath = List Nat`. This tracks
struct nesting: a member at path `[2, 0]` with index `1` means "the second member of the
first sub-struct of the third sub-struct of the root".

**Program**: A `Module (n+1) F` — a collection of `n+1` struct definitions indexed in
topological order (leaves first, main last at index `n`).

### Design: intrinsic well-formedness

StructIR uses **dependent types** to make ill-formed programs unrepresentable:

1. **No cyclic calls**: `call (target : Fin i)` — callees have smaller index.
2. **No missing struct references**: `MemberType n` uses `substruct : Fin n`.
3. **No missing member references**: `readMember` takes `Fin numMembers`.
4. **Automatic termination**: `evalConstrainBody` recurses on `(i, stmts.length)`.
5. **No duplicate reads**: `Module` carries `noDupReads` — each `(path, member)` read
   at most once across the constrain traversal tree.
6. **SSA (isSSA)**: each destination variable written at most once per constrain body.
7. **Def-before-use (isDefBeforeUse)**: every source variable is either a parameter or
   the destination of an earlier statement.

### Statements

| Statement | Effect on `evalConstrainBody` |
|-----------|-------------------------------|
| Felt ops | Update `env[dest]` |
| `readMember dest self member` | `env[dest] = w(objEnv self, member)`; update `objEnv[dest]` |
| `constrainEq src1 src2` | Assert `env[src1] = env[src2]` |
| `call target args` | Recurse into callee's `@constrain` body with args-seeded envs |

### Satisfaction

`evalConstrainBody m w mainIdx (fun k => w([], k)) initObjEnv m.main.constrain.body`

The main struct's initial env is seeded from the witness at the root path: `env k = w([], k)`.

### Compute interpreter

`evalComputeBody` interprets `@compute` bodies to produce witnesses, threading
`ComputeState {env, objEnv, acc, nextPath}`. Used by `computeWitness` (entry point for
public inputs). Not a compiler pass — an interpreter.

### Examples

See `Heyting/Examples/StructIRExamples.lean` for 4 validated examples:
- **Component1A**: two felt members with equality constraints
- **Adder**: felt addition with constraint
- **Divider**: felt division with non-zero and result constraints
- **Wrapper + Component1A**: nested structs with `readMember` + `call`
