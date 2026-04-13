# Languages in Heyting

Heyting models ZKP compilation as a chain of **languages** connected by **correct passes**. Each language defines a program syntax and a satisfaction relation (`w |= p`), and each pass proves that compilation preserves and reflects that relation.

The current pipeline is:

```
StructIR  --->  FlatIR  --->  R1CS
(structs,       (flat          (A * B = C
 functions,      felt ops,      constraint
 nesting)        assertions)    system)
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

`satisfies w p` means witness `w` satisfies the constraints of program `p`. This is the only semantic notion — there is no execution model, just a declarative constraint relation.

### Pass and PresReflPass (`Heyting/Core/Pass.lean`)

```lean
class Pass (S : Language Vs Fs) (T : Language Vt Ft) where
  compile : S.Program → T.Program
  witnessRel : S.Program → Witness Vs Fs → Witness Vt Ft → Prop

class PreservingPass (S : Language Vs Fs) (T : Language Vt Ft) extends Pass S T where
  preservation : ∀ ws p, S.satisfies ws p →
    ∃ wt, witnessRel p ws wt ∧ T.satisfies wt (compile p)

class ReflectingPass (S : Language Vs Fs) (T : Language Vt Ft) extends Pass S T where
  reflection : ∀ wt p, T.satisfies wt (compile p) →
    ∃ ws, witnessRel p ws wt ∧ S.satisfies ws p

class PresReflPass (S : Language Vs Fs) (T : Language Vt Ft)
  extends PreservingPass S T, ReflectingPass S T
```

A `Pass` compiles programs and declares a **witness relation** `witnessRel` connecting source and target witnesses. The relation is per-program (since the variable mapping depends on the program structure).

A `PresReflPass` additionally proves two properties:
- **Reflection** (= CC~, trace-relating compiler correctness): if `wt` satisfies the target, there exists a related `ws` satisfying the source (soundness — the compiler doesn't lose constraints). This is the core correctness guarantee from Abate et al.
- **Preservation**: if `ws` satisfies the source, there exists a related `wt` satisfying the target (completeness — the compiler doesn't add spurious constraints). This is an additional guarantee beyond CC~.

Together, these establish **equisatisfiability**: the source and compiled programs accept the same (related) witnesses.

This formulation follows the trace-relating compiler correctness framework of Abate et al. ("Trace-Relating Compiler Correctness and Secure Compilation", ESOP 2020). The `witnessRel` plays the role of the trace relation `~`. Reflection corresponds to CC~ (trace-relating compiler correctness), which is equivalent to both TPσ and TPτ. Preservation is a separate, additional property. The trinitarian equivalence (TPσ ↔ CC~ ↔ TPτ) is proved in `Heyting/Core/TrinitaryCC.lean`.

---

## R1CS (`Heyting/Languages/R1CS.lean`)

**Variable type**: `R1CS.VarId` — tagged union of `varOne` (constant 1), `var n` (program variables), and `aux n` (auxiliary variables introduced by compilation).

**Program**: A list of constraints, each of the form `A * B = C` where `A`, `B`, `C` are linear combinations over variables.

**Satisfaction**: A witness `w` satisfies an R1CS system if `w varOne = 1` and every constraint `A * B = C` holds under `w`.

R1CS is the standard arithmetization target for ZKP backends (Groth16, Plonk, etc.). It is the lowest level in Heyting's pipeline.

---

## FlatIR (`Heyting/Languages/FlatIR.lean`)

**Variable type**: `Nat` — simple integer identifiers.

**Program**: A flat list of instructions over a field `F`:

| Instruction | Semantics |
|-------------|-----------|
| `assignAdd dest src1 src2` | `w[dest] = w[src1] + w[src2]` |
| `assignSub dest src1 src2` | `w[dest] = w[src1] - w[src2]` |
| `assignMul dest src1 src2` | `w[dest] = w[src1] * w[src2]` |
| `assignDiv dest src1 src2` | `w[src2] != 0` and `w[dest] = w[src1] * w[src2]^-1` |
| `assignNeg dest src` | `w[dest] = -w[src]` |
| `assignConst dest c` | `w[dest] = c` |
| `assertEq src1 src2` | `w[src1] = w[src2]` |

**Satisfaction**: A witness satisfies a FlatIR program if it satisfies every instruction.

FlatIR corresponds to LLZK's field-native operations (`felt.add`, `felt.sub`, `felt.mul`, `felt.div`, `felt.neg`, `felt.const`, `constrain.eq`). It is the result of flattening StructIR's hierarchical structure into a linear sequence.

See `docs/GUARANTEES.md` §Pass 2 for the full compilation table, witness relation, and proof strategy.

---

## StructIR (`Heyting/Languages/StructIR.lean`)

StructIR is the highest-level language in the pipeline. It captures LLZK's `struct`, `function`, `felt`, and `constrain` dialects — the core of any real ZKP circuit.

**Variable type**: `VarId = InstancePath × Nat` where `InstancePath = List Nat`. This tracks struct nesting: a member at path `[2, 0]` with index `1` means "the second member of the first sub-struct of the third sub-struct of the root".

**Program**: A `Module (n+1) F` — a collection of `n+1` struct definitions indexed in topological order, where the last struct (index `n`) is the main entry point.

### Design: intrinsic well-formedness

StructIR uses **dependent types** to make ill-formed programs unrepresentable:

```
Module (n+1) F
  structs : (i : Fin (n+1)) -> StructDef (n+1) i F
  noDupReads : (readPositions ...).Nodup

StructDef n i F
  members : List (MemberDecl n)
  constrain : ConstrainFunc n i F members.length
  compute   : ComputeFunc   n i F members.length
```

The key invariants are enforced by the type system:

1. **No cyclic calls**: A struct at index `i` can only call structs at index `j < i`, enforced by `call (target : Fin i)`. Since `Fin 0` is empty, leaf structs (index 0) cannot call anyone.

2. **No missing struct references**: `MemberType n` uses `substruct : Fin n` — only structs within the module can be referenced.

3. **No missing member references**: `readMember` and `writeMember` take `Fin numMembers` where `numMembers = members.length` — out-of-bounds access is unrepresentable.

4. **Automatic termination**: `evalConstrainBody` recurses on `(i, stmts.length)`. When struct `i` calls struct `j < i`, the first component decreases. When processing the next statement, the second component decreases. Lean accepts this without fuel or well-formedness predicates.

5. **No duplicate reads (NoDuplicateReads)**: The `Module` carries a `noDupReads` field asserting that `readPositions` (the list of all `(path, member)` pairs read during constrain body traversal) has no duplicates. This is an SSA-like well-formedness assumption needed for reflection: it ensures each member value is read into exactly one FlatIR variable, so the variable allocation map is injective at read positions.

### Struct definition

Each struct contains:
- **Members**: a list of `MemberDecl n` — each member is either `felt` or a `substruct (j : Fin n)` pointing to another struct in the module.
- **`@compute`**: witness generation function — felt arithmetic, `newStruct`, `writeMember`, and calls to other structs' `@compute`. Defines how to build the witness.
- **`@constrain`**: constraint generation function — felt arithmetic, `readMember`, `constrainEq`, and calls to other structs' `@constrain`. Defines the constraint system.

### Semantics

Only `@constrain` is interpreted by the `satisfies` predicate — witness generation (`@compute`) is a compilation concern, not a semantic one.

Evaluation maintains two environments:
- **`LocalEnv F`**: maps local variables (`Nat`) to field values — tracks felt computations
- **`ObjEnv`**: maps local variables to instance paths — tracks which struct instance a variable refers to

The `evalConstrainBody` function walks the statement list, threading both environments and accumulating constraints as a conjunction of `Prop`s:
- **Felt operations**: update the local environment
- **`readMember dest self member`**: reads `w(objEnv self, member)` into `env[dest]` and updates `objEnv[dest]` to `objEnv self ++ [member]` — this tracks the nested instance path so subsequent `call` statements on `dest` correctly resolve to the right sub-struct
- **`constrainEq`**: asserts equality of two local variables
- **`call target args`**: recursively evaluates the callee's `@constrain` body with fresh environments built from the arguments

### Examples

See `Heyting/Examples/StructIRExamples.lean` for 4 validated examples:

1. **Component1A** (single struct): two felt members with equality constraints
2. **Adder** (single struct): felt addition with constraint
3. **Divider** (single struct): felt division with non-zero and result constraints
4. **Wrapper + Component1A** (nested structs): wrapper calls nested component's constrain function, demonstrating correct `objEnv` threading through `readMember` + `call`

Each example includes `noDupReads` proofs, positive/negative satisfaction proofs, and compilation output (`#eval` for both StructIR→FlatIR and FlatIR→R1CS).

See `docs/GUARANTEES.md` §Pass 1 for the full compilation strategy, witness relation, and proof details.
