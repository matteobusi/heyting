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
- **Preservation**: if `ws` satisfies the source, there exists a related `wt` satisfying the target (soundness — the compiler doesn't lose constraints)
- **Reflection**: if `wt` satisfies the target, there exists a related `ws` satisfying the source (completeness — the compiler doesn't add spurious constraints)

Together, these establish **equisatisfiability**: the source and compiled programs accept the same (related) witnesses.

This formulation follows the trace-relating compiler correctness framework of Abate et al. ("Trace-Relating Compiler Correctness and Secure Compilation", ESOP 2020). The `witnessRel` plays the role of the trace relation `~`. Preservation corresponds to TP^τ (forward property preservation) and reflection corresponds to CC~ (trace-relating compiler correctness). The trinitary equivalence (TP^σ ↔ CC~ ↔ TP^τ) is proved in `Heyting/Core/TrinitaryCC.lean`.

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

### FlatIR to R1CS pass (`Heyting/Passes/FlatIRToR1CS.lean`)

This pass is **fully verified** — preservation and reflection are proven for all 7 instruction types with no `sorry` and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Witness relation**: `∀ v, wt (.var v) = ws v` — each FlatIR variable maps directly to the corresponding R1CS program variable.

Each FlatIR instruction compiles to one or more R1CS constraints:

| Instruction | R1CS encoding |
|-------------|---------------|
| `assignAdd` | `1 * (src1 + src2) = dest` |
| `assignSub` | `1 * (src1 - src2) = dest` |
| `assignMul` | `src1 * src2 = dest` |
| `assignDiv` | `src2 * dest = src1` **and** `src2 * aux = 1` (forces `src2 != 0`) |
| `assignNeg` | `1 * (-src) = dest` |
| `assignConst` | `1 * c = dest` |
| `assertEq` | `1 * src1 = src2` |

Division uses a two-constraint encoding: the auxiliary constraint `src2 * aux = 1` ensures `src2` is invertible (and hence non-zero), making the reflection proof unconditional.

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

### StructIR to FlatIR pass (`Heyting/Passes/StructIRToFlatIR.lean`)

This pass flattens hierarchical StructIR modules into linear FlatIR instruction sequences by inlining all cross-struct `@constrain` calls.

**Compilation strategy:**

The pass walks the main struct's `@constrain` body, recursively inlining callee bodies for `call` statements. Each felt operation emits the corresponding FlatIR instruction, `constrainEq` emits `assertEq`, and `readMember` emits no instruction (the witness handles value injection). The compiler additionally emits zero-initialization constraints (`assignConst v 0` for all `v < initNext`) at the start of the compiled program — these constrain parameter positions to zero, which is required for reflection.

**Variable mapping (counter-based allocation):**

Each assignment (felt op, readMember) gets a fresh FlatIR variable ID from a monotonically increasing counter (`next`). A mapping `VarMap : LocalVar → FlatIR.VarId` tracks the current FlatIR variable for each StructIR local. This scheme is correct even for non-SSA programs where locals are reassigned.

| StructIR statement | FlatIR output | Allocation |
|--------------------|---------------|------------|
| `feltAdd dest src1 src2` | `assignAdd next (varMap src1) (varMap src2)` | `varMap[dest] := next`, `next += 1` |
| `feltSub`, `feltMul`, `feltDiv`, `feltNeg`, `feltConst` | Corresponding `assign*` | Same pattern |
| `readMember dest self member` | *(none)* | `varMap[dest] := next`, `next += 1` |
| `constrainEq src1 src2` | `assertEq (varMap src1) (varMap src2)` | No allocation |
| `call target args` | Inline callee body (recursive) | Callee uses same counter |

**Witness relation:**

The witness relation connects source and target witnesses through the **variable allocation map** (`buildVarAlloc`):

```
witnessRel p ws wt := ∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)
```

`buildVarAlloc` mirrors the structure of `compileConstrainBody` but instead of emitting instructions, it records which FlatIR variable ID each StructIR `(path, member)` read is allocated to. The relation says: for every StructIR variable that was read during compilation (i.e., whose allocation is non-zero), the source and target witnesses agree at that position.

**Preservation:**

`buildWitness` mirrors `compileConstrainBody` exactly in allocation, but records the computed value at each fresh variable. Preservation constructs `wt = compileWitness(ws)` and proves it satisfies the compiled FlatIR program. The zero-initialization prefix is satisfied because `buildWitness` starts from `acc = fun _ => 0`. The witness relation holds via `buildWitness_varAlloc_agree`: the constructed witness agrees with the source witness at all allocated positions.

**Reflection (backward simulation via `reflection_direct`):**

Reflection proves that if a FlatIR witness `wt` satisfies the compiled program and is related to some source witness `ws` via `witnessRel`, then `ws` satisfies the original StructIR program.

The proof uses `reflection_direct`, which works directly with `wt` (not through `buildWitness`). It maintains `WitnessCoherent wt varMap env` — that `wt(varMap v) = env v` — inductively through each statement:

- **Felt ops**: extract the satisfaction equation from `hsat`, derive the new local env value, update coherence
- **readMember**: no instruction emitted, but coherence needs `wt(next) = w(path, member)`. This follows from `witnessRel` + `NoDuplicateReads`: `buildVarAlloc` assigns `next` to `(path, member)`, and NoDuplicateReads ensures this is the final assignment (via `buildVarAlloc_preserves_absent`)
- **constrainEq**: derive equality from coherence + satisfaction
- **call**: build callee coherence from args mapping, recurse. `wt 0 = 0` (from zero-init constraints) handles unmapped callee params

**Proof status:**

Both preservation and reflection are **fully verified** (0 sorry, standard axioms only: `propext`, `Classical.choice`, `Quot.sound`).

Helper lemmas: `buildWitness_next_le`, `buildWitness_preserves_below`, `varMapBound_update`, `witnessCoherent_update_felt`, `buildWitness_compileConstrainBody_next`, `compileConstrainBody_next_le`, `compileConstrainBody_instrVars_bounded`, `acc_zero_of_update`, `buildVarAlloc_next_eq`, `buildVarAlloc_alloc_bound`, `buildWitness_varAlloc_agree`, `buildVarAlloc_preserves_absent`, `buildVarAlloc_acc_irrelevant`, `witnessCoherent_update_from_sat_*` (one per felt op).
