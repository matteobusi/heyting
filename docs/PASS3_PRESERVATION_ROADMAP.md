# Pass 3 Preservation Proof - Roadmap

**File**: `Heyting/Passes/MemberlessIRToFlatIR.lean`  
**Goal**: Prove `preservation` theorem (line 318)
**Status**: In progress

## Theorem Statement

```lean
theorem preservation (m : MemberlessIR.Module (n + 1) F)
    (mw : Nat → F)
    (h : MemberlessIR.satisfies mw m) :
    FlatIR.satisfies (compileModuleWitness m mw) (compile m)
```

**Meaning**: If a MemberlessIR witness `mw` satisfies a MemberlessIR module `m`, then the compiled 
witness `compileModuleWitness m mw` satisfies the compiled FlatIR program `compile m`.

## Strategy

The proof should follow the pattern from the old `StructIRToFlatIR` pass (which was removed when 
we split it into Pass 2 and Pass 3). The key steps are:

### 1. Key Invariant: Witness Agreement

Define and prove a helper lemma showing that `compileWitness` produces a witness that agrees with 
the MemberlessIR local environment on the variable map positions:

```lean
theorem compileWitness_agrees (m : MemberlessIR.Module n F)
    (mw : Nat → F) (i : Fin n) (vm : VarMap) (next : Nat)
    (memberSlot : Nat → Nat) (env : MemberlessIR.LocalEnv F)
    (stmts : List (MemberlessIR.Stmt n i F))
    (acc : FlatIR.VarId → F)
    (hEnv : ∀ v, env v = mw v)
    (hAcc : ∀ v, acc (vm v) = env v) :
    let (wt', _) := compileWitness m mw i vm next memberSlot env stmts acc
    ∀ v, wt' (vm v) = env v
```

**Proof approach**: Induction on `stmts`, showing each statement preserves the invariant.

### 2. Main Preservation by Joint Induction

Prove preservation using joint induction on `(i, stmts.length)` (termination metric):

```lean
theorem compileBody_preserves (m : MemberlessIR.Module n F)
    (mw : Nat → F) (i : Fin n) (vm : VarMap) (next : Nat)
    (memberSlot : Nat → Nat) (env : MemberlessIR.LocalEnv F)
    (stmts : List (MemberlessIR.Stmt n i F))
    (acc : FlatIR.VarId → F)
    (hEnv : ∀ v, env v = mw v)
    (hAcc : ∀ v, acc (vm v) = env v)
    (hSat : MemberlessIR.evalBody m i env stmts) :
    let (instrs, _) := compileBody m i vm next memberSlot stmts
    let (wt, _) := compileWitness m mw i vm next memberSlot env stmts acc
    ∀ instr ∈ instrs, FlatIR.satisfiesInstr wt instr
```

**Cases**:
- **Felt ops** (`feltAdd`, `feltSub`, `feltMul`, `feltDiv`, `feltNeg`, `feltConst`): 
  The compiled instruction is satisfied using the witness agreement invariant.
- **`constrainEq`**: Compiles to `assertEq`, satisfied by the MemberlessIR constraint.
- **`call`**: Recurse on callee body (termination by `j < i`), use IH.
- **`readMember`**: No instruction emitted, witness pre-populated from Pass 2.

### 3. Top-Level Preservation

Apply the helper theorem to the main function body:

```lean
theorem preservation (m : MemberlessIR.Module (n + 1) F)
    (mw : Nat → F)
    (h : MemberlessIR.satisfies mw m) :
    FlatIR.satisfies (compileModuleWitness m mw) (compile m) := by
  simp only [FlatIR.satisfies, MemberlessIR.satisfies, compile,
             compileModuleWitness] at *
  -- Set up initial conditions for compileBody_preserves
  let mainIdx := Fin.last n
  let initEnv := mw  -- Initial env is mw itself
  let initAcc := fun k => mw k  -- Initial accumulator for params
  -- Apply compileBody_preserves with initial conditions
  exact compileBody_preserves m mw mainIdx initVm initNext memberSlot
    initEnv (m mainIdx).body initAcc (by intro; rfl) (by intro; rfl) h
```

## Implementation Steps

1. **Start with `feltAdd` case**: Prove the simplest felt operation case completely.
2. **Generalize to other felt ops**: `feltSub`, `feltMul` follow the same pattern.
3. **Handle `feltDiv`**: Similar but needs non-zero check.
4. **Handle `constrainEq`**: Direct from MemberlessIR constraint.
5. **Handle `call`**: Use termination metric and inductive hypothesis.
6. **Handle `readMember`**: No instruction, witness value from Pass 2.
7. **Complete witness agreement helper**: Prove the invariant is maintained.
8. **Connect to top-level**: Instantiate with initial conditions.

## Key Lemmas Needed

1. **VarMap.update properties**: How variable map updates interact with lookups.
2. **Function update properties**: How `fun k => if k == v then x else f k` behaves.
3. **List membership after append**: Relating instructions in compiled sublists.
4. **Witness at allocated position**: Showing `wt next = computed_value` after allocation.

## References

- **Pass 4 (FlatIR → R1CS)**: Lines 200-250 in `FlatIRToR1CS.lean` — shows direct proof by cases
- **Pass 2 preservation**: Lines 190-500 in `StructInlineIRToMemberlessIR.lean` — shows agreement pattern
- **Old StructIRToFlatIR**: (removed file) — original pattern we're reconstructing

## Expected Difficulty

**Medium-High**. The call inlining case requires careful handling of the termination metric and 
inductive hypothesis. The witness agreement invariant requires threading through all statement cases. 
However, the structure is clear and each case is mechanical.

## Next Steps

Start with the `feltAdd` case in `compileWitness_agrees`, prove it completely, then generalize to 
other cases following the same pattern.
