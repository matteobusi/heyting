# Proof Tactics

Custom tactics for automating recurring proof patterns in compiler pass
correctness proofs. Defined in `Heyting/Passes/Tactics.lean`.

## `r1cs_arith`

Closes R1CS field-arithmetic goals after all definitions have been unfolded
to raw field expressions.

**What it does:** Tries the following closers in order:

1. `linear_combination h.symm` — handles add, sub, mul, neg, const preservation
2. `linear_combination h` — handles assertEq
3. `simp_all` with arithmetic lemmas — handles simple reflection cases
4. `ring_nf` + `simp_all` — handles cases needing normalization first
5. `ring_nf` + `aesop` — handles neg reflection
6. `field_simp` + `aesop` — handles div
7. `aesop` — fallback

**Prerequisite:** Unfold pass-specific definitions (`compileVar`, `compileWitness`,
`extractWitness`) and R1CS core definitions (`R1CS.satisfiesLinComb`,
`R1CS.evalLinComb`, `FlatIR.satisfiesInstr`, `List.foldl`) before calling.

### Usage in FlatIR-to-R1CS preservation

Each single-constraint case (add, sub, mul, neg, const, assertEq):

```lean
| assignAdd dest src1 src2 =>
  simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
  simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
        compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
  r1cs_arith
```

The div case (two constraints) still needs manual `obtain`/`rcases`/`constructor`
but each sub-goal can use `field_simp` or the standard R1CS unfolding.

### Usage in FlatIR-to-R1CS reflection

Each single-constraint case:

```lean
| assignAdd dest src1 src2 =>
  simp only [compileInstr, List.forall_mem_cons] at h_all
  simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
        extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
  r1cs_arith
```

### Limitations

- Does **not** handle div (two constraints require manual decomposition)
- Must unfold pass-specific names at the call site (macro hygiene prevents
  hardcoding namespace-local names like `compileVar`)

## `r1cs_unfold_sat`

Unfolds `R1CS.satisfiesLinComb`, `R1CS.evalLinComb`, and `List.foldl` in all
hypotheses and the goal. Convenience shortcut for the common unfolding step.

```lean
r1cs_unfold_sat
-- equivalent to:
-- simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, List.foldl] at *
```

## Design decisions

### Why no `split_compiled_instrs` or `heyting_unfold_body`

We considered macros for:
- Splitting constraint membership (`compileInstr` unfolding + `subst`)
- Unfolding the `compileConstrainBody`/`compileWitness`/`evalConstrainBody` triple

Both were rejected because Lean 4 macro hygiene renames identifiers defined
in other namespaces. A macro in `Tactics.lean` referencing `compileInstr`
(defined in `FlatIRToR1CS`) would produce `FlatIRToR1CS.compileInstr✝` at
the expansion site, which `simp` cannot resolve. The workaround (passing the
identifier as a parameter) doesn't save enough boilerplate to justify the
extra syntax.

### Structural proofs use explicit local lemmas

Call and StructObject proofs recurse over typed statements and static state.
Keep pass-specific unfolding and frame/simulation lemmas near each pass.
Generic macros should not hide structural state transitions or exact lowering
equations needed by whole-artifact composition.

## Adding a new FlatIR instruction

When adding a new single-constraint instruction (e.g., `assignPow`):

1. Add the case to `compileInstr` (produces one `R1CS.Constraint`)
2. In `preservation`, add:
   ```lean
   | assignPow dest src exp =>
     simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
     simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
           compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
     r1cs_arith  -- will try linear_combination, ring_nf, etc.
   ```
3. In `reflection`, add:
   ```lean
   | assignPow dest src exp =>
     simp only [compileInstr, List.forall_mem_cons] at h_all
     simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
           extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
     r1cs_arith
   ```
4. If `r1cs_arith` fails, the goal will be a field equation — close it
   manually with `linear_combination`, `ring`, or `field_simp`.
