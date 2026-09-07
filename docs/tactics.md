# Proof tactics

The custom tactics in `Heyting/Passes/Tactics.lean` operate on field equations.
The active backend uses them in `Heyting/Dialects/R1CSLike.lean`.

## `r1cs_unfold_sat`

Unfolds `R1CS.satisfiesLinComb`, `R1CS.evalLinComb`, and `List.foldl` in the
goal and hypotheses. Pass-specific syntax must be unfolded separately.

## `r1cs_arith`

After constraint definitions have reduced to field expressions, tries
`linear_combination`, restricted `simp_all`, normalization with `ring_nf`,
`field_simp`, and `aesop`. It is a closing tactic, not a semantic simulation.

For actual uses, inspect `R1CSLike.compileWitness_op_iff` and `op_reflection`.
Multi-constraint division/inverse cases require explicit decomposition and zero/nonzero
reasoning before arithmetic automation can finish the goals. In particular, do not
assume a denominator is nonzero without a source validity premise or target equation.

## Structural proofs

Keep frame, renaming, freshness, and state-relation lemmas explicit. Explain the
induction invariant before a long simulation proof. Automation should discharge local
equalities, not hide which source/target semantics or lowering equation is being used.

When extending a terminal operation, update syntax, direct constraint encoding,
materialization, checker, satisfaction, constructed-witness equivalence, and arbitrary-target
reflection. See [AUDIT.md](AUDIT.md) for the proof dependency map.
