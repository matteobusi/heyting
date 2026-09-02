# Warnings, Assumptions, Known Limitations

## 1. Parser and typed lowering unverified

Tokenizer, parser, AST analysis, and `ASTToDialect` are executable but lack
kernel-checked correctness theorem. Strong compiler theorem begins at successful
typed dialect module. Unsupported parsed operations are rejected at typed
boundary; parser warnings are not proof.

## 2. Partial LLZK coverage

Supported: Felt arithmetic, equality, objects, topologically decreasing calls,
Oracle reads, public members. Unsupported: arrays, booleans, casts, globals,
templates, control flow, includes, most non-native ops. Free functions rejected.

## 3. Callable restriction

Each struct has one `compute` and one `constrain`; call selector must be `0` and
target matching function kind in earlier topological struct. Same-struct helpers
and arbitrary named functions unsupported.

## 4. Division validity

Field division is mathematically total at zero, but R1CS encoding requires
nonzero divisor and inverse witness. Source witness execution rejects zero
divisors. Correctness uses successful materialization/forwarding boundary.

## 5. Witness generation theorem is pointwise

Compiler proves generated candidate satisfies source iff transported candidate
satisfies exact R1CS. It does not claim every input/Oracle candidate satisfies
source constraints. CLI checks and rejects false candidates.

## 6. Oracle is positional

`llzk.nondet` consumes values sequentially. Missing values cause
`oracleUnderflow`; unused suffix has no source meaning. Oracle file is trusted
input, not inferred witness completion.

## 7. CLI primality axioms

Supported field primality facts are `private axiom` declarations in
`Heyting/CLI.lean`, isolated from proof-bearing passes. Pass theorems remain
generic over `F : Type [Field F]` and audit to standard axioms only.

## 8. Parser skips before typed rejection

AST has `.skipped` nodes so parser can report unsupported generic operations.
Typed lowering rejects each `.skipped` body operation. Parser acceptance without
matching typed lowering must remain error.

## 9. macOS Lake cache issue

Some macOS 15/Lake combinations reject Reservoir platform string during
`lake cache get`. Full source build remains correct but slow.

## 10. External artifact trust

Lean proves internal R1CS semantics. JSON/binary serializers and snarkjs parsing
are tested executable boundaries, not currently proved faithful byte encodings.

## Archived issues

Retired StructIR-specific assumptions and proofs live on branch
`legacy-infrastructure`. They do not apply to active compiler. Migration history
remains in `docs/dialect-migration-plan.md`.
