# Warnings, Assumptions, Known Limitations

## 1. Parser and typed lowering unverified

Tokenizer, parser, AST analysis, and `ASTToDialect` are executable but lack
kernel-checked correctness theorem. Strong compiler theorem begins at successful
typed dialect module. The parser and frontend reject every construct outside the
supported subset and type-check member access, but this strictness is tested, not proved.

## 2. Partial LLZK coverage

Supported: Felt arithmetic, equality, objects, topologically decreasing calls,
Oracle reads, public members. Unsupported: arrays, booleans, casts, globals,
templates, control flow, includes, custom fields, split-input files, most non-native ops.
Free functions rejected. Upstream programs that use `struct.writem`/`struct.new` on another
struct, or read private members of another struct, are rejected as in upstream LLZK.

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
`oracleUnderflow`; unread values are an error. Oracle file is trusted
input, not inferred witness completion.

## 7. CLI primality axioms

Supported field primality facts are `private axiom` declarations in
`Heyting/CLI.lean`, isolated from proof-bearing passes. Pass theorems remain
generic over `F : Type [Field F]` and audit to standard axioms only.

## 8. Object model shared by compute and constrain

Objects form a tree in both functions (`StructObject` module documentation). `struct.new`
creates a fresh root, and `struct.writem` of a struct-typed member is lowered to
`writeObject`, which copies the sub-component below the member path that `@constrain` reads.
Witness generation reads the observation below the object the entry `@compute` returns, so a
struct with members must return its own struct type. The copy semantics of `writeObject`
and the generator itself are tested (`tests/ObjectTree.lean`), not proved: generator
correctness remains an open obligation.

## 9. macOS Lake cache issue

Some macOS 15/Lake combinations reject Reservoir platform string during
`lake cache get`. Full source build remains correct but slow.

## 10. External artifact trust

Lean proves internal R1CS semantics. JSON/binary serializers and snarkjs parsing
are tested executable boundaries, not currently proved faithful byte encodings.

## 11. Whole-entry pass packaging remains incomplete

`typed_source_r1cs_iff` assumes successful forwarding of a particular source witness.
The separate `typed_source_of_r1cs` theorem now covers every satisfying target assignment,
reflecting it to finite source readback. Reserved parameter zeros are enforced by target
constraints. `typed_entry_correct` (`EntryCorrect`) gives both directions for compiled entries,
including totality of `forward` on canonically sized satisfying source observations.
Entries whose compute function has more parameters than the constrain function are now
rejected by `lowerEntryCertified`. `EntryCorrect` is not a `PresReflPass` instance (finite
list observations, partial compilation). Generator correctness for producing source
observations remains open.

Wire encoding is only intended for allocated constructor ranges. Global injectivity
over all natural-number-indexed `R1CS.VarId` values would be false. Public/private
wire ordering and finite serialization must be audited separately.

**Public/private classification.** The statement wires are public outputs (public felt
members of the entry) followed by public inputs (`{llzk.pub}` compute parameters). They are
proved to carry the source public part (`statement_readback`) and to occupy wires `1..k`
(`WireAssignment`). A public member that `@constrain` never reads, or a public member of
struct type, is rejected. The Circom bytes themselves are tested with snarkjs Groth16, not
proved.

## Archived issues

Retired StructIR-specific assumptions and proofs live on branch
`legacy-infrastructure`. They do not apply to active compiler. Migration history
remains in `docs/dialect-migration-plan.md`.
