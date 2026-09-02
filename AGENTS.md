# Heyting — Agent Guide

AI agent reference. Read before changes.

Respond like smart caveman. Cut filler. Keep technical substance. Fragments fine.

## Project

Lean 4 + Mathlib formally verified LLZK-to-R1CS compiler.

Proof code requirements:

- zero `sorry`
- standard axioms only: `propext`, `Classical.choice`, `Quot.sound`
- no added/lost constraints across certified boundaries

## Build

```bash
lake build
lake build hey
```

Lean 4.28.0. Requires elan.

## Repository layout

```text
Heyting/
  Core/
    Language.lean          -- satisfaction relation abstraction
    Pass.lean              -- Pass, PreservingPass, ReflectingPass, PresReflPass
    Dialect.lean           -- OpSig, Stmt, typed Module/FuncDef
    DialectPass.lean       -- leaf-dialect lowering
    StructuralPass.lean    -- partial structural erasure + composition
    WitnessCodec.lean      -- constructive witness transport
    WitnessSemantics.lean  -- modular compute evaluator interfaces
  Dialects/
    Call*.lean             -- syntax, erasure, semantic correspondence
    StructObject*.lean     -- object state, erasure, simulation
    Oracle*.lean           -- nondeterministic input and constraint projection
    Felt*.lean             -- field operations and semantics
    ConstrainEq.lean       -- source equality constraints
    R1CSLike*.lean         -- leaf constraint dialect and FlatIR adapter
    TypedSourceSemantics.lean
    WitnessExecution.lean
  Languages/
    FlatIR.lean            -- backend instruction list
    R1CS.lean              -- rank-1 constraint systems
  Parsers/
    AST.lean               -- untyped LLZK AST
    ASTAnalysis.lean       -- topology, symbol, SSA analysis
    Tokenizer.lean / Parser.lean / Main.lean
    InputJSON.lean
  Passes/
    ASTToDialect.lean      -- unverified typed frontend
    DialectPipeline.lean   -- active proof-carrying whole pipeline
    FlatIRWitnessCodec.lean
    FlatIRToR1CS.lean      -- verified backend pass
  Backends/                -- JSON, .r1cs, .wtns serializers
  CLI.lean / CLIArgs.lean
tests/                     -- Lean unit tests and LLZK fixtures
scripts/smoke_cli.sh       -- CLI + snarkjs integration gate
```

Retired StructIR pipeline exists only on branch `legacy-infrastructure`.
Do not restore imports or CLI selectors from that branch.

## Active pipeline

```text
LLZK text
  → untyped AST
  → Module [Call, StructObject, Oracle, Felt, ConstrainEq]
  → Oracle constraint projection
  → Call erasure
  → StructObject erasure
  → [Felt, ConstrainEq]
  → R1CSLike
  → FlatIR
  → R1CS
```

Witness path executes full typed source module once, projects canonical source
witness, then transports it through pass-owned codecs. It does not re-execute
compute bodies at each layer.

## Correctness structure

`PresReflPass S T` supplies `compile`, program-indexed `witnessRel`,
preservation, reflection. `PresReflPass.compose` lifts local results.

`StructuralPass` handles partial passes whose static semantic state changes.
Correctness applies when lowering returns exact target. Structural passes
compose explicitly and bridge to `PresReflPass` when total/witness-backed.

`TypedEntryCompilationArtifact` retains original typed module, entry, Oracle
projection, Call and StructObject certificates, leaf program, witness layout,
and exact R1CS target. Key results:

- `typed_source_artifact_iff`
- `typed_source_check_eq_artifact`
- `typed_source_r1cs_iff`
- `generated_typed_source_r1cs_iff`
- `typed_pipeline_readback`

Guarantee begins at successfully typed dialect module. Parser and AST-to-dialect
lowering remain executable but unverified.

## Invariants

1. New semantic pass needs matching preservation/reflection interface:
   `DialectPass`, `StructuralPass`, or `PresReflPass` as appropriate.
2. No custom axioms in proof files. CLI-only `private axiom` primality facts allowed.
3. Zero sorries.
4. Keep `lake build` green.
5. Preserve intrinsic capability and SSA proofs in `Dialect.FuncDef`.
6. Keep structural order explicit: Oracle projection, Call erasure, StructObject erasure.
7. Never encode object paths as field values. Use `VarIdEncoding` only for witness slots.
8. Unsatisfied constraints are Boolean false, not transport failure. Runtime faults stay `Except`.

## Lean work

Field parameters: `(F : Type) [Field F]`; add `[DecidableEq F]`, `[IntCast F]`,
or `[Repr F]` only where needed. Never hardcode field in proof-bearing code.

New leaf dialect:

- define `OpSig` metadata and semantics
- add typed frontend lowering
- add erasure/lowering with local correctness
- add handler to witness execution when compute-capable
- extend pipeline composition and artifact theorem

New structural dialect:

- define one static state type for stage
- implement explicit `StructuralPass` value
- prove conditional preservation/reflection
- define witness codec/readback if state contributes observables

New FlatIR instruction:

- extend `FlatIRToR1CS.compileInstr`
- prove preservation/reflection, usually with `r1cs_arith`
- extend witness construction/readback

Use specific Mathlib imports. Lean style width 100. Search mathlib before proving.

## Verification

```bash
lake env lean path/to/File.lean
lake build
lake build hey
/Users/mbusi/.codex/plugins/cache/lean4-skills/lean4/4.8.1/bin/lean4-skills-sorry-analyzer Heyting --report-only --format=summary
./tests/run_tests.sh
./scripts/smoke_cli.sh
```

Run `lean_verify <file> <theorem>` for changed major theorems. Expected axioms:
`propext`, `Classical.choice`, `Quot.sound` only.

## Documentation

- `docs/GUARANTEES.md`: exact proof boundary/status
- `docs/WARNING.md`: assumptions and limitations
- `docs/languages.md`: language and pass semantics
- `docs/ROADMAP.md`: future work
- `docs/cli.md`: user-facing CLI
- `docs/llzk-dialects.md`: supported LLZK syntax
- `docs/dialect-migration-plan.md`: completed migration history
- `README.md`: public summary

## graphify

Knowledge graph lives at `graphify-out/`.

- For codebase questions, first run `graphify query "<question>"` when graph exists.
- Use `graphify path "<A>" "<B>"` for relationships.
- Use `graphify explain "<concept>"` for focused context.
- Prefer `graphify-out/wiki/index.md` for broad navigation when present.
- Dirty generated graph files are expected.
- After code changes, run `graphify update .`.
