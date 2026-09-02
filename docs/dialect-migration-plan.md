# Dialect-Based Pass Migration Plan

**Branch:** `dialect-based-passes`

**Completion checkpoint:** `b608671 feat(compiler): complete dialect migration`

**Archive branch:** `legacy-infrastructure` at checkpoint `b608671`

**Plan status:** complete

**Current point:** Phase 15 complete — legacy infrastructure extracted

## Ground rules

- Historical phase descriptions below record incremental migration.
- Completed phases left `lake build`, Lean tests, CLI smoke, zero-sorry, and
  standard-axiom gates green.
- Active branch no longer carries retired StructIR implementation.
- Branch `legacy-infrastructure` preserves exact final compatibility checkpoint.

## Status legend

- `[done]` committed or ready baseline
- `[active]` currently executing
- `[next]` immediate next phase
- `[blocked]` requires design decision or prior phase
- `[later]` planned later

---

## Phase R — Working-tree recovery `[done]`

Completed 2026-08-03 before resuming Phase 6.

- Captured the pre-recovery deletions and untracked files in the named Git
  stash `phase-r-pre-recovery-2026-08-03`.
- Restored the committed Phase-5 source baseline (`70a6fc4`).
- Isolated the unconnected scratch `Heyting/Dialect.lean` experiment in
  `tmp/phase-r-recovery/`.
- Kept this migration plan and `docs/related-work.md` uncommitted, as intended.
- Validated `lake build`, `lake build hey`, `tests/run_tests.sh`, and
  `scripts/smoke_cli.sh` successfully.

Phase 6 followed the recovery phase and is now complete.

---

## Phase 0 — Unified dialect pass baseline `[done]`

**Commit:** `7494d50 refactor: unify dialect pass core`

### Scope

- Establish dialect-native core syntax and body semantics.
- Replace public pass variants with one unified `DialectPass`.
- Add concrete Felt dialect and module-safe fresh-temp Felt pass.

### Files

- `Heyting.lean`
- `Heyting/Core/Dialect.lean`
- `Heyting/Core/Semantics.lean`
- `Heyting/Core/Module.lean`
- `Heyting/Core/DialectPass.lean`
- `Heyting/Dialects/Felt.lean`
- `Heyting/Dialects/FeltPass.lean`
- `Heyting/Dialects/ConstrainEq.lean`
- `Heyting/Dialects/Call.lean`

### Acceptance

- `lake build` green.
- No public `SimplePass`, `FreshPass`, `ModulePass`, `FreshModulePass` names under `Heyting`.
- `FeltPass.modulePass` uses unified `DialectPass`.

---

## Phase 1 — Module-level semantics skeleton `[done]`

### Goal

Lift body semantics to whole-module semantics without solving full call semantics yet.

### Commit name

`feat: add dialect module semantics skeleton`

### Design

Add new file:

- `Heyting/Core/ModuleSemantics.lean`

Define a minimal, call-free/module-local semantics layer around existing body evaluators:

- environment initialization for function parameters
- function compute evaluation
- function constrain evaluation
- struct-level satisfaction relation
- module-level satisfaction wrapper

Keep semantics conservative and explicit. Avoid pretending call semantics is solved.

### Proposed definitions

Names may adjust while proving.

```lean
namespace Dialect

structure FuncInput (F : Type) where
  args : List F

structure FuncOutput (F : Type) where
  env : LocalVar → F
  returnValue : Option F

def bindParams (args : List F) (default : F) : LocalVar → F

def evalFuncCompute
    (handlers : HandlerFamily Δ F)
    (fn : FuncDef Δ n i F .witness numMembers)
    (args : List F) (default : F) : Option (FuncOutput F)

def evalFuncConstrain
    (handlers : HandlerFamily Δ F)
    (fn : FuncDef Δ n i F .constraint numMembers)
    (env : LocalVar → F) : Prop

def satisfiesStruct
    (handlers : HandlerFamily Δ F)
    (s : StructDef Δ n i F)
    (args : List F) (default : F) : Prop

def satisfiesModuleAt
    (handlers : HandlerFamily Δ F)
    (m : Module Δ n F)
    (entry : Fin n)
    (args : List F) (default : F) : Prop

end Dialect
```

### Proofs/lemmas

- `bindParams_lt`: parameters below `args.length` read assigned values.
- `bindParams_ge`: variables above params use default.
- simple unfolding simp lemmas for `evalFuncCompute`, `evalFuncConstrain`, `satisfiesStruct`.
- theorem connecting `DialectPass.constrainBody`/`computeBody` to function-level semantics when `startFresh` conditions hold.

### Acceptance

- `lake build` green.
- `Heyting.lean` imports `Heyting.Core.ModuleSemantics`.
- No call-specific claims yet.
- File docs explain call semantics pending.

### Commit boundary

Commit only:

- `Heyting/Core/ModuleSemantics.lean`
- `Heyting.lean`
- possible tiny imports/simp lemmas in existing core files if strictly required
- updated plan file remains uncommitted unless asked

---

## Phase 2 — Module-pass semantic correctness `[done]`

Completed first correctness layer: constraint-function iff, compute status preservation, struct/module constraint wrappers.

### Goal

Prove unified `DialectPass` preserves module-level semantics for call-free/local semantics.

### Commit name

`feat: prove dialect module pass correctness`

### Design

Extend `Heyting/Core/DialectPass.lean` or add:

- `Heyting/Core/DialectPass/ModuleCorrect.lean` if file growth becomes too large

Prove function/module wrappers over existing body theorem:

```lean
theorem DialectPass.evalFuncConstrain_iff ...
theorem DialectPass.evalFuncCompute_agree ...
theorem DialectPass.satisfiesStruct_iff ...
theorem DialectPass.satisfiesModuleAt_iff ...
```

Compute functions are not modeled as preservation/reflection obligations. Keep compute semantics executable/relational, then prove a separate witness-generation correctness theorem later: generated witnesses satisfy the constraint semantics.

### Compute/witness design note

Do not require preservation/reflection for compute functions. The useful final theorem is not "lowered compute returns the same observable value". The useful final theorem is witness-generation correctness:

- execute compute semantics to produce a witness/environment;
- prove the produced witness/environment satisfies the constrain semantics;
- when passes lower constraints, compose constraint correctness with witness-generation correctness.

Therefore `evalFuncCompute_status` may remain as a sanity lemma, but future phases should not build architecture around compute preservation/reflection.

### Acceptance

- `lake build` green.
- module-level constrain theorem proved.
- compute-side theorem limited to operational sanity/status if useful; no preservation/reflection requirement for compute functions.
- witness generation correctness is deferred to a dedicated theorem relating compute semantics to produced witnesses.
- no new old pass variants.

### Commit boundary

Commit only module-correctness files and minimal core API changes needed for theorem.

---

## Phase 3 — Pass composition API `[done]`

Completed wrapper-style `ModuleConstraintPass`, `ofDialectPass`, and composition with explicit middle-handler equality witness.

### Goal

Compose dialect passes into verified dialect pipelines.

### Commit name

`feat: compose dialect passes`

### Design

Possible approaches:

#### Option A — compose raw `DialectPass`

Define:

```lean
def DialectPass.compose
    (p₁ : DialectPass Δ₀ Δ₁ F)
    (p₂ : DialectPass Δ₁ Δ₂ F) : DialectPass Δ₀ Δ₂ F
```

Hard because fresh-state threading and module-level `startFresh` policies compose poorly.

#### Option B — introduce checked pipeline wrapper

Define semantic wrapper that stores lowered module function and correctness theorem:

```lean
structure ModulePassCorrect (Δ Δ' : DialectSet) (F : Type) [Field F] where
  lowerModule : {n : Nat} → Module Δ n F → Module Δ' n F
  satisfies_iff : ...
```

Then:

```lean
def ModulePassCorrect.ofDialectPass ...
def ModulePassCorrect.compose ...
```

Recommended: Option B first. Keep raw `DialectPass` as construction/proof helper; compose correctness wrappers.

### Acceptance

- Can express pipeline of two passes.
- Composition theorem builds.
- Existing Felt pass can be lifted into wrapper.

### Commit boundary

Commit composition wrapper and any proof adapters only.

---

## Phase 4 — Call semantics decision + interface `[done]`

Decision made: generalize `DialectSem` with module context. Phase 4a complete: `SemCtx` is threaded through dialect semantics/evaluators. Phase 4b complete: call argument binding, selector policy, and target lookup helpers compile. Phase 4c next: assess/implement `Call.sem` if laws are tractable.

### Goal

Make `Call` dialect semantically meaningful in module evaluator.

### Commit name

`feat: define call-aware module semantics`

### Decision needed

Two options:

#### Option A — Special-case `Call` in module evaluator

Pros:
- fastest
- avoids changing all `DialectSem`
- good for initial `EraseCalls`

Cons:
- `Call` not fully ordinary dialect semantically
- generic evaluator needs knowledge of dialect membership/index

#### Option B — Extend `DialectSem` with module context

Pros:
- call remains ordinary dialect op
- future dialects can inspect module if needed

Cons:
- touches `Semantics`, all dialect sems, all pass proofs
- bigger proof churn

Recommended initial path: Option A only if matching concrete canonical source set (`[Call, Felt, ConstrainEq]`). Option B if we want fully generic call support immediately.

### Acceptance

- clear committed design in code comments
- call evaluation for at least compute or constrain path sketched/proved enough to support `EraseCalls`
- build green

### Phase 4 result

Completed module-context generalization and call helper layer. Full `Call.sem` is intentionally deferred: current `DialectSem` laws (`reads_congr`, `frame`) require callee-body congruence/frame theorems that belong with `EraseCalls`/call correctness. Phase 5 should implement syntactic erasure first, then Phase 6 can prove call/callee semantic laws using freshening/substitution infrastructure.

---

## Phase 5 — EraseCalls pass skeleton `[done]`

Completed syntax-only `CallPass.lean` with `SourceSet`/`TargetSet`, index helpers, `eraseBody`/`eraseFunc`/`eraseStruct`/`eraseModule`. Call branch is a documented TODO placeholder; no correctness theorems, no `sorry`.

### Goal

First real erasure pass:

```text
[Call, Felt, ConstrainEq] → [Felt, ConstrainEq]
```

### Commit name

`feat: add erase calls pass skeleton`

### Scope

Add:

- `Heyting/Passes/EraseCalls.lean` or `Heyting/Dialects/CallPass.lean`

Implement syntax lowering first:

- find/inline callee body
- bind args to callee params
- freshen callee locals into caller fresh space
- bind return to destination

### Acceptance

- syntax lowering defined
- caps preservation proof if tractable
- SSA proof may be stubbed only as theorem statement with no `sorry`? No: avoid theorem until proof exists.
- build green

### Commit boundary

Commit skeleton without false correctness claims.

---

## Phase 6 — EraseCalls correctness `[done]`

Unblocked by Phase 5 syntax skeleton.

### Current implementation status

- Added `Heyting/Dialects/CallSemantics.lean`: executable, call-aware module
  semantics for the concrete `[Call, Felt, ConstrainEq]` source set.
- Evaluation is well founded on `(enclosing struct index, remaining body)`:
  calls can only target earlier structs, while ordinary body execution consumes
  one statement.
- Added shared call-target lookup and return-environment binding primitives in
  `Heyting/Dialects/Call.lean`.
- Replaced `eraseBody`'s placeholder with hygienic, recursively terminating
  inlining. Parameters map to caller arguments, callee locals receive fresh
  ranges, and returns use explicit target definitions.
- Added direct/nested execution guards plus rejection guards for unsupported
  selectors and argument-arity mismatches.
- Connected executable target evaluation to generic `HandlerFamily` semantics.
- Proved recursive erasure monotonically advances its fresh counter, bounded
  callee variables stay inside their reserved block, and return-copy execution
  implements source return binding under the resulting freshness invariant.
- Added target compute-fragment composition over appended lowered bodies.
- Introduced the bounded source/target environment-agreement invariant, proved
  parameter substitution establishes it, and proved renamed Felt and
  ConstrainEq operations preserve their local semantics.
- Proved target compute/constraint fragments compose over append, including
  final constraint-environment threading.
- Proved SSA bodies never overwrite parameters; combined with reserved ranges,
  `inlineVar` separates every operation destination even when call arguments
  alias. This discharges the local Felt-step simulation side condition.
- Added explicit SSA-defined-set tracking. Compute calls now reject an observed
  callee return unless it is a parameter or body-defined local, preventing an
  undefined source return from reading arbitrary fresh target storage.
- Proved parameter binding initializes defined-set environment agreement, Felt
  steps extend it, and successful return checking exposes an agreed return.
- Added `RenameInvariant`, packaging local-below-fresh and SSA destination
  separation. Proved it for root identity renaming, nested `inlineVar`, larger
  fresh counters, and call-argument lookup.
- Proved renamed return binding and executable return-copy code extend caller
  agreement to the destination while preserving previously defined locals.
- Added capability extraction and ruled out `ConstrainEq` operations from
  well-formed witness/compute bodies, removing an impossible induction branch.
- Added concrete source evaluator equations for calls, Felt operations, and
  equality constraints, exposing the cases hidden by well-founded recursion.
- Proved that successful recursive compute erasure certifies total source
  compute execution, including nested callees, and lifted the result to
  `eraseComputeFunc`.
- Added caller-frame invariants for inlined renaming: SSA destinations map into
  the callee's reserved range, recursive erasure preserves that destination
  floor, and erased target execution cannot overwrite locals below it.
- Lifted target frame preservation to `EnvAgreesOn`, proving execution of an
  erased nested callee preserves all protected caller-local values. This closes
  the caller-state side condition needed by recursive value simulation.
- Extended focused coverage with parameter-return copying and exact constraint
  call lowering, including callee-local arithmetic feeding equality checks.
- Proved generalized recursive compute simulation and constrain truth/final-state
  equivalence, then lifted both results to top-level function erasure.
- Added executable certification of target capability and SSA checks, so every
  successfully erased function and module carries a genuine well-formed
  `FuncDef`; no proof obligations are bypassed.
- Added a certified partial module erasure and proved entry-point constraint
  preservation/reflection against the generic target handlers.
- Added `CallModuleConstraintPass.compose`, allowing the call-aware partial
  boundary to compose with ordinary total `ModuleConstraintPass` values.
- Kept the wrapper partial because source `Module` does not intrinsically encode
  selector, call-arity, or call-kind validity. A total `ModuleConstraintPass`
  would therefore make a false claim for malformed source modules.

### Goal

Prove call erasure preserves call-aware module semantics.

### Commit name

`feat: prove erase calls correctness`

### Scope

- frame/freshness lemmas
- substitution/freshening lemmas
- compute/constrain preservation
- module-level correctness wrapper instance

### Acceptance

- build green
- correctness theorem usable by composition wrapper
- no `sorry`

---

## Phase 7 — Felt/ConstrainEq to constraint dialect path `[done]`

### Goal

Move from core arithmetic dialects toward executable constraint backend.

Target:

```text
[Felt, ConstrainEq] → [R1CS-like dialect] → backend artifact
```

### Completed implementation

- Added `R1CSLike`, a single SSA instruction dialect containing arithmetic
  assignments and equality assertions with direct `FlatIR.Instr` encodings.
- Added call-free target semantics and a total, one-operation-to-one-instruction
  `DialectPass` from `[Felt, ConstrainEq]` to `[R1CSLike]`.
- Proved per-operation compute/constrain simulation and exact preservation of
  capabilities and SSA structure; lifted these through `ModuleConstraintPass`.
- Composed the Phase-6 partial call-aware wrapper with the new total pass via
  `callToR1CSLike`.
- Added module-entry backend compilation through the existing verified
  `FlatIRToR1CS` pass, including preservation/reflection theorems at the flat
  witness boundary.
- Added focused checks for module lowering, FlatIR adaptation, constraint count,
  and module-level constraint equivalence.

The backend boundary deliberately does not claim that sequential dialect
evaluation unconditionally implies FlatIR satisfaction. In particular, Felt
division is total at zero, while legacy FlatIR/R1CS `assignDiv` requires a
nonzero divisor. Resolving that mismatch requires either a total-division R1CS
gadget or an explicit source validity condition; neither is hidden in Phase 7.

### Commit candidates

1. `feat: add r1cs dialect syntax`
2. `feat: lower constrain eq to r1cs dialect`
3. `feat: lower felt ops to r1cs dialect`
4. `feat: add dialect r1cs backend adapter`

### Acceptance

- each commit builds
- old backend reused where possible
- no frontend switch yet

---

## Phase 8 — Frontend dialect AST output `[done]`

### Goal

Retarget frontend from old `StructIR` path to generic dialect module output.

Target:

```text
parser → AST → Module [Call, Felt, ConstrainEq]
```

### Completed implementation

- Added typed AST lowering to `Module [Call, Felt, ConstrainEq]`, including
  topological struct indexing and executable capability/SSA certification.
- Lowered Felt arithmetic, equality constraints, returns, and typed
  compute/constrain calls; unsupported struct-object, nondeterminism, free
  function, and skipped-operation cases now fail explicitly.
- Added the executable constraint path from AST through call erasure,
  `[Felt, ConstrainEq]`, `R1CSLike`, and the existing R1CS backend adapter.
- Added opt-in `hey compile --dialect`; the default legacy CLI is unchanged.
  `--auto` and `--input` are rejected with this flag until dialect compute and
  witness generation are integrated.
- Added focused frontend, call-erasure, malformed-call, unsupported-operation,
  CLI-argument, and legacy/dialect differential tests. The differential tests
  record legacy-only parameter/object plumbing constraints separately from
  source-operation constraints.
- Added a parser/CLI fixture for the currently representable source subset.

### Commit candidates

1. `feat: add ast to dialect module lowering`
2. `feat: add dialect pipeline cli flag`
3. `feat: compare dialect and legacy outputs`

### Acceptance

- legacy CLI path remains green while dialect path matures
- golden/differential tests added when executable path exists

---

## Phase 9 — Legacy pipeline quarantine `[done]`

### Goal

After dialect pipeline can compile target examples, move old `StructIR → FlatIR → R1CS` from primary path to reference/legacy.

### Completed implementation

- Moved the verified StructIR composition out of the ambiguous root
  `Pipeline` namespace and into `Legacy.Pipeline`.
- Added `Heyting.Legacy.Pipeline` as the canonical compatibility import while
  retaining the implementation file to avoid unnecessary proof churn.
- Updated the CLI, parser documentation, differential tests, and umbrella
  imports to use the quarantined namespace.
- Added explicit `--legacy` selection. It remains the compatibility default;
  `--legacy` and `--dialect` are mutually exclusive.
- Added namespace, correctness-instance, CLI selection, and smoke coverage.
- Reframed architecture documentation around the dialect-native target while
  documenting the precise coverage and witness limitations that prevent a
  default switch today.

### Commit candidates

1. `refactor: separate legacy pipeline namespace`
2. `docs: document dialect pipeline architecture`
3. `chore: retire obsolete structir assumptions`

---

## Structural-erasure continuation

The original migration sequence is complete. The next sequence makes
structural dialect erasure compositional without introducing a dynamic effect
registry or a universal heterogeneous state container.

### StructObject frontend slice `[done]`

- Added `StructObject` operations for allocation and typed member reads/writes.
- Added standalone executable semantics threading field locals, object paths,
  witness storage, and a fresh-path counter.
- Generalized the AST traversal through dialect-set builders, making
  `[Call, StructObject, Felt, ConstrainEq]` the primary typed frontend output
  without duplicating name resolution, topology, capability, or SSA checks.
- Retained `lowerCallCompatible` as the temporary executable projection to
  `[Call, Felt, ConstrainEq]`; it rejects object operations with a precise
  erasure-boundary error.
- Added frontend and state-semantic tests covering allocation, reads, writes,
  typed member indices, and backend-projection rejection.

---

## Phase 10 — Static structural-pass foundation `[done]`

### Goal

Define the common shape of a pass that removes one structural dialect while
allowing source and target stages to use different, statically known semantic
state types.

Conceptual interface:

```text
EraseDialect removed residual F
  source: ModuleStage (removed :: residual) F
  target: ModuleStage residual F
  lower:  Module source → Except Error (Module target)
  relation: source.State → target.State → Prop
  preservation / reflection
```

`EraseDialect` is an explicit pass value/certificate, not a typeclass that
automatically chooses or invokes a pass. The implementation should reuse
`Language` and `PresReflPass` where practical rather than duplicate their
composition logic.

### Design constraints

- One statically selected semantic state type per compiler stage.
- No `List Effect`, dynamic casts, heterogeneous runtime maps, or global
  extensible “god state.”
- Explicit pipeline ordering and composition.
- Canonical structural-dialect prefix order initially:

  ```text
  [Call, StructObject, leaf dialects...]
  ```

- Each structural pass removes the head dialect. Arbitrary list-element
  deletion/permutation is deferred until demonstrated necessary.
- Supporting laws may use typeclasses when they have unique canonical
  instances, but pass selection must remain explicit.

### Scope

- Define or adapt the static module-stage semantic packaging.
- Define the structural-erasure pass/certificate wrapper.
- Connect its composition to `PresReflPass.compose`.
- Isolate small reusable laws such as residual-operation rename stability,
  destination framing, and fresh-variable monotonicity.
- Add a minimal synthetic composition test using two explicitly chosen passes.

### Completed implementation

- Added `ModuleStage Δ n F`, which selects one concrete semantic `State` type
  and satisfaction relation for a dialect-module stage.
- Added partial `StructuralPass source target` values with explicit lowering,
  a relation indexed by both source and target modules, and conditional
  preservation/reflection for successful lowering.
- Added `EraseDialect removed residual` as the head-erasure specialization;
  it is an abbreviation for an explicit certificate, not a typeclass.
- Added identity and explicit composition. Composition retains the typed
  intermediate module and state and short-circuits through `Except`.
- Added witness-backed `ModuleStage`/`Language` constructors, lifting from
  `PresReflPass`, constructive totality evidence, and conversion of total
  structural passes back to `PresReflPass`.
- Proved that lifting an existing `PresReflPass.compose` agrees with structural
  composition on both lowering and witness/state relations.
- Added `LocalStateView`, `StateAgreesUnder`, and
  `PreservesLocalsOutside` as small reusable relations over the field-local
  projection of richer states, including composition/frame lemmas.
- Reused the existing dialect pass freshness machinery rather than introducing
  a second fresh-variable abstraction.
- Added synthetic coverage with three distinct static state types, explicit
  two-pass composition, rejection propagation, both framework adapters, and
  rename/frame relations.

### Acceptance

- No runtime effect registry or dependent heterogeneous state collection.
- Source and target semantic carrier types may differ safely.
- Two structural pass values compose without pipeline-specific glue.
- Existing leaf `DialectPass` APIs and legacy reference pipeline remain green.
- No `sorry`.

---

## Phase 11 — Residual-polymorphic Call erasure `[done]`

### Goal

Generalize Call erasure from the hard-coded
`[Call, Felt, ConstrainEq] → [Felt, ConstrainEq]` transformation to:

```text
[Call] ++ residual → residual
```

The pass must inline and rename residual operations without knowing their
constructors.

### Required interfaces

- `RenameStable`: residual semantics commute with local-variable renaming.
- Residual frame laws: an operation changes only its declared effects/dest.
- `CallProtocol State`: statically typed argument binding, callee-state
  initialization, return binding, and caller/callee state merging.
- Existing SSA, capability, fresh-variable, selector, and arity validity.

`CallProtocol` is indexed by one concrete stage state. It is not a state
builder. For the object-aware stage, its instance transports object paths and
witness/allocation state through calls.

### Migration

- Refactor existing Call syntax erasure to preserve arbitrary residual ops via
  `OpSig.mapVars` and dialect-index reindexing.
- Parameterize correctness proofs over residual semantics and the required
  laws.
- Instantiate first for `[Felt, ConstrainEq]`, reproducing all current results.
- Instantiate for `[StructObject, Felt, ConstrainEq]` with object-aware state.
- Remove the hard-coded `CallPass.SourceSet` restriction from the primary
  frontend pipeline.

### Acceptance

- Existing call tests remain unchanged or become strictly more general.
- Nested calls containing StructObject instructions erase to a call-free typed
  module while preserving those instructions.
- The executable pipeline reaches
  `[StructObject, Felt, ConstrainEq]` for object-bearing programs.
- Preservation/reflection composes through the explicit structural-pass API.
- No `sorry`.

### Completed implementation

- Added the module-aware generic eraser
  `[Call] ++ residual → residual`. Its recursive core recognizes only the
  Call head; residual dialect indices are shifted structurally and local
  renaming uses each `OpSig.mapVars` implementation.
- Added explicit `ResidualSyntax` pass values for operation-context transport
  and return-copy emission. This is necessary because inlining changes the
  enclosing `OpCtx`; it is not a runtime registry or an inferred pass.
- Added `ResidualSyntax.RenameStable` certificates showing that context
  transport preserves destination, reads, and capability metadata.
- Instantiated the syntax and certificates for `[Felt, ConstrainEq]` and
  `[StructObject, Felt, ConstrainEq]`.
- Added the static `CallProtocol State F`, plus field-local and object-aware
  values. The object protocol transports argument object paths and threads the
  witness store and allocation counter through calls while framing unrelated
  caller locals.
- Added generic function, struct, and module certification after inlining.
- Changed the primary executable frontend to lower the full object-aware AST,
  erase calls, and only then reject remaining StructObject operations at the
  explicit Phase-12 boundary.
- Added nested `Root → Middle → Leaf` coverage in which a StructObject
  operation survives both levels of call inlining.
- Exposed the existing leaf preservation/reflection theorem as an explicit
  `EraseDialect`/`StructuralPass` value, so it composes through the Phase-10
  API without pipeline-specific glue.
- Defined the structural Call dialect's residual-polymorphic elaboration
  semantics: a Call-bearing module denotes its successfully expanded residual
  module under the residual stage's own satisfaction relation. Proved generic
  preservation/reflection for every residual `ModuleStage` and concrete state
  type, conditional only on successful partial lowering.
- Retained the independent direct field-local Call evaluator and its existing
  simulation theorem as the coherence check for the leaf specialization.
- Added concrete `[StructObject, Felt, ConstrainEq]` constraint semantics over
  field locals, object paths, witness storage, and allocation state, then
  instantiated the generic certificate as an object-aware `EraseDialect`.
- Added a composition test showing this object-aware pass pipelines through
  the explicit `StructuralPass.compose` API.

---

## Phase 12 — StructObject erasure `[done]`

### Goal

Erase object operations after calls have been removed:

```text
[StructObject, Felt, ConstrainEq]
  → [Felt, ConstrainEq]
```

Because the input is call-free, this pass owns object-path and witness-store
lowering without recursive module evaluation.

### Design

- Source state: field locals, object paths, witness storage, allocation state.
- Target state: field locals plus the concrete encoded witness variables needed
  by the constraint backend.
- Define a typed state relation connecting `(instance path, member)` storage to
  target locals/wires.
- Lower member reads/writes and allocation using explicit path/slot encoding.
- Preserve public-member accounting and avoid collisions with SSA locals via a
  proved fresh/witness-variable boundary.
- Compose with generalized Call erasure and existing leaf passes.

### Acceptance

- `struct_ops.llzk`, `pub_members.llzk`, and object-bearing call fixtures compile
  with `--dialect`.
- Object-state executable behavior agrees with the legacy reference fixtures.
- Preservation/reflection is stated over the typed source/target state relation.
- No no-op or field-value encoding of object identities.
- No `sorry`.

### Completed implementation

- Added the call-free `[StructObject, Felt, ConstrainEq] →
  [Felt, ConstrainEq]` module pass.
- Execute object allocation and member-path propagation statically. Object
  identities remain `List Nat` paths and are never represented by field
  elements.
- Encode `(instance path, member)` positions injectively with the existing
  `VarIdEncoding` bijection. Member-read destinations become aliases of
  dedicated initial witness locals.
- Reserve the witness-local interval immediately after the original function
  parameters and shift every non-parameter SSA local above it. Target
  capability and SSA checks are rerun before constructing each typed
  `FuncDef`.
- Added an explicit typed `StateRel`: original parameter values agree and each
  encoded target witness local equals the corresponding source witness slot.
  Constructive encode/decode functions establish the relation in both
  directions.
- Packaged the partial transformation as `EraseDialect StructObject.sig ...`
  with preservation/reflection, and composed it explicitly after the Phase-11
  Call pass.
- Replaced the executable object-rejection boundary. `--dialect` now compiles
  `struct_ops.llzk`, `pub_members.llzk`, and object-bearing nested calls.
- Public-member counts continue to be forwarded to the R1CS backend, while
  witness positions remain explicit target locals.
- Added focused path/alias/witness-range and structural-composition tests plus
  CLI smoke coverage for object and public-member fixtures.

---

## Phase 13 — Compositional dialect witnesses and proof-carrying compilation `[complete]`

### Goal

Retain source-level witness generation while making both source execution and
witness transport modular. Compile each program into a proof-carrying artifact
whose target program and witness codec are constructed together. Prove
pointwise source/R1CS satisfaction equivalence for every successfully
transported witness, then derive the generated-witness corollary.

### Scope

- Define a canonical source witness independently of transient compute state.
- Factor source computation into per-dialect handlers assembled by the full
  source dialect set. Calls remain a structural evaluator over those handlers.
- Add a constructive, pointwise witness-codec layer above the existing
  existential `PresReflPass`/`StructuralPass` interfaces.
- Make every pass in the executable dialect pipeline return its target program
  together with the exact witness-layout metadata and codec used for that
  target.
- Compose Oracle, Call, StructObject, leaf, and backend codecs into one
  compilation artifact.
- Prove source/target satisfaction equivalence and observable readback for the
  composed artifact.
- Replace the current monolithic/manual witness bridge in the CLI only after
  the composed theorem and parity suite are green.
- Keep `--legacy` as the proved reference escape hatch throughout.

### Acceptance

- The full pipeline exposes a `CompilationArtifact` containing the compiled
  R1CS, forward transport, readback, and their laws.
- For any successful forward transport, source satisfaction is equivalent to
  R1CS satisfaction for that exact witness pair.
- Readback after forward transport is identity on source-observable witness
  coordinates.
- The generated-witness theorem is a corollary of the general transport
  theorem, not a separate monolithic proof.
- Source execution dispatches through per-dialect handlers; no evaluator file
  performs a closed case split over every source dialect.
- No manual reproduction of StructObject slot encoding or backend auxiliary
  layout remains in `DialectPipeline`.
- Full fixture, oracle, division, JSON/binary, and `snarkjs` suites remain green
  through both the default dialect path and `--legacy`.
- Unsupported constructs and partiality fail at named typed boundaries.
- Documentation distinguishes existential correctness, pointwise transport
  correctness, generator correctness, and executable validation.
- No `sorry` in the new interfaces, transports, or theorems.

### Operational baseline already delivered

- Added typed `Oracle.next` syntax and `Oracle.Stream` state. The full frontend
  module is `[Call, StructObject, Oracle, Felt, ConstrainEq]`.
- Added an explicit executable Oracle constraint projection and a typed compute
  evaluator that threads locals, object paths, witness storage, allocation, and
  the oracle cursor through nested calls.
- Added dialect R1CS witness materialization, including encoded StructObject
  slots, shifted locals, inverse auxiliaries, and equality validation.
- Added `--oracle`; `--auto` and `--input` now work on the dialect path.
- Named the R1CS division precondition as `Felt.backendValid`; dialect witness
  execution rejects division by zero before artifact emission.
- Switched unflagged CLI compilation to dialect mode. `--legacy` remains the
  explicit proved reference escape hatch.
- Every LLZK fixture compiles through both paths. Every witness-capable fixture
  is checked with `snarkjs` on both paths; smoke tests additionally cover a
  nonzero oracle witness and division-by-zero rejection.
- Oracle erasure and executable witness generation are not yet accompanied by
  new preservation/reflection theorems; documentation does not claim them.

The baseline is intentionally not the final Phase-13 architecture. Its current
bridge is:

```text
full source module
  → monolithic WitnessExecution
  → source object witness
  → manual object-slot seeding in DialectPipeline
  → direct FlatIR instruction execution
  → R1CS witness
```

Problems to remove:

1. `WitnessExecution` knows Oracle, Call, StructObject, Felt, and ConstrainEq
   simultaneously, so dialect extension is not local.
2. It returns an object witness without establishing source satisfaction.
3. Source constraints are checked only after lowering, so the source generator
   and source language semantics are not cleanly connected.
4. `DialectPipeline` duplicates StructObject encoding and backend witness
   materialization instead of consuming pass-owned codecs.
5. `OracleErasure` is only a constraint projection: replacing `Oracle.next`
   with zero does not preserve whole compute semantics.
6. Existing `PresReflPass` theorems are existential and do not imply a
   pointwise iff for a particular generated/transported witness pair.

### Final architecture

```text
program + public inputs + oracle
  → modular source evaluator
  → canonical source witness ws

program
  → compileArtifact
  → { target R1CS, composed witness codec, correctness laws }

artifact.forward ws
  → target witness wt
```

Generation occurs once at the source level. Compiler stages do not carry the
oracle cursor, call frames, object allocation counter, or other transient
interpreter state. They transport only the canonical semantic witness and the
metadata required to represent it at the next stage.

### Theorem targets

The plan adds a stronger constructive layer without replacing the established
existential framework.

```lean
structure WitnessCodec (S : ModuleStage Δs n F) (T : ModuleStage Δt n F)
    (source : Module Δs n F) (target : Module Δt n F)
    (rel : S.State → T.State → Prop) where
  forward : S.State → Except TransportError T.State
  readback : T.State → S.State
  forward_rel : ∀ ws wt, forward ws = .ok wt → rel ws wt
  satisfies_iff : ∀ ws wt, forward ws = .ok wt →
    (S.satisfies ws source ↔ T.satisfies wt target)
  readback_forward : ∀ ws wt, forward ws = .ok wt →
    ObservableEq (readback wt) ws
```

Exact names and universe parameters may change during implementation, but the
semantic obligations may not be weakened. `ObservableEq` compares canonical
source witness positions; target-only fresh locals, inverse auxiliaries, and
is-zero auxiliaries are intentionally excluded.

Compilation packages program translation and witness layout together:

```lean
structure CompilationArtifact (S : Language Vs Fs) (T : Language Vt Ft)
    (program : S.Program) where
  target : T.Program
  forward : Witness Vs Fs → Except TransportError (Witness Vt Ft)
  readback : Witness Vt Ft → Witness Vs Fs
  satisfies_iff : ∀ ws wt, forward ws = .ok wt →
    (S.satisfies ws program ↔ T.satisfies wt target)
  readback_forward : ∀ ws wt, forward ws = .ok wt →
    ObservableEq (readback wt) ws
```

Whole-pipeline theorem:

```lean
theorem pipeline_witness_iff
    (hcompile : compileArtifact program = .ok artifact)
    (hforward : artifact.forward ws = .ok wt) :
    Source.satisfies ws program ↔ R1CS.satisfies wt artifact.target
```

Generated-witness corollary:

```lean
theorem generated_witness_iff
    (hgen : genWitness program inputs oracle = .ok ws)
    (hcompile : compileArtifact program = .ok artifact)
    (hforward : artifact.forward ws = .ok wt) :
    Source.satisfies ws program ↔ R1CS.satisfies wt artifact.target
```

If source generation is later changed to return a satisfying subtype, target
satisfaction follows immediately from this corollary. The general theorem must
continue to quantify over arbitrary source witnesses so that failed source
constraints correspond to failed target constraints rather than transport
failure.

### Correctness hierarchy

Three levels remain explicit:

1. `PresReflPass`: existential equisatisfiability. This remains the baseline
   compiler-correctness interface and is not broken by Phase 13.
2. `WitnessTransportingPass`: constructive forward transport plus pointwise
   satisfaction iff for every successful transport.
3. `RoundTripPass`: transport plus readback identity on source observables.

Adapters may derive `PresReflPass` from the stronger interface when compilation
and forward transport are total on satisfying inputs. The converse is not
assumed: existential preservation does not construct the particular witness
needed by the CLI.

### Source witness generation

The source generator has two layers:

```text
SourceExecState
  = locals × object paths × witness store × allocation counter × oracle stream

SourceWitness
  = canonical semantic witness visible to Source.satisfies
```

`genWitness` initializes `SourceExecState`, evaluates the main compute function,
and projects only `SourceWitness`. Transient state may be retained in a debug
result but is not passed to compiler stages.

Per-dialect execution interface:

```lean
structure WitnessDialectSem (sig : OpSig) (State : Type) where
  step : SemCtx Δ n F → sig.Op γ F → State → Except RuntimeFault State
  reads_congr : ...
  frame : ...
```

The concrete full source set chooses one static `SourceExecState`; there is no
heterogeneous runtime effect list and no dynamic state builder. Dialects receive
only the projections/protocols they require:

- Felt: read/write field locals and enforce division validity.
- Oracle: consume exactly one stream element and advance the cursor.
- StructObject: update object paths, allocation, and canonical witness slots.
- ConstrainEq: no compute mutation; source constraint semantics remains
  independently defined.
- Call: structural recursion over the module using a `CallProtocol` that binds
  arguments and threads witness/oracle state through topologically smaller
  callees.

Oracle underflow remains an explicit policy choice. The operational baseline
defaults missing entries to zero. The recommended Phase-13A decision is a typed
`oracleUnderflow` fault because it distinguishes a deliberately supplied zero
from missing private input; if accepted, CLI behavior and tests change together.

### Pass-owned witness codecs

Every pass owns the layout decisions it introduces.

#### Oracle constraint projection

- Program translation removes Oracle from the constraint-stage dialect set.
- Source witness forward transport is identity on canonical witness positions;
  already-consumed oracle values survive only where compute stored them.
- Correctness is stated over constraint observations, not whole compute-body
  equivalence. The zero replacement in erased compute bodies must not appear as
  the semantic justification.

#### Call erasure

- The artifact records inlining renamings/fresh ranges needed by downstream
  materialization.
- Canonical source witness positions remain unchanged unless a concrete call
  expansion introduces an observable mapping.
- Pointwise constrain satisfaction iff is proved from the existing hygienic
  expansion and frame lemmas.

#### StructObject erasure

- Reuse `VarIdEncoding`, `encodeTargetState`, and `StateRel`; do not duplicate
  their arithmetic in the pipeline.
- Forward maps `(instance path, member)` to the inserted encoded local range.
- Readback decodes that range to the canonical source witness.
- Prove `readback (forward ws)` agrees with `ws` on all source coordinates.

#### Felt/ConstrainEq to R1CSLike

- Materialize SSA locals from parameters and encoded witness locals.
- Arithmetic assignments compute destinations; equality assertions never
  mutate or reject transport. An unsatisfied equality must produce an
  unsatisfying target witness so the pointwise iff remains meaningful.
- Division transport is partial exactly when `Felt.backendValid` fails.

#### FlatIR/R1CS backend

- Reuse `FlatIRToR1CS.compileWitness` and `extractWitness`.
- Forward constructs canonical inverse/is-zero auxiliary witnesses.
- Readback discards target-only auxiliaries.
- Existing backend correctness is strengthened or wrapped with the pointwise
  theorem needed by the artifact.

#### Compaction and future optimizations

- Any pass used by the witness-generating pipeline must supply a constructive
  codec, including its exact renaming map.
- A pass with only existential `PresReflPass` correctness remains valid for
  compilation but cannot be inserted into the CLI witness pipeline until a
  codec exists.

### Detailed implementation sequence

#### Phase 13A — semantic contract and regression boundary

Files: `Core/Pass.lean`, `Core/StructuralPass.lean`, new
`Core/WitnessCodec.lean`, tests documenting current bridge behavior.

1. Freeze the canonical source witness type and `Source.satisfies` entry
   semantics, including public-input coordinates.
2. Decide Oracle underflow semantics and Felt division validity.
3. Define `ObservableEq`, `TransportError`, `WitnessCodec`,
   `WitnessTransportingPass`, and `RoundTripPass`.
4. Prove identity and composition for codecs, including composition of
   `satisfies_iff` and `readback_forward`.
5. Add adapters to existing `StructuralPass`/`PresReflPass` without changing
   their public theorem statements.

Gate: a two-pass toy pipeline composes forward/readback and proves pointwise
satisfaction iff with no `sorry`.

#### Phase 13B — modular source evaluator

Files: new `Core/WitnessSemantics.lean`, `Dialects/Oracle.lean`,
`Dialects/StructObject.lean`, `Dialects/Felt.lean`, Call semantics support.

1. Define the handler interface over one statically selected source state.
2. Implement and test Felt, Oracle, and StructObject handlers independently.
3. Implement call-aware module evaluation over the handler family.
4. Define `genWitness` as compute execution followed by projection to the
   canonical source witness.
5. State and prove handler-local frame/read laws needed by generator soundness.
6. Remove the closed five-dialect dispatch from `WitnessExecution`; retain a
   compatibility wrapper only until CLI cutover.

Gate: all compute fixtures produce the same canonical source witnesses as the
operational baseline, including nested calls and multiple oracle reads.

#### Phase 13C — source generator correctness

Files: source module semantics and focused theorem tests.

1. Connect the modular compute evaluator to independently defined source
   constraint semantics.
2. Prove the generated candidate corresponds to the final compute state.
3. Provide a decidable source witness checker.
4. Prove checker correctness: `checkSource ws p = true ↔ Source.satisfies ws p`.
5. Keep candidate generation distinct from checking so unsatisfying candidates
   remain representable for the general transport theorem.

Gate: source satisfaction is testable and proved independently of compilation.

#### Phase 13D — structural pass codecs

Files: `OracleErasure.lean`, `CallErasure.lean`, `StructObjectPass.lean`.

1. Replace the semantic justification of Oracle zero-substitution with a
   constraint-observation projection theorem and identity source-witness codec.
2. Attach constructive witness metadata/transport to Call erasure.
3. Promote StructObject's existing encode/decode functions and `StateRel` into
   a `RoundTripPass` codec.
4. Compose Oracle → Call → StructObject artifacts explicitly.

Gate: the structural prefix proves pointwise satisfaction iff and observable
round-trip for every successfully lowered module.

#### Phase 13E — leaf and backend codecs

Files: `R1CSLikePass.lean`, `FlatIRCompact.lean`, `FlatIRToR1CS.lean`, or thin
artifact adapters beside those passes.

1. Move SSA materialization from `DialectPipeline` into the leaf-pass codec.
2. Make equality assertions observational rather than transport failures.
3. Align division partiality exactly with `Felt.backendValid`.
4. Package backend auxiliary construction and readback.
5. Prove pointwise iff and observable round-trip for each layer.

Gate: a source witness can be transported through the entire lower half without
calling the current manual FlatIR witness executor.

#### Phase 13F — whole-pipeline artifact and theorems

Files: `Passes/DialectPipeline.lean`, new theorem-focused tests.

1. Make compilation return a single artifact owning the exact target R1CS and
   the composed codec.
2. Prove `pipeline_witness_iff` by codec composition.
3. Prove `generated_witness_iff` by specializing to `genWitness`.
4. Prove observable readback for the whole pipeline.
5. Where totality conditions hold, derive or connect the existing whole-program
   `PresReflPass` result.

Gate: all three whole-pipeline theorems compile with no additional axioms and
no `sorry`.

#### Phase 13G — CLI cutover and bridge removal

Files: `CLI.lean`, `DialectPipeline.lean`, `WitnessExecution.lean`, scripts and
documentation.

1. Route `--auto`, `--input`, and `--oracle` through source generation followed
   by `artifact.forward`.
2. Run the proved source or target checker before serialization and report the
   named failing boundary.
3. Delete manual object-slot seeding and direct FlatIR execution from
   `DialectPipeline`.
4. Delete or reduce `WitnessExecution` to the modular source-evaluator wrapper.
5. Keep binary/JSON output behavior and `--legacy` unchanged.
6. Run all fixture, differential, oracle, division, `snarkjs`, axiom-audit, and
   zero-sorry checks.

Gate: the CLI contains no witness-layout knowledge; it only calls
`genWitness`, `compileArtifact`, and `artifact.forward`.

### Phase 13 completion report

- Added generic proof-carrying `CompilationArtifact`, identity/composition,
  constructive transporting-pass roles, and a two-pass theorem test.
- Added typed runtime faults and a static per-dialect handler family. The source
  evaluator handles only structural `Call`; StructObject, Oracle, Felt, and
  ConstrainEq are independently assembled leaf handlers.
- Froze Oracle exhaustion as `oracleUnderflow`. Division-by-zero is the named
  leaf/backend-validity failure.
- Defined finite `SourceWitness` observables (`inputs` and reachable encoded
  object slots). Transient interpreter and target-only state is excluded.
- Moved StructObject seeding/readback into `StructObjectPass`, SSA witness
  materialization into `R1CSLikePass`, and R1CS auxiliary construction/readback
  into `FlatIRWitnessCodec`.
- Equality assertions no longer reject transport. `checkSource` independently
  decides satisfaction and is proved equivalent to `Source.satisfies`.
- `EntryCompilationArtifact` owns the exact FlatIR constraint observation,
  layout metadata, exact R1CS target, forward transport, and readback.
- Proved `pipeline_witness_iff`, `generated_witness_iff`, and
  `pipeline_readback` for every successful transport, with no new axioms or
  `sorry`.
- Removed the private/manual FlatIR witness interpreter and inline object-slot
  arithmetic from `DialectPipeline`; the CLI now uses generation, checking,
  and `artifact.forward`.
- Full fixture, differential, Oracle, division, JSON/binary, and `snarkjs`
  validation remains green. Legacy witness comparison is intentionally skipped
  only for `nondet`, because `--legacy` has no Oracle input channel.

The theorem's source language is the artifact's canonical constraint
observation, not parser syntax. Parser/typing correctness and a theorem that a
particular source compute program always generates a satisfying candidate are
orthogonal future results; the pointwise theorem intentionally permits
unsatisfying candidates.

---

## Phase 14 — Typed-source-to-artifact correctness `[complete]`

### Goal

Lift Phase 13's constructive theorem from the canonical constraint observation
to the original typed dialect module. Define direct source constraint semantics
independently of erasure, prove that the Oracle → Call → StructObject prefix
produces the same observation checked by the artifact, and derive the full
typed-source/R1CS witness theorem.

### Scope

- Give `[Call, StructObject, Oracle, Felt, ConstrainEq]` a direct, call-aware
  constraint semantics over one static object state.
- Keep compute generation and constraint checking separate. A generated
  candidate may be unsatisfying; the theorem must still be pointwise.
- Relate finite `SourceWitness` inputs/object slots to the direct source state.
- Prove Oracle projection is irrelevant to legal constraint bodies rather than
  just relying on zero substitution.
- Prove Call expansion and StructObject encoding preserve and reflect the
  direct source observation used by `Source.satisfies`.
- Retain the Phase-13 artifact and backend theorems unchanged; Phase 14 adds a
  source-facing layer above them.

### Theorem targets

```lean
theorem source_checker_iff
    (hcompile : compileSource program = .ok artifact) :
    checkTypedSource source program = true ↔
      TypedSource.satisfies source program

theorem source_artifact_iff
    (hcompile : compileSource program = .ok artifact) :
    TypedSource.satisfies source program ↔
      Pipeline.Source.satisfies (artifact.project source) artifact.entry

theorem typed_source_r1cs_iff
    (hcompile : compileSource program = .ok artifact)
    (hforward : artifact.forward source = .ok target) :
    TypedSource.satisfies source program ↔
      R1CS.satisfies target artifact.target

theorem generated_typed_source_r1cs_iff
    (hgen : genWitness program inputs oracle = .ok source)
    (hcompile : compileSource program = .ok artifact)
    (hforward : artifact.forward source = .ok target) :
    TypedSource.satisfies source program ↔
      R1CS.satisfies target artifact.target
```

Exact structure names may vary, but `TypedSource.satisfies` must inspect the
typed source module directly. It may not be defined by invoking compilation or
the artifact checker.

### Phase 14A — direct typed-source semantics `[done]`

Files: new `Dialects/TypedSourceSemantics.lean`, source-semantics tests.

1. Define direct constraint execution for the object-aware leaf set.
2. Add topologically recursive Call execution over that state.
3. Treat Oracle in constraint bodies as an explicit semantic impossibility;
   malformed unchecked syntax gets a named failure/false observation.
4. Define canonical initialization from finite `SourceWitness` inputs and
   object slots.
5. Add focused tests for nested calls, member reads, arithmetic, equality, and
   illegal Oracle statements.

Gate: typed source constraints can be evaluated without calling any erasure or
lowering function, and the evaluator contains only one structural `Call` case.

Result:

- Added executable direct semantics for the full typed source set without
  invoking compilation or erasure.
- `Call` is the only structural evaluator case; StructObject, Oracle, Felt, and
  ConstrainEq are interpreted by the residual leaf layer.
- Added finite canonical initialization and the `checkTypedSource` adapter for
  Phase-13 `SourceWitness` values.
- Added `checkTypedSource_true_iff` and focused nested-call/object/arithmetic/
  equality/illegal-Oracle tests.
- Added the generic `cap_le_of_capsLE` lemma and proved certified constraint
  bodies cannot contain Oracle operations.

### Phase 14B — Oracle and Call correspondence `[done]`

Files: `OracleErasure.lean`, `CallErasure.lean`, theorem tests.

1. Prove well-formed constraint bodies contain no Oracle operation.
2. Prove Oracle projection preserves direct constraint observations.
3. Prove hygienic Call expansion agrees with direct recursive Call execution.
4. Package both results as pointwise structural-prefix certificates.

Gate: the direct full-source observation is equivalent to the call-free
object-aware observation after successful Oracle and Call erasure.

Result:

- Oracle correspondence is complete. `OracleFreeBody` follows from constraint
  capabilities, `evalBody_lowerBody` proves recursive direct execution agrees
  with successful projection, and `checkAt_eq_checkProjectedAt` packages the
  selected-entry pointwise certificate.
- Added direct call-free Boolean execution and proved equivalence with existing
  propositional object-residual semantics.
- Proved recursive hygienic Call expansion agrees with direct projected-source
  execution. Simulation preserves constraint truth, all SSA-defined values,
  witness/cursor state, future object aliases, and fresh object storage.
- Added `PrefixCertificate`, `structuralPrefix_check_eq`, and
  `structuralPrefix_satisfies_iff`, composing successful Oracle projection with
  selected Call expansion into pointwise preservation/reflection certificates.
- Added generic `CallErasure.eraseModule_struct` extraction for successful
  module erasure.

### Phase 14C — StructObject correspondence `[done]`

Files: `StructObjectPass.lean`, `ObjectResidualSemantics.lean`.

1. Prove `seedCanonicalWitness` represents canonical source inputs and every
   reachable encoded object coordinate.
2. Prove `lowerBody` preserves/refects the direct object-aware constraint
   observation under the existing alias/path state relation.
3. Connect direct source satisfaction to the Phase-13 canonical checker.
4. Prove finite readback covers exactly the selected entry's observable span.

Gate: `source_artifact_iff` compiles with no `sorry` or new axioms.

Result:

- Proved canonical seeding for parameters and every reachable encoded object
  coordinate, plus exact finite readback of selected witness span.
- Proved direct `lowerBody` preservation/reflection under alias/path relation,
  including SSA values, object aliases, reachable coordinates, and untouched
  locals.
- Proved leaf materialization succeeds with satisfying FlatIR witness exactly
  when direct object-erased semantics accepts canonical seed.
- Aligned direct Felt division observation with backend validity: division by
  zero is false at constraint layer and named failure during materialization.
- Added `source_artifact_iff`, connecting certified object-aware source
  satisfaction to Phase-13 `Pipeline.Source.satisfies` under exact artifact
  metadata and canonical finite lengths.

### Phase 14D — whole typed-source artifact `[done]`

Files: `Passes/DialectPipeline.lean`, theorem-focused tests.

1. Package the original full module, selected entry, constraint artifact, and
   structural correspondence evidence together.
2. Prove `typed_source_r1cs_iff` by composing `source_artifact_iff` with
   Phase 13's `pipeline_witness_iff`.
3. Derive `generated_typed_source_r1cs_iff` by specialization.
4. Preserve exact finite readback and the existing existential correctness
   hierarchy.

Gate: the final theorem mentions the original typed module and the exact R1CS
returned by compilation.

Result:

- Added `EntryLoweringArtifact`, retaining selected Call expansion, certified
  Call-free function, certified StructObject result, and exact leaf program.
- Added `TypedEntryCompilationArtifact`, intrinsically tying original typed
  module and entry to Oracle projection, all structural certificates, and exact
  backend artifact.
- Added `typed_source_artifact_iff`, `typed_source_r1cs_iff`, and
  `generated_typed_source_r1cs_iff` by ordinary composition of pass-local
  preservation/reflection results.
- Successful forwarding implies canonical finite source lengths; whole typed
  transport preserves exact readback through `typed_pipeline_readback`.

### Phase 14E — executable integration and validation `[done]`

Files: CLI pipeline, tests, guarantees, roadmap.

1. Run the direct typed-source checker before serialization and distinguish a
   source constraint failure from a transport/runtime fault.
2. Keep the artifact checker as a differential assertion during migration.
3. Add direct-vs-erased differential fixtures, including nested objects/calls
   and nonzero Oracle witnesses.
4. Run full build, Lean tests, zero-sorry and axiom audits, CLI smoke,
   `snarkjs`, and graph refresh.

Gate: direct source checking and artifact checking agree on every supported
fixture, and the typed-source/R1CS theorems use only standard axioms.

Result:

- Dialect compilation now retains certified structural intermediates rather
  than rebuilding an evidence-free raw body path.
- Witness CLI checks direct typed-source semantics first, reports source
  constraint failure distinctly, then runs erased artifact checker as a
  differential assertion before transport.
- `typed_source_check_eq_artifact` proves both executable checkers agree for
  every canonical source witness; generated witnesses are canonical by
  `generateSourceWitness_canonical`.
- Existing nested-call, StructObject, and nonzero-Oracle fixtures exercise the
  differential path; full build, integration, backend, axiom, sorry, and graph
  gates pass.

---

## Phase 15 — Legacy extraction and adversarial gate `[done]`

Files: active imports/CLI, parser AST analysis, tests, all current docs.

1. Commit Phase-14 completion as `b608671`.
2. Create `legacy-infrastructure` branch at exact checkpoint.
3. Remove StructIR language, lowering, compaction, composition, CLI selector,
   and legacy-only tests from active branch.
4. Extract topology, call-target parsing, struct indexing, and SSA numbering
   from old lowering into dialect-agnostic `Parsers/ASTAnalysis.lean`.
5. Add full-feature adversarial LLZK fixture with valid and deliberately invalid
   Oracle cases.
6. Update all active project documentation and smoke gates.

Gate: no active source imports removed architecture; valid adversarial witness
passes snarkjs; altered Oracle fails direct typed-source checker; retired CLI
selectors fail; full Lean/build/smoke/sorry/axiom gates pass.

Result:

- Active compiler has one executable dialect-native path.
- Retired implementation remains recoverable from named branch, not source tree.
- Frontend no longer depends on StructIR lowering for shared AST analysis.
- Integration suite exercises nested compute/constrain calls, object storage,
  public members, every Felt operation, two Oracle reads, and negative checking.

---

## Intended explicit pipeline

```text
AST
  → Module [Call, StructObject, Oracle, d₁, ..., dₙ]
  → Module [Call, StructObject, d₁, ..., dₙ]  -- explicit oracle projection
  → Module [StructObject, d₁, ..., dₙ]  -- explicit callErase value
  → Module [d₁, ..., dₙ]                -- explicit structObjectErase value
  → progressively smaller leaf sets
  → constraint dialect
  → backend
```

Semantic state changes only at declared stage boundaries. Pass correctness
relations connect those state types, and ordinary explicit pass composition
connects the stages. Witness computation is separate from this program path:
it runs once against the full source module, then the compilation artifact's
composed codec transports the resulting canonical source witness.

## Resolved design decisions

1. Structural erasure passes are explicit values, not automatically selected
   typeclass instances.
2. Compiler stages have statically known semantic state types.
3. No heterogeneous runtime effect list or universal state builder.
4. Call erasure precedes StructObject erasure and is polymorphic over residual
   dialects.
5. Structural dialects use a canonical prefix order until arbitrary reordering
   is justified by a concrete use case.
6. Witness generation executes once at the source level; target stages do not
   re-execute compute bodies.
7. Source execution is modular by dialect but uses one statically selected
   source state, not a heterogeneous effect list.
8. Transient execution state is projected to a canonical source witness before
   compiler transport begins.
9. Program translation and witness-layout metadata are packaged in one
   compilation artifact so they cannot diverge.
10. `PresReflPass` remains the existential correctness baseline. Constructive
    transport and observable round-trip are strictly stronger opt-in layers.
11. An unsatisfied constraint yields an unsatisfying transported witness; it is
    not treated as transport failure. Runtime faults and invalid backend
    preconditions remain explicit `Except` boundaries.

## Open questions

1. Should `returnVar` be required to be below fresh bound for every module-safe pass?
2. What is the minimal `CallProtocol State` that supports object-aware calls
   without exposing StructObject-specific fields to generic Call erasure?
3. Can rename/frame laws be attached directly to semantic handlers, or should
   they form separate reusable certificates?
4. Should malformed selector/arity/kind calls remain an executable `Except`
   boundary, or move into a stronger intrinsically valid module type?
5. Should `ObservableEq` quantify over all canonical source witness coordinates
   or only coordinates reachable from the selected entry struct?
6. Which existing optimization passes can provide constructive codecs, and
   which should remain constraint-only `PresReflPass` values?
