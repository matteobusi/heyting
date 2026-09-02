# Heyting Roadmap: Fully Verified, Multi-Backend LLZK Compiler

**Status:** approved architecture direction (2026-06).
**Goal:** a fully verified end-to-end production compiler for LLZK with multiple
constraint-system backends.

---

## 1. Where we are

Heyting retains a fully verified fixed pipeline as a quarantined reference:

```
LLZK AST  --(unverified Lowering)-->  StructIR  --✓-->  FlatIR  --✓(compact)--✓-->  R1CS
```

This composition now lives under `Legacy.Pipeline`. In parallel, the
dialect-native pipeline is executable from AST through Oracle, Call, and
StructObject erasure, R1CSLike, and R1CS. Struct-object operations have typed
dialect syntax, standalone state semantics, frontend lowering, and an encoded
witness-local backend erasure. Typed compute execution and oracle-stream
nondeterminism now generate backend witnesses, and the dialect path is the CLI
default. `--legacy` retains the proved reference composition.

Phase 13 replaced the operational witness bridge with modular source-level
generation and a proof-carrying entry artifact. The artifact owns finite source
observables, structural layout metadata, leaf materialization, the exact R1CS,
pointwise source/R1CS satisfaction equivalence, and exact canonical readback.
Phase 14 lifts that result to original typed module. Direct
call-aware typed-source constraint semantics and canonical initialization are
implemented. Oracle projection and hygienic Call expansion correspondence are
proved and packaged as pointwise structural-prefix certificates. StructObject
correspondence, canonical object encoding/readback, exact leaf materialization,
and source-artifact satisfaction equivalence are proved. Whole typed-entry
artifact retains every structural certificate and exact backend target;
typed-source/R1CS equivalence, generated specialization, checker agreement,
and finite readback are complete. CLI validates direct source semantics before
artifact differential checking and transport.

Both legacy IR-level passes (`StructIRToFlatIR`, `FlatIRToR1CS`, plus
compaction) remain fully proved `PresReflPass` instances, composed via
`PresReflPass.compose` (`Heyting/Core/Pass.lean`).

### Gap assessment (summary)

| Gap | Detail |
|---|---|
| Free functions / same-struct helpers | Rejected at lowering. `docs/WARNING.md` §8 — 156+ proof references assume the exactly-two-functions (`@compute`/`@constrain`) model. |
| Feature dialects | No arrays, bool ops, globals, casts, templates (`poly`), `scf` loops, `include`. |
| Front half unverified | Parser → AST → StructIR lowering has no correctness statement. |
| `llzk.nondet` | Typed Oracle handler with explicit stream exhaustion; constraint projection is explicit. |
| Single backend | R1CS only; no CCS, no Plonkish. |
| Proof scalability | `StructIRToFlatIR` is a 7188-line monolith; per-op proof reuse is poor. |

### Binding decisions

1. **Composable dialects.** Each dialect packages its own ops + semantics. A
   module is typed by the set of dialects it may use. Each pass is
   preservation/reflection-verified and *erases one dialect* into a subset of
   the remaining ones. The compiler is a sequence of erasure passes shrinking
   the dialect set until only the lowest constraint dialect remains.
2. Free functions become **first-class** (not AST-inlined away invisibly).
3. **CCS** is the verified lowest constraint dialect, with verified R1CS
   specialization and a Plonkish serializer.
4. Verified AST→IR lowering + parser round-trip validation.
5. Verified per-run witness checker.
6. Real `llzk.nondet` semantics (oracle-stream).

---

## 2. Architecture

### Three layers

```
text
  │  generic parser (dialect-agnostic, MLIR generic form: mnemonic +
  │  operands + results + attrs + regions)
  ▼
GenericOp tree
  │  typing / skeleton extraction (unverified now; Phase 6 verifies):
  │  interpret struct.def / function.def / module ops → callable order Fin n,
  │  member tables, OpCtx per body; per-dialect lowerOp on leaf ops
  ▼
Module Δfull, calls = true ───────────── MIDDLE: dialect erasure passes
  │  skeleton-preserving, Vs = Vt (one shared VarId type), witnessRel ≈
  │  equality on shared variables; Δ shrinks to core; EraseCalls last
  ▼
Module Δcore, calls = false ──────────── BOTTOM: fixed two-pass backend
  │  flatten: skeleton + struct-op erasure, (path × slot) → Nat
  │  core lowering: felt + constrainEq → CCS
  ▼
CCS → verified R1CS specialization / Plonkish serializer
```

Key consequences:

- **Front end is uniform.** Regions make `struct.def`/`function.def`/module
  parse generically — no per-dialect parser machinery. Structural dialects
  are special at *typing* time (they build the `OpCtx` every other dialect's
  op type is indexed by), not at parse time. Leaf-op lowering and round-trip
  proofs (Phase 6) decompose per dialect via mnemonic dispatch.
- **VarId coherence.** All dialect ops live inside the same skeleton, so all
  middle-layer passes share one VarId type and get a canonical, near-trivial
  witness relation. The heterogeneous witness relations (instance paths →
  Nat → R1CS ids) — the hard proof artifacts — are confined to the fixed
  bottom passes, which exist and are proved today. `PresReflPass.compose`
  is V-polymorphic and stitches the regimes together.
- **Fixed backend = today's pipeline, minus inlining.** Current
  `StructIRToFlatIR` survives as the flatten pass, simplified by extracting
  call inlining into a middle-layer `EraseCalls` pass (the principled seam
  for splitting the 7188-line monolith: freshening/frame proofs go to
  `EraseCalls`, encoding proofs stay in flatten).

### Encoding (`Heyting/Core/Dialect.lean`, `Core/Stmt.lean`)

Statements are **flat sums of leaf ops** — no recursion through subterms; the
only recursion is `call`, through the module index. A dialect is an `OpSig`:
an op type indexed by `OpCtx` (= number of structs `n`, current struct index
`i`, member count), plus metadata (`dest`, `reads`, `mapVars`, `objEffect`,
`objReads`, capability). A dialect set is a `List OpSig`; statements are:

```lean
inductive Stmt (Δ : DialectSet) (calls : Bool) (γ : OpCtx) (F : Type)
  | op   (d : Fin Δ.length) (payload : (Δ.get d).Op γ F)
  | call (h : calls = true) (target : Fin γ.i) (sel : Nat) (args : List LocalVar)
```

Design points:

- `Fin Δ.length` index (not Prop-valued membership) so handler dispatch
  computes and `fin_cases` gives exact case splits.
- `call` stays a **core constructor** gated by a type-level Bool: the
  termination measure `(i, stmts.length)` remains verbatim today's; "function
  dialect erased" = flipping `calls` to `false` (constructor becomes
  uninhabitable). Phase 3 generalizes `target` to a single topologically
  ordered callable space (free funcs + compute/constrain/helpers) with
  selector `sel`.
- The structural skeleton (Module/StructDef, `Fin n` topological indexing,
  `Fin numMembers`, SSA/objSafe/noDupReads) stays core, implemented once
  generically via OpSig metadata.
- One `Stmt` type for compute+constrain; `FuncDef` carries a capability kind
  with well-formedness proof `body.all (cap · ≤ kind)` (mirrors LLZK
  WitnessGen/ConstraintGen traits).

### Semantics (`Core/Semantics.lean`)

Per-dialect `DialectSem` handlers (`constrainStep`/`computeStep` + laws:
reads-congruence, dest-frame, rename-commutation, decidability). Generic
`evalConstrainBody`/`evalComputeBody` defined once over a handler family,
producing `ModuleLang Δ calls : Language VarId F`. The existing
`Language`/`PresReflPass`/`TrinitaryCC` framework is reused unchanged.

### Pass forms

- `ErasePass D Δ Δ'` — removes dialect `D` from the set.
- `OptPass Δ` — Δ-preserving optimization (compaction precedent).
- Generic **macro-expansion theorem**: pass author supplies `lowerOp` + a
  per-op simulation lemma; the framework lifts to module-level pres/refl.
  Tiered: **T1** (no fresh locals, Phase 0) and **T2** (fresh temporaries with
  frame discipline, Phase 2 — where the 7188-line proof's complexity actually
  lives). Never forced; bespoke proofs remain allowed.

### Migration strategy

Incremental via **isomorphism bridges**, never big-bang. A syntactic iso with
satisfies-iff is itself a `PresReflPass`, so `iso ∘ existing-pass ∘ iso⁻¹`
keeps the existing verified passes as black boxes and the CLI green while
native re-ports land one at a time.

### Pipeline (erasure order, front → back)

Canonical total order on dialects; every pass lowers strictly downward
(emits only into dialects below it). Any module's dialect subset is then
automatically schedulable, and composition is type-checked — a scheduling
bug is a type error, not a runtime failure.

1. poly/include monomorphization, scf unrolling — initially AST-level rewrites
   with translation validation; verified-pass status deferred until the
   encoding proves out
2. global const-inlining
3. array scalarization (static sizes)
4. bool + `constrain.in` via bit decomposition
5. cast
6. non-native felt ops (pow, bitwise)
7. **function erasure** (`EraseCalls`: inlining; flips `calls`) — deliberately
   *late*, so feature-dialect lowerings (4–6) may emit calls into shared
   verified gadget functions (bit decomposition, range checks) instead of
   inline-expanding at every use site
8. fixed backend: flatten (skeleton + struct-op erasure, member → witness
   slot, paths → Nat)
9. fixed backend: felt + constrainEq lowering into **CCS**
10. verified CCS→R1CS specialization + Plonkish serializer

Open question (defer): whether `EraseCalls` runs strictly before struct-op
erasure or interleaved with it inside flatten. Constrain-call inlining must
remap callee member reads through caller instance paths, easiest while
struct ops are still present — so "before" is the likely answer — but
today's monolith does them interleaved, so keeping that is cheap if
extraction proves awkward.

---

## 3. Phases

### Phase 0 — framework core (4–5 pw, critical path; gate everything on it)

`Core/Dialect.lean`, `Core/Stmt.lean`, `Core/Module.lean`,
`Core/Semantics.lean`, `Core/DialectPass.lean`, `Core/DialectTactics.lean`;
`Dialects/Felt.lean`, `Dialects/ConstrainEq.lean`; T1 macro-expansion theorem;
proof-of-concept erasure pass (feltNeg → const+sub — deliberately needs one
fresh temp, to de-risk T2 early); FlatIR iso.

**Acceptance gates:** no `cast`/`HEq` in PoC proofs; concrete-Δ dispatch
reduces by `rfl`/`simp`; 0 sorries.

### Phase 1 — iso-bridged migration (3–4 pw)

`Dialects/StructOps.lean`, `Passes/IsoStructIR.lean` / `IsoFlatIR.lean`;
transported pipeline; CLI parity tests.

### Phase 2 — native re-port, split the monolith (5–7 pw)

T2 theorem; `Passes/EraseCalls.lean`, `EraseStructOps.lean`, `EraseFelt.lean`,
`Compact.lean`; retire isos; quarantine old StructIR/FlatIR.
The monolith splits along the inlining/encoding seam: freshening and frame
discipline proofs (`StructIRFreshen` machinery) move to `EraseCalls`
(middle layer, shared VarId, near-trivial witnessRel); witness-encoding
proofs (`witnessBase`, `encodeWitnessPos`) stay in the fixed flatten pass.
**Success metric:** 7188 lines → ≤ ~3000.

### Phase 3 — first-class function dialect (3–4 pw)

Unified callable space (`Fin k` topological order over free funcs + struct
funcs + helpers), selector-aware call + erasure; parser/lowering accept free
`function.def` (Parser.lean:659,733,752) and helpers (Lowering.lean:406-407).
Closes WARNING.md §8.

### Phase 4 — CCS + multi-backend (3–4 pw, parallel with 1–2)

`Languages/CCS.lean`, retarget felt-erasure, verified `Passes/CCSToR1CS.lean`,
`Backends/Plonkish.lean` (+ executable checker). snarkjs differential stays
green.

### Phase 5 — feature dialects (10–14 pw, 2–3 parallel streams)

global (0.5–1) → array-static (3–4) → bool/`constrain.in` + bit-decomposition
kit (4–5) → cast (1–2) → felt pow/bitwise (3); scf/poly AST-level front-end
(3–4) anytime.

### Phase 6 — front-half verification + witness checker (4–6 pw)

`Parsers/ASTSemantics.lean`; verified typing of the GenericOp tree into
`Module Δ` (skeleton extraction + per-dialect `lowerOp`; fallback: verified
per-run validator); `Parsers/Printer.lean` + round-trip/golden harness vs
llzk-lib — round-trip decomposes per dialect via mnemonic dispatch;
`Core/WitnessChecker.lean` (`checkWitness ↔ satisfies`, generic from
`stepDecidable`); `Dialects/Nondet.lean` with oracle-stream semantics.

### Phase 7 — hardening (3–4 pw, ongoing)

CI (build, zero-sorry, axiom audit, snarkjs/llzk-lib differential),
Pos-threaded error messages, `docs/dialects.md` dialect-author guide,
per-dialect lake targets, benchmarks.

**Critical path:** 0 → 1 → 2 → {3 ∥ 4} → 5(bool→cast) → 6.
**Total: ~36–48 person-weeks.**

---

## 4. Top risks + fallbacks

1. **Generic fresh-temp theorem (T2) may not generalize.** Mitigation: tiered
   API, bespoke proofs allowed, PoC surfaces it in week 2.
2. **Dependent-index friction** (stuck `Δ.get`, `HEq`). Mitigation: canonical
   dialect order, no list permutation in proofs, tactic+simp pack; fallback to
   a universal inductive syntax keeping OpSig/handlers/pass theorems.
3. **Generic evaluator termination / equation lemmas.** Mitigation:
   call-as-core-constructor keeps today's measure, mirror current eval shape,
   hand-proved unfolding lemmas.
