# Graph Report - .  (2026-05-27)

## Corpus Check
- 52 files · ~87,196 words
- Verdict: corpus is large enough that graph structure adds value.

## Summary
- 175 nodes · 192 edges · 37 communities (10 shown, 27 thin omitted)
- Extraction: 89% EXTRACTED · 11% INFERRED · 0% AMBIGUOUS · INFERRED: 22 edges (avg confidence: 0.82)
- Token cost: 0 input · 0 output

## Community Hubs (Navigation)
- [[_COMMUNITY_Circom Binary Backends|Circom Binary Backends]]
- [[_COMMUNITY_Correctness Framework Docs|Correctness Framework Docs]]
- [[_COMMUNITY_StructIR & FlatIR-R1CS Bridge|StructIR & FlatIR-R1CS Bridge]]
- [[_COMMUNITY_LLZK Parser & Dialects|LLZK Parser & Dialects]]
- [[_COMMUNITY_FlatIR Language Core|FlatIR Language Core]]
- [[_COMMUNITY_CLI & Prime Fields|CLI & Prime Fields]]
- [[_COMMUNITY_Abate Pass Hierarchy|Abate Pass Hierarchy]]
- [[_COMMUNITY_Pass Compilation Pipeline|Pass Compilation Pipeline]]
- [[_COMMUNITY_R1CS Language Core|R1CS Language Core]]
- [[_COMMUNITY_Legacy Pass Chain|Legacy Pass Chain]]
- [[_COMMUNITY_Checked Semantics Results|Checked Semantics Results]]
- [[_COMMUNITY_Legacy IR Docs|Legacy IR Docs]]
- [[_COMMUNITY_R1CS Constraints|R1CS Constraints]]
- [[_COMMUNITY_Agent Guide|Agent Guide]]
- [[_COMMUNITY_natLeBytes Helper|natLeBytes Helper]]
- [[_COMMUNITY_R1CS Summary Struct|R1CS Summary Struct]]
- [[_COMMUNITY_Trace Stutter|Trace Stutter]]
- [[_COMMUNITY_PTerm Symbolic|PTerm Symbolic]]
- [[_COMMUNITY_PathSubst|PathSubst]]
- [[_COMMUNITY_PTerm Interpretation|PTerm Interpretation]]
- [[_COMMUNITY_FlatIR Program|FlatIR Program]]
- [[_COMMUNITY_Reads Accessor|Reads Accessor]]
- [[_COMMUNITY_Dest Accessor|Dest Accessor]]
- [[_COMMUNITY_AST Position|AST Position]]
- [[_COMMUNITY_AST Type|AST Type]]
- [[_COMMUNITY_AST Pretty-Print|AST Pretty-Print]]
- [[_COMMUNITY_R1CS Extract Witness|R1CS Extract Witness]]
- [[_COMMUNITY_Call Target Parse|Call Target Parse]]
- [[_COMMUNITY_Topological Sort|Topological Sort]]
- [[_COMMUNITY_Compress Tactics|Compress Tactics]]
- [[_COMMUNITY_README Overview|README Overview]]
- [[_COMMUNITY_Proof Status Doc|Proof Status Doc]]
- [[_COMMUNITY_Resolved Issues|Resolved Issues]]
- [[_COMMUNITY_macOS Cache Bug|macOS Cache Bug]]
- [[_COMMUNITY_LLZK Attributes|LLZK Attributes]]
- [[_COMMUNITY_LLZK Array Dialect|LLZK Array Dialect]]
- [[_COMMUNITY_LLZK Poly Dialect|LLZK Poly Dialect]]

## God Nodes (most connected - your core abstractions)
1. `Heyting CLI (hey compile)` - 15 edges
2. `Pass typeclass` - 9 edges
3. `PresReflPass typeclass` - 9 edges
4. `StructIRToFlatIR.CorrectPass (PresReflPass)` - 9 edges
5. `StructIR.ConstrainStmt` - 8 edges
6. `FlatIRToR1CS.CorrectPass (PresReflPass)` - 8 edges
7. `FieldBytes typeclass` - 5 edges
8. `R1CSBinary.systemToBinary` - 5 edges
9. `WireAssignment.fromSystem` - 5 edges
10. `CLI.BN128_p (BN254 modulus)` - 5 edges

## Surprising Connections (you probably didn't know these)
- `Pass1 StructIR→StructInlineIR (legacy)` --semantically_similar_to--> `StructIRToFlatIR.CorrectPass (PresReflPass)`  [INFERRED] [semantically similar]
  docs/handover/PASS1_STRUCTIR_TO_STRUCTINLINEIR.md → Heyting/Passes/StructIRToFlatIR.lean
- `WellFormedForCompile invariant (Pass 2)` --semantically_similar_to--> `StructIR.isSSA`  [INFERRED] [semantically similar]
  docs/handover/PASS2_STRUCTINLINEIR_TO_MEMBERLESSIR.md → Heyting/Languages/StructIR.lean
- `Pipeline Description (AGENTS.md)` --references--> `Heyting CLI (hey compile)`  [INFERRED]
  AGENTS.md → Heyting/CLI.lean
- `Key Invariants (no sorries, std axioms only)` --rationale_for--> `CLI.BN128_p (BN254 modulus)`  [INFERRED]
  AGENTS.md → Heyting/CLI.lean
- `llzk::felt dialect` --rationale_for--> `StructIR.ConstrainStmt`  [INFERRED]
  docs/llzk-dialects.md → Heyting/Languages/StructIR.lean

## Hyperedges (group relationships)
- **Circom binary serialization stack** — fieldbytes_class, r1csbinary_systemtobinary, witnessbinary_witnesstobinary, wireassignment_encode [EXTRACTED 0.90]
- **Prime field FieldBytes instances** — cli_bn128_p, cli_babybear_p, cli_goldilocks_p, cli_mersenne31_p [EXTRACTED 1.00]
- **JSON serialization stack** — r1csjson_systemtojson, witnessjson_witnesstojson, r1csjson_summarize [EXTRACTED 0.90]
- **Abate et al. correctness framework (CC~/TPσ/TPτ)** — trinitarycc_cc, trinitarycc_wpsigma, trinitarycc_wptau, trinitarycc_tpsigma_iff_cc [EXTRACTED 0.95]
- **Pass class hierarchy** — pass_class, preservingpass_class, reflectingpass_class, presreflpass_class [EXTRACTED 1.00]
- **Constraint language instances (StructIR, FlatIR, R1CS)** — r1cs_language_instance, flatir_satisfiesinstr, structir_constrainstmt [EXTRACTED 0.90]
- **Active StructIR→FlatIR→Compact→R1CS pipeline** — structirtoflatir_compileprogram, flatircompact_compileprogram, flatirtor1cs_compileprogram, pipeline_compileprogram [EXTRACTED 1.00]
- **All proved PresReflPass instances** — structirtoflatir_correctpass, flatircompact_correctpass, flatirtor1cs_correctpass, pipeline_correctpass [EXTRACTED 1.00]
- **R1CS-pass proof tactics** — tactics_r1cs_arith, tactics_r1cs_unfold_sat, structirtoflatir_tactics_materialize_rename [EXTRACTED 0.90]
- **LLZK parser pipeline (tokenize → parse → lower)** — tokenizer_tokenize, llzk_parse, lowering_main [EXTRACTED 0.95]
- **All language handover docs** — handover_lang_flatir, handover_lang_r1cs, handover_lang_structir, handover_lang_memberlessir, handover_lang_structinlineir [EXTRACTED 1.00]
- **Per-pass guarantee docs** — guarantees_structirtoflatir, guarantees_flatirtor1cs, guarantees_flatircompact, guarantees_pipeline [EXTRACTED 1.00]
- **Active assumptions/limitations** — warning_nodup_reads, warning_lake_cache_macos, warning_private_axiom_primes [EXTRACTED 1.00]
- **Legacy 4-pass chain (deprecated)** — handover_pass2_legacy, handover_pass3_legacy, handover_pass4_proof_pattern [EXTRACTED 0.90]
- **LLZK Tier 1 foundational dialects** — llzk_dialect_felt, llzk_dialect_constrain, llzk_dialect_struct, llzk_dialect_function, llzk_dialect_common_attrs [EXTRACTED 1.00]
- **Heyting proof tactic set** — tactics_md_r1cs_arith, tactics_md_usage_pattern [EXTRACTED 0.95]

## Communities (37 total, 27 thin omitted)

### Community 0 - "Circom Binary Backends"
Cohesion: 0.10
Nodes (23): fileHeader, sectionHeader, u32LE, u64LE, R1CSBinary.constraintBytes, R1CSBinary.linCombBytes, R1CSBinary.saveR1CSBinary, R1CSBinary.systemToBinary (+15 more)

### Community 1 - "Correctness Framework Docs"
Cohesion: 0.16
Nodes (19): FlatIRCompact.CorrectPass (PresReflPass), FlatIRToR1CS.CorrectPass (PresReflPass), Guarantee: FlatIRCompact pass, Guarantee: FlatIR→R1CS pass, Pass correctness framework (GUARANTEES.md), Guarantee: full Pipeline composition, Pass1 StructIR→StructInlineIR (legacy), Pipeline composition handover (+11 more)

### Community 2 - "StructIR & FlatIR-R1CS Bridge"
Cohesion: 0.12
Nodes (19): ComputingLanguage typeclass, ComputingLanguage.computeWitness, witnessBase namespace partition, FlatIRToR1CS.compileInstr, FlatIRToR1CS.compileVar, FlatIRToR1CS.compileWitness, StructIR Handover doc, Pass1 Preservation Plan (witnessBase shift) (+11 more)

### Community 3 - "LLZK Parser & Dialects"
Cohesion: 0.12
Nodes (17): Intrinsic well-formedness via Fin, Guarantee: StructIR→FlatIR pass, llzk::constrain dialect, llzk::felt dialect, llzk::function dialect, llzk::struct (component) dialect, LLZK.parse / parseFile entry, LLZK.Lowering.lower (AST → StructIR.Module) (+9 more)

### Community 4 - "FlatIR Language Core"
Cohesion: 0.14
Nodes (16): FlatIR.Instr inductive, FlatIR.instrVars, FlatIR.satisfiesInstr, satisfiesInstr_congr theorem, FlatIRChecked.checkStep, FlatIR Handover doc, FlatIR description (languages.md), languages.md — IR overview (+8 more)

### Community 5 - "CLI & Prime Fields"
Cohesion: 0.21
Nodes (14): Key Invariants (no sorries, std axioms only), Pipeline Description (AGENTS.md), CLI.BABYBEAR_p, CLI.BN128_p (BN254 modulus), CLI.GOLDILOCKS_p, Heyting CLI (hey compile), hey CLI options (--prime-field etc.), Supported prime fields table (+6 more)

### Community 6 - "Abate Pass Hierarchy"
Cohesion: 0.20
Nodes (12): Witness abbreviation, Pass typeclass, ReflectingPass typeclass, ReflectingPass.compose, CC~ (trace-relating compiler correctness), σ (universal preimage), τ (existential image), TPσ_iff_CC lemma (+4 more)

### Community 7 - "Pass Compilation Pipeline"
Cohesion: 0.22
Nodes (10): FlatIRCompact.compactInstr, FlatIRCompact.compactVar, FlatIRCompact.compileProgram, FlatIRCompact.denseVars, FlatIRCompact.usedVars, FlatIRToR1CS.compileProgram, Pipeline.compileFlatIR, Pipeline.compileProgram (+2 more)

### Community 8 - "R1CS Language Core"
Cohesion: 0.22
Nodes (9): assignDiv two-constraint encoding (resolved), R1CS Handover doc, Language typeclass, llzk::r1cs backend dialect, R1CS.evalLinComb, R1CS Language instance, R1CS.satisfies, R1CS.System (+1 more)

### Community 9 - "Legacy Pass Chain"
Cohesion: 0.33
Nodes (6): Fixed-env vs state-threaded semantic gap, WellFormedForCompile invariant (Pass 2), Pass 2: StructInlineIR → MemberlessIR (legacy), Pass 3: MemberlessIR → FlatIR (legacy), StructIR.isSSA, NoDuplicateReads assumption

## Knowledge Gaps
- **75 isolated node(s):** `Heyting Agent Guide`, `Pipeline Description (AGENTS.md)`, `Key Invariants (no sorries, std axioms only)`, `u64LE`, `natLeBytes` (+70 more)
  These have ≤1 connection - possible missing edges or undocumented components.
- **27 thin communities (<3 nodes) omitted from report** — run `graphify query` to explore isolated nodes.

## Suggested Questions
_Questions this graph is uniquely positioned to answer:_

- **Why does `Heyting CLI (hey compile)` connect `CLI & Prime Fields` to `Circom Binary Backends`, `StructIR & FlatIR-R1CS Bridge`, `LLZK Parser & Dialects`, `Pass Compilation Pipeline`?**
  _High betweenness centrality (0.306) - this node is a cross-community bridge._
- **Why does `PresReflPass typeclass` connect `Correctness Framework Docs` to `FlatIR Language Core`, `Abate Pass Hierarchy`?**
  _High betweenness centrality (0.168) - this node is a cross-community bridge._
- **Why does `Pipeline.compileProgram` connect `Pass Compilation Pipeline` to `CLI & Prime Fields`?**
  _High betweenness centrality (0.168) - this node is a cross-community bridge._
- **Are the 2 inferred relationships involving `Heyting CLI (hey compile)` (e.g. with `Pipeline Description (AGENTS.md)` and `InputJSON.parseFieldElem`) actually correct?**
  _`Heyting CLI (hey compile)` has 2 INFERRED edges - model-reasoned connections that need verification._
- **Are the 4 inferred relationships involving `StructIR.ConstrainStmt` (e.g. with `StructIR.MemberType` and `materialize_rename_simp tactic`) actually correct?**
  _`StructIR.ConstrainStmt` has 4 INFERRED edges - model-reasoned connections that need verification._
- **What connects `Heyting Agent Guide`, `Pipeline Description (AGENTS.md)`, `Key Invariants (no sorries, std axioms only)` to the rest of the system?**
  _75 weakly-connected nodes found - possible documentation gaps or missing edges._
- **Should `Circom Binary Backends` be split into smaller, more focused modules?**
  _Cohesion score 0.10276679841897234 - nodes in this community are weakly interconnected._