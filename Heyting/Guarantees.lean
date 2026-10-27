/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.DialectPipeline
import Heyting.Backends.WireAssignment
import Mathlib.Data.List.Sigma

/-!
# Compiler guarantee

`compiler_guarantee` collects, for every successfully compiled entry, the properties the
compiler proves about its output. Let `M` be a typed module, `e` an entry,
`c : TypedEntryCompilationArtifact M e` a successful compilation, and `A := c.artifact`.

1. **Statement wires.** The statement wires of `A.target` (public outputs, then public
   inputs) are pairwise distinct, and the serializer layout places statement wire `i` at
   wire `i + 1`.
2. **Statement fidelity.** For every R1CS assignment `z`, the statement wires carry exactly
   the public part of the extracted source observation `A.readback z`.
3. **Completeness.** Every source instance `(x, w)` of `SourceRelation` is accepted by the
   prover map `A.forward`; its result is an R1CS instance for the same statement `x` and
   reads back to `w`.
4. **Soundness with extraction.** Every R1CS instance `(x, z)` extracts to the source
   instance `(x, A.readback z)`. The extractor reads fixed wires (a reindexing).
5. **Language equivalence.** `x` has a source witness iff it has an R1CS witness.
6. **Determinism.** For every key and observable of source observations, the source
   constraints determine the observable from the key iff the R1CS constraints determine it
   through the extractor (`determines_iff`). Compilation adds and removes no
   under-constrained witness pairs.

For the prover, `proveEntry_sound` and `proveEntry_complete` relate the executable prover to
the relation: it returns only R1CS instances for the public part of a satisfying generated
observation, and it succeeds whenever the generated observation satisfies the constraints.

## What the guarantee does not cover

* The parser and the AST-to-dialect frontend: the guarantee starts at the typed module.
* The bytes of `.r1cs`/`.wtns` files: only the wire layout is proved.
* Cryptographic properties of a proof system Π. Items 1–4 make the compilation a Levin
  reduction (`entryLevinReduction`) with the identity statement map, so for a Π that is
  knowledge-sound and zero-knowledge for the R1CS relation, "compile, then Π" is
  knowledge-sound (extractor `A.readback ∘ E_Π`) and zero-knowledge (simulator `S_Π`) for
  `SourceRelation`. That transfer argument is standard but not formalized here.
* Witness generation: the compute executor (`WitnessExecution.genWitness`) is the operational
  semantics of compute. It is not proved equal to upstream LLZK compute, and the
  theorems do not prove that compute output satisfies the constraints: `proveEntry_complete`
  takes that as a hypothesis. `WitnessExecution.genWitness_fault` proves that the executor
  fails only on run-time data.
-/

namespace Dialect.Pipeline

open WireAssignment

/-! ## Statement wires are distinct -/

/-- Indices kept by filtering an indexed list are distinct. -/
private theorem nodup_filter_zipIdx_snd {α : Type} (l : List α) (p : α × Nat → Bool) :
    ((l.zipIdx.filter p).map (·.2)).Nodup :=
  (List.nodup_zipIdx_map_snd l).sublist (List.filter_sublist.map _)

private theorem publicMemberSlots_nodup {n : Nat} (members : List (MemberDecl n)) :
    (EntryCompilationArtifact.publicMemberSlots members).Nodup := by
  have hinj : Function.Injective fun i : Nat ↦ VarIdEncoding.encode ([], i) := by
    intro i j h
    have := congrArg VarIdEncoding.decode h
    simpa [VarIdEncoding.decode_encode] using congrArg Prod.snd this
  exact (nodup_filter_zipIdx_snd members _).map hinj

private theorem publicFlagSlots_nodup (flags : List Bool) :
    (EntryCompilationArtifact.publicFlagSlots flags).Nodup :=
  nodup_filter_zipIdx_snd flags _

/-- The statement wires of a compiled target are pairwise distinct and are ordinary wires.

Proof sketch: output wires are `.var (numParams + j)` for distinct slots `j`; input wires are
`.var (paramOffset + i)` for distinct `i < computeParams`, hence below `numParams` because
`paramOffset + computeParams = numParams`. So the two lists are disjoint. -/
theorem target_statementVars_nodup [Field F] {n : Nat}
    {module : Module LLZK.DialectLowering.WitnessSourceSet n F} {entry : Fin n}
    (compiled : TypedEntryCompilationArtifact module entry) :
    compiled.artifact.target.statementVars.Nodup ∧
      R1CS.VarId.varOne ∉ compiled.artifact.target.statementVars := by
  have hle := compiled.lowering.computeParams_le
  set A := compiled.artifact with hA
  have houts : A.publicOutputSlots.Nodup := by
    simp only [hA, TypedEntryCompilationArtifact.artifact,
      EntryCompilationArtifact.ofLowering]
    exact (publicMemberSlots_nodup _).sublist List.filter_sublist
  have hins : A.publicInputSlots.Nodup := by
    simp only [hA, TypedEntryCompilationArtifact.artifact,
      EntryCompilationArtifact.ofLowering]
    exact (publicFlagSlots_nodup _).sublist List.filter_sublist
  have hoff : A.paramOffset + A.computeParams = A.numParams := by
    simp only [hA, TypedEntryCompilationArtifact.artifact,
      EntryCompilationArtifact.ofLowering]
    omega
  refine ⟨?_, ?_⟩
  · simp only [R1CS.System.statementVars, EntryCompilationArtifact.target]
    refine List.Nodup.append (houts.map fun _ _ h ↦ by simpa using h)
      (hins.map fun _ _ h ↦ by simpa using h) ?_
    intro v hout hin
    simp only [List.mem_map] at hout hin
    obtain ⟨j, -, rfl⟩ := hout
    obtain ⟨i, hi, heq⟩ := hin
    have hlt := A.publicInputSlots_lt i hi
    simp only [R1CS.VarId.var.injEq] at heq
    omega
  · simp [R1CS.System.statementVars, EntryCompilationArtifact.target]

/-! ## Witness generation

`compiler_guarantee` is about any source observation. The theorems below are about the
observation that the prover generates by running compute. The compute executor
(`WitnessExecution.genWitness`) is the operational semantics of compute; nothing here
relates it to upstream LLZK. -/

/-- Inversion of `generateSourceWitness`: it succeeds iff compute succeeds, and then the
observation is the inputs (padded or truncated to the compute arity) and the re-rooted object
witness at the first `witnessSpan` slots. -/
theorem generateSourceWitness_eq_ok [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (artifact : EntryCompilationArtifact F) (inputs oracle : List F) (source : SourceWitness F) :
    generateSourceWitness module artifact inputs oracle = .ok source ↔
      ∃ result, WitnessExecution.genWitness module inputs oracle = .ok result ∧
        source = { inputs := List.ofFn fun i : Fin artifact.computeParams ↦ inputs[i.val]?.getD 0
                   objects := List.ofFn fun i : Fin artifact.witnessSpan ↦
                     result.1 (VarIdEncoding.decode i.val) } := by
  unfold generateSourceWitness
  cases WitnessExecution.genWitness module inputs oracle with
  | error fault => simp [bind, Except.bind]
  | ok result =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, exists_eq_left']
    exact eq_comm

/-- With exactly one value per compute parameter, the generated observation records the
inputs unchanged. -/
theorem generateSourceWitness_inputs [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (artifact : EntryCompilationArtifact F) (inputs oracle : List F) (source : SourceWitness F)
    (hgen : generateSourceWitness module artifact inputs oracle = .ok source)
    (hlen : inputs.length = artifact.computeParams) :
    source.inputs = inputs := by
  obtain ⟨_, -, rfl⟩ := (generateSourceWitness_eq_ok module artifact inputs oracle source).mp hgen
  exact List.ext_getElem (by simp [hlen]) fun i _ _ ↦ by simp [*]

/-- Conditional completeness of witness generation: if the generated observation satisfies the
typed-source semantics, `forward` accepts it and the result is an R1CS instance whose
statement is the public part of the observation.

Proof sketch: generated observations are canonical (`generateSourceWitness_canonical`);
apply `typed_source_forward_total` and `statement_readback`. -/
theorem generated_complete [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F) (entry : Fin (k + 1))
    (compiled : TypedEntryCompilationArtifact module entry) (inputs oracle : List F)
    (source : SourceWitness F)
    (hgen : generateSourceWitness module compiled.artifact inputs oracle = .ok source)
    (hsat : TypedSourceSatisfies module entry source) :
    ∃ z, compiled.artifact.forward source = .ok z ∧
      R1CS.Relation compiled.artifact.target (compiled.artifact.publicPart source) z ∧
      compiled.artifact.readback z = source := by
  obtain ⟨z, hforward, hz, hreadback⟩ := typed_source_forward_total module entry compiled source
    (generateSourceWitness_canonical module compiled.artifact inputs oracle source hgen) hsat
  exact ⟨z, hforward, ⟨hz, by rw [statement_readback, hreadback]⟩, hreadback⟩

/-- Soundness of the prover `proveEntry`: a returned witness comes from a generated
observation that satisfies the typed-source semantics and records `inputs`; the witness is
an R1CS instance for the public part of that observation and reads back to it. -/
theorem proveEntry_sound [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F) (entry : Fin (k + 1))
    (compiled : TypedEntryCompilationArtifact module entry) (inputs oracle : List F)
    (z : R1CS.Witness F) (hprove : proveEntry module entry compiled inputs oracle = .ok z) :
    ∃ source, generateSourceWitness module compiled.artifact inputs oracle = .ok source ∧
      source.inputs = inputs ∧
      SourceRelation module entry compiled (compiled.artifact.publicPart source) source ∧
      R1CS.Relation compiled.artifact.target (compiled.artifact.publicPart source) z ∧
      compiled.artifact.readback z = source := by
  unfold proveEntry at hprove
  cases hgen : generateSourceWitness module compiled.artifact inputs oracle with
  | error e =>
    simp only [hgen, bind, Except.bind, pure, Except.pure] at hprove
    split_ifs at hprove
  | ok source =>
    have key : inputs.length = compiled.artifact.computeParams ∧
        checkTypedSource module entry source = true ∧
        compiled.artifact.forward source = .ok z := by
      simp only [hgen, bind, Except.bind, pure, Except.pure] at hprove
      repeat' first | split_ifs at hprove | split at hprove
      all_goals simp_all
    obtain ⟨hlen, hcheck, hforward⟩ := key
    have hsat := (checkTypedSource_true_iff module entry source).mp hcheck
    have hreadback := typed_pipeline_readback module entry compiled source z hforward
    refine ⟨source, rfl,
      generateSourceWitness_inputs module compiled.artifact inputs oracle source hgen hlen,
      ⟨generateSourceWitness_canonical module compiled.artifact inputs oracle source hgen, hsat,
        rfl⟩,
      ⟨(typed_source_r1cs_iff module entry compiled source z hforward).mp hsat, ?_⟩, hreadback⟩
    rw [statement_readback, hreadback]

/-- Conditional completeness of the prover `proveEntry`: with one value per compute
parameter, an oracle that compute reads completely, and a generated observation that
satisfies the typed-source semantics, the prover succeeds.

Proof sketch: every guard of `proveEntry` passes (`checkTypedSource_true_iff`,
`typed_source_check_eq_artifact`), and `forward` succeeds by `generated_complete`. -/
theorem proveEntry_complete [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F) (entry : Fin (k + 1))
    (compiled : TypedEntryCompilationArtifact module entry) (inputs oracle : List F)
    (source : SourceWitness F)
    (hlen : inputs.length = compiled.artifact.computeParams)
    (hgen : generateSourceWitness module compiled.artifact inputs oracle = .ok source)
    (hused : ∀ w used, WitnessExecution.genWitness module inputs oracle = .ok (w, used) →
      used = oracle.length)
    (hsat : TypedSourceSatisfies module entry source) :
    ∃ z, proveEntry module entry compiled inputs oracle = .ok z ∧
      R1CS.Relation compiled.artifact.target (compiled.artifact.publicPart source) z ∧
      compiled.artifact.readback z = source := by
  obtain ⟨z, hforward, hz, hreadback⟩ :=
    generated_complete module entry compiled inputs oracle source hgen hsat
  have hcheck := (checkTypedSource_true_iff module entry source).mpr hsat
  have hcheck' : checkSource compiled.artifact source = true := by
    rwa [← typed_source_check_eq_artifact module entry compiled source
      (generateSourceWitness_canonical module compiled.artifact inputs oracle source hgen)]
  refine ⟨z, ?_, hz, hreadback⟩
  unfold proveEntry
  cases hexec : WitnessExecution.genWitness module inputs oracle with
  | error _ => simp [hgen, hlen, hcheck, hcheck', hforward, bind, Except.bind, pure, Except.pure]
  | ok r =>
    obtain ⟨w, used⟩ := r
    simp [hgen, hlen, hcheck, hcheck', hforward, hused w used hexec, bind, Except.bind, pure,
      Except.pure]

/-! ## Determinism

A circuit is under-constrained when its constraints admit two different witnesses that agree
on a key, for example on the inputs. `determines_iff` shows that compilation neither adds nor
removes such pairs: the source determines `obs` from `key` iff the R1CS determines
`obs ∘ readback` from `key ∘ readback`. -/

/-- On satisfying canonical source observations, `key` determines `obs`. -/
def SourceDetermines [Field F] [DecidableEq F] {n : Nat} {α β : Type}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F) (entry : Fin n)
    (compiled : TypedEntryCompilationArtifact module entry)
    (key : SourceWitness F → α) (obs : SourceWitness F → β) : Prop :=
  ∀ w₁ w₂, compiled.artifact.CanonicalSource w₁ → TypedSourceSatisfies module entry w₁ →
    compiled.artifact.CanonicalSource w₂ → TypedSourceSatisfies module entry w₂ →
    key w₁ = key w₂ → obs w₁ = obs w₂

/-- On satisfying R1CS assignments of the compiled target, `key` determines `obs`. -/
def TargetDetermines [Field F] {n : Nat} {α β : Type}
    {module : Module LLZK.DialectLowering.WitnessSourceSet n F} {entry : Fin n}
    (compiled : TypedEntryCompilationArtifact module entry)
    (key : R1CS.Witness F → α) (obs : R1CS.Witness F → β) : Prop :=
  ∀ z₁ z₂, R1CS.satisfies z₁ compiled.artifact.target →
    R1CS.satisfies z₂ compiled.artifact.target → key z₁ = key z₂ → obs z₁ = obs z₂

/-- Compilation preserves and reflects determinism of every source observable.

Proof sketch: (→) the readback of a satisfying assignment is a satisfying canonical source
(`typed_source_of_r1cs`, `canonicalSource_readback`). (←) `forward` maps each satisfying
canonical source to a satisfying assignment that reads back to it
(`typed_source_forward_total`). -/
theorem determines_iff [Field F] [DecidableEq F] {n : Nat} {α β : Type}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F) (entry : Fin n)
    (compiled : TypedEntryCompilationArtifact module entry)
    (key : SourceWitness F → α) (obs : SourceWitness F → β) :
    SourceDetermines module entry compiled key obs ↔
      TargetDetermines compiled (key ∘ compiled.artifact.readback)
        (obs ∘ compiled.artifact.readback) := by
  constructor
  · intro h z₁ z₂ h₁ h₂ hkey
    exact h _ _ (compiled.artifact.canonicalSource_readback z₁)
      (typed_source_of_r1cs module entry compiled z₁ h₁)
      (compiled.artifact.canonicalSource_readback z₂)
      (typed_source_of_r1cs module entry compiled z₂ h₂) hkey
  · intro h w₁ w₂ hc₁ hs₁ hc₂ hs₂ hkey
    obtain ⟨z₁, -, hz₁, hr₁⟩ := typed_source_forward_total module entry compiled w₁ hc₁ hs₁
    obtain ⟨z₂, -, hz₂, hr₂⟩ := typed_source_forward_total module entry compiled w₂ hc₂ hs₂
    simpa [hr₁, hr₂] using h z₁ z₂ hz₁ hz₂ (by simpa [hr₁, hr₂] using hkey)

/-- Wire form of `determines_iff` for the full observation: the source inputs determine all
object slots iff, in the R1CS, the input wires determine the object wires. -/
theorem inputs_determine_objects_iff [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F) (entry : Fin n)
    (compiled : TypedEntryCompilationArtifact module entry) :
    SourceDetermines module entry compiled SourceWitness.inputs SourceWitness.objects ↔
      ∀ z₁ z₂, R1CS.satisfies z₁ compiled.artifact.target →
        R1CS.satisfies z₂ compiled.artifact.target →
        (∀ i < compiled.artifact.computeParams,
          z₁ (.var (compiled.artifact.paramOffset + i)) =
            z₂ (.var (compiled.artifact.paramOffset + i))) →
        ∀ j < compiled.artifact.witnessSpan,
          z₁ (.var (compiled.artifact.numParams + j)) =
            z₂ (.var (compiled.artifact.numParams + j)) := by
  rw [determines_iff]
  simp only [TargetDetermines, Function.comp_def, readback_inputs, readback_objects,
    List.ofFn_inj, funext_iff, Fin.forall_iff]

/-! ## The guarantee -/

/-- Properties proved for one successful compilation; see the module documentation. -/
structure CompilerGuarantee [Field F] [DecidableEq F] [Repr F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F) (entry : Fin n)
    (compiled : TypedEntryCompilationArtifact module entry) : Prop where
  /-- Statement wires are distinct and occupy serialized wires `1..k` in order. -/
  statement_wires :
    compiled.artifact.target.statementVars.Nodup ∧
      ∀ i (hi : i < compiled.artifact.target.statementVars.length),
        encode (fromSystem compiled.artifact.target)
            compiled.artifact.target.statementVars[i] = i + 1 ∧
          decode (fromSystem compiled.artifact.target) (i + 1) =
            some compiled.artifact.target.statementVars[i]
  /-- Statement wires carry the public part of the extracted source observation. -/
  statement_fidelity : ∀ z : R1CS.Witness F,
    R1CS.statement compiled.artifact.target z =
      compiled.artifact.publicPart (compiled.artifact.readback z)
  /-- The prover map accepts every source instance and preserves its statement. -/
  completeness : ∀ (x : List F) (w : SourceWitness F),
    SourceRelation module entry compiled x w →
      ∃ z, compiled.artifact.forward w = .ok z ∧
        R1CS.Relation compiled.artifact.target x z ∧ compiled.artifact.readback z = w
  /-- Every R1CS instance extracts to a source instance with the same statement. -/
  soundness : ∀ (x : List F) (z : R1CS.Witness F),
    R1CS.Relation compiled.artifact.target x z →
      SourceRelation module entry compiled x (compiled.artifact.readback z)
  /-- The extractor reads fixed wires. -/
  extractor_reindex : ∀ z : R1CS.Witness F,
    (compiled.artifact.readback z).inputs =
        List.ofFn (fun i : Fin compiled.artifact.computeParams ↦
          z (.var (compiled.artifact.paramOffset + i.val))) ∧
      (compiled.artifact.readback z).objects =
        List.ofFn (fun j : Fin compiled.artifact.witnessSpan ↦
          z (.var (compiled.artifact.numParams + j.val)))
  /-- A statement has a source witness iff it has an R1CS witness. -/
  language : ∀ x : List F,
    (∃ w, SourceRelation module entry compiled x w) ↔
      ∃ z, R1CS.Relation compiled.artifact.target x z
  /-- Compilation preserves and reflects determinism of every source observable. -/
  determinism : ∀ {α β : Type} (key : SourceWitness F → α) (obs : SourceWitness F → β),
    SourceDetermines module entry compiled key obs ↔
      TargetDetermines compiled (key ∘ compiled.artifact.readback)
        (obs ∘ compiled.artifact.readback)

/-- Every successfully compiled entry satisfies `CompilerGuarantee`.

Proof sketch: statement wires use `target_statementVars_nodup` with
`WireAssignment.encode_statement`/`decode_statement` (the layout of `fromSystem` lists the
statement wires first); fidelity is `statement_readback`; completeness is
`typed_source_forward_total` plus fidelity; soundness and language equivalence come from
`entryLevinReduction`; the reindexing holds by definition; determinism is
`determines_iff`. -/
theorem compiler_guarantee [Field F] [DecidableEq F] [Repr F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F) (entry : Fin n)
    (compiled : TypedEntryCompilationArtifact module entry) :
    CompilerGuarantee module entry compiled where
  statement_wires := by
    obtain ⟨hnodup, hone⟩ := target_statementVars_nodup compiled
    exact ⟨hnodup, fun i hi ↦
      ⟨encode_statement (fromSystem compiled.artifact.target) hnodup hone i hi,
        decode_statement (fromSystem compiled.artifact.target) i hi⟩⟩
  statement_fidelity := statement_readback compiled
  completeness x w h := by
    obtain ⟨z, hforward, hsat, hreadback⟩ :=
      typed_source_forward_total module entry compiled w h.1 h.2.1
    exact ⟨z, hforward, ⟨hsat, by rw [statement_readback, hreadback, h.2.2]⟩, hreadback⟩
  soundness x z h := (entryLevinReduction module entry compiled).extraction x z h
  extractor_reindex z := ⟨readback_inputs compiled z, readback_objects compiled z⟩
  language := typed_entry_levin module entry compiled
  determinism key obs := determines_iff module entry compiled key obs

end Dialect.Pipeline
