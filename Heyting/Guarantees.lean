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

## What the guarantee does not cover

* The parser and the AST-to-dialect frontend: the guarantee starts at the typed module.
* The bytes of `.r1cs`/`.wtns` files: only the wire layout is proved.
* Cryptographic properties of a proof system Π. Items 1–4 make the compilation a Levin
  reduction (`entryLevinReduction`) with the identity statement map, so for a Π that is
  knowledge-sound and zero-knowledge for the R1CS relation, "compile, then Π" is
  knowledge-sound (extractor `A.readback ∘ E_Π`) and zero-knowledge (simulator `S_Π`) for
  `SourceRelation`. That transfer argument is standard but not formalized here.
* Witness generation: the source witness passed to `forward` is not proved to come from the
  upstream compute semantics.
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

/-- Every successfully compiled entry satisfies `CompilerGuarantee`.

Proof sketch: statement wires use `target_statementVars_nodup` with
`WireAssignment.encode_statement`/`decode_statement` (the layout of `fromSystem` lists the
statement wires first); fidelity is `statement_readback`; completeness is
`typed_source_forward_total` plus fidelity; soundness and language equivalence come from
`entryLevinReduction`; the reindexing holds by definition. -/
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

end Dialect.Pipeline
