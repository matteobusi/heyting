/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.ASTToDialect
import Heyting.Dialects.R1CSLikePass
import Heyting.Dialects.CallErasure
import Heyting.Dialects.ObjectCallSemantics
import Heyting.Dialects.StructObjectPass
import Heyting.Dialects.WitnessExecution
import Heyting.Dialects.TypedSourceSemantics
import Heyting.Dialects.OracleErasure

/-!
# Executable dialect-native constraint pipeline

```text
LLZK AST → [Call, StructObject, Oracle, Felt, ConstrainEq]
         → Oracle projection → [Call, StructObject, Felt, ConstrainEq] → Call erasure
         → [StructObject, Felt, ConstrainEq]
         → StructObject erasure → [Felt, ConstrainEq]
         → R1CSLike → R1CS
```

The pipeline retains successful lowering equations in `TypedEntryCompilationArtifact`.
Compute execution produces finite source observations once; transport then materializes
the terminal locals and auxiliary wires.

## Main results

- `typed_source_artifact_iff`: direct typed-source satisfaction agrees with the
  lowering-defined artifact predicate for canonical finite source witnesses.
- `typed_source_r1cs_iff`: successful forwarding preserves and reflects satisfaction
  for the particular source/target witness pair.
- `typed_pipeline_readback`: successful forwarding recovers exact finite observations.

## Proof sketch and scope

Compose the Oracle/Call checker correspondence, the object-erasure simulation,
the leaf materialization equivalence, and the terminal codec equivalence. Layout
equalities in the artifact identify the exact programs and witnesses at each bridge.
Successful forwarding supplies canonical lengths and the checked readback equation.

This is not a whole-entry `PresReflPass`: arbitrary-target reflection and transport
totality are not established here. Parsing, AST lowering, source-generation success,
public-wire classification, and serialization remain outside the theorem.
-/

namespace Dialect.Pipeline

open Dialect

abbrev CallResidual : DialectSet :=
  [StructObject.sig, Felt.sig, ConstrainEq.sig]

/-- Certified selected-entry lowering. Intermediate structural results remain
attached to exact terminal dialect body consumed by backend. -/
structure EntryLoweringArtifact {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n) where
  callErased : List (Stmt CallResidual
    ⟨n, entry.val, (m.structs entry).members.length⟩ F) × LocalVar
  callErasure : CallErasure.eraseConstrainFunc
    (CallErasure.objectFeltConstrainSyntax (F := F)) m entry = some callErased
  callFree : FuncDef CallResidual n entry.val F .constraint
    (m.structs entry).members.length
  callCertification : CallErasure.certifyFunc
    (m.structs entry).constrain callErased.1 = some callFree
  /-- Compute inputs occupy a suffix of the constraint parameters; the remaining prefix
  is the reserved region initialized to zero. Checked by `lowerEntryCertified`. -/
  computeParams_le : (m.structs entry).compute.numParams ≤ callFree.numParams
  objectFree : FuncDef CallPass.TargetSet n entry.val F .constraint
    (m.structs entry).members.length
  objectErasure : StructObjectPass.lowerFunc callFree = some objectFree
  terminal : List (Stmt R1CSLike.Set
    ⟨n, entry.val, (m.structs entry).members.length⟩ F)
  terminal_eq : terminal =
    (R1CSLikePass.dialectPass F).lowerModuleBody objectFree.numParams objectFree.body

namespace EntryLoweringArtifact

/-- Size of the finite object-member witness region required by the expanded body. -/
def witnessSpan {F : Type} [Field F] {n : Nat}
    {m : Module LLZK.DialectLowering.SourceSet n F} {entry : Fin n}
    (artifact : EntryLoweringArtifact m entry) : Nat :=
  StructObjectPass.witnessSpan StructObjectPass.StaticState.initial.objects 0
    artifact.callFree.body

end EntryLoweringArtifact

/-- Execute selected-entry structural and leaf lowering while retaining every
certificate needed by source-facing correctness composition. -/
def lowerEntryCertified {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n) :
    Except String (EntryLoweringArtifact m entry) :=
  match herase : CallErasure.eraseConstrainFunc
      (CallErasure.objectFeltConstrainSyntax (F := F)) m entry with
  | none => .error s!"call erasure failed for entry {(m.structs entry).name}::constrain"
  | some callErased =>
      match hcall : CallErasure.certifyFunc
          (m.structs entry).constrain callErased.1 with
      | none => .error s!"call-erased entry failed certification: \
          {(m.structs entry).name}::constrain"
      | some callFree =>
        if hparams : (m.structs entry).compute.numParams ≤ callFree.numParams then
          match hobject : StructObjectPass.lowerFunc callFree with
          | none => .error s!"StructObject-erased entry failed certification: \
              {(m.structs entry).name}::constrain"
          | some objectFree =>
              let pass := R1CSLikePass.dialectPass F
              let lowered := pass.lowerModuleBody objectFree.numParams objectFree.body
              .ok {
                callErased
                callErasure := herase
                callFree
                callCertification := hcall
                computeParams_le := hparams
                objectFree
                objectErasure := hobject
                terminal := lowered
                terminal_eq := rfl
              }
        else .error s!"compute function has more parameters than constrain function: \
          {(m.structs entry).name}"

/-- Erase calls from the primary object-aware frontend module. -/
noncomputable def eraseCalls {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) :
    Except String (Module CallResidual n F) :=
  match CallErasure.eraseModule (CallErasure.objectFeltConstrainSyntax (F := F)) m with
  | some out => .ok out
  | none => .error "call erasure failed"

/-- Typed frontend plus Call erasure, retaining StructObject operations. -/
noncomputable def eraseCallsAST {F : Type} [Field F] [IntCast F]
    (ast : LLZK.Module) :
    Except String (Σ k, Module CallResidual (k + 1) F) := do
  let ⟨k, m⟩ ← LLZK.DialectLowering.lower (F := F) ast
  pure ⟨k, ← eraseCalls m⟩

/-- Erase StructObject from an already call-free residual module. -/
noncomputable def eraseObjects {F : Type} [Field F] {n : Nat}
    (m : Module CallResidual n F) :
    Except String (Module CallPass.TargetSet n F) :=
  match StructObjectPass.lowerModule m with
  | some out => .ok out
  | none => .error "StructObject erasure failed"

/-- Typed frontend through both structural-prefix erasures. -/
noncomputable def eraseStructuralAST {F : Type} [Field F] [IntCast F]
    (ast : LLZK.Module) :
    Except String (Σ k, Module CallPass.TargetSet (k + 1) F) := do
  let ⟨k, callFree⟩ ← eraseCallsAST (F := F) ast
  pure ⟨k, ← eraseObjects callFree⟩

/-- Compile the constraint function selected as a module entry. -/
def compileEntry {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n) :
    Except String (R1CS.System F) := do
  let lowering ← lowerEntryCertified m entry
  let numPublic := (m.structs entry).members.countP (·.isPublic)
  pure (R1CSLike.enforceZeroPrefix
    (lowering.callFree.numParams - (m.structs entry).compute.numParams)
    (R1CSLike.toR1CS lowering.terminal numPublic))

/-- Finite source observables transported by compilation. Transient locals,
call frames, object paths, allocation counters, and the oracle cursor are not
part of this value. -/
structure SourceWitness (F : Type) where
  inputs : List F
  objects : List F
  deriving Repr, DecidableEq

/-- The exact constraint artifact and constructive codec selected for one
module entry. Every layout decision needed by `forward` is stored beside the
target program that introduced it. -/
structure EntryCompilationArtifact (F : Type) [Field F] where
  terminal : R1CSLike.Program F
  numParams : Nat
  computeParams : Nat
  paramOffset : Nat
  witnessSpan : Nat
  numPublicInputs : Nat
  numPublicInputs_eq : terminal.numPublicInputs = numPublicInputs
  backend : WitnessCodec.CompilationArtifact
    (R1CSLike.Language F) (R1CS.Language F) terminal

namespace EntryCompilationArtifact

/-- Assemble the terminal codec and layout from a certified selected-entry lowering.
The stored public-input count is metadata, not a proof of serializer wire visibility. -/
def ofLowering {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n)
    (lowering : EntryLoweringArtifact m entry) : EntryCompilationArtifact F :=
  let numPublic := (m.structs entry).members.countP (·.isPublic)
  {
    terminal := .mk lowering.terminal numPublic
    numParams := lowering.callFree.numParams
    computeParams := (m.structs entry).compute.numParams
    paramOffset := lowering.callFree.numParams - (m.structs entry).compute.numParams
    witnessSpan := lowering.witnessSpan
    numPublicInputs := numPublic
    numPublicInputs_eq := rfl
    backend := R1CSLike.compilationArtifact (.mk lowering.terminal numPublic)
  }

/-- Exact internal target: backend constraints plus reserved-source initialization. -/
def target {F : Type} [Field F] (artifact : EntryCompilationArtifact F) : R1CS.System F :=
  R1CSLike.enforceZeroPrefix artifact.paramOffset artifact.backend.target

/-- Every satisfying target enforces reserved source initialization, independently
of witness provenance. Proof sketch: project the zero-prefix constraint equivalence. -/
theorem target_reserved_zero {F : Type} [Field F] (artifact : EntryCompilationArtifact F)
    (w : R1CS.Witness F) (h : R1CS.satisfies w artifact.target) :
    ∀ v < artifact.paramOffset, w (.var v) = 0 :=
  ((R1CSLike.satisfies_enforceZeroPrefix_iff _ _ _).mp h).2

/-- Place finite input and object observations in their canonical terminal local slots. -/
def seed {F : Type} [Field F] (artifact : EntryCompilationArtifact F)
    (source : SourceWitness F) : R1CSLike.Witness F :=
  StructObjectPass.seedCanonicalWitness artifact.numParams artifact.witnessSpan
    artifact.paramOffset source.inputs source.objects

/-- Construct ordinary target locals. Equality assertions remain observable;
only malformed canonical lengths and backend-invalid division are failures. -/
def materialize {F : Type} [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) :
    Except String (R1CSLike.Witness F) :=
  if source.inputs.length != artifact.computeParams then
    .error "canonical source witness has the wrong input length"
  else if source.objects.length != artifact.witnessSpan then
    .error "canonical source witness has the wrong object span"
  else match artifact.terminal.materialize (artifact.seed source) with
    | .ok witness => .ok witness
    | .error fault => .error s!"dialect leaf transport: {fault}"

def readback {F : Type} [Field F] (artifact : EntryCompilationArtifact F)
    (target : R1CS.Witness F) : SourceWitness F :=
  let witness := artifact.backend.readback target
  {
    inputs := List.ofFn fun i : Fin artifact.computeParams =>
      witness (artifact.paramOffset + i.val)
    objects := List.ofFn fun i : Fin artifact.witnessSpan =>
      witness (artifact.numParams + i.val)
  }

/-- Compose structural seeding, leaf materialization, and backend auxiliary
construction. A final finite readback check makes successful transport carry
its exact round-trip evidence even for independently constructed artifacts. -/
def forward {F : Type} [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) :
    Except String (R1CS.Witness F) :=
  match artifact.materialize source with
  | .error error => .error error
  | .ok witness =>
    match artifact.backend.forward witness with
    | .error error => .error error
    | .ok target =>
      if artifact.readback target = source ∧
          (List.range artifact.paramOffset).all (fun v ↦ target (.var v) == 0) then .ok target
      else .error "canonical source readback or reserved-zero check failed"

end EntryCompilationArtifact

namespace Source

/-- Artifact-relative satisfaction: materialization succeeds and the resulting
terminal witness satisfies the terminal body. This is not a definition of direct
typed-source semantics; `typed_source_artifact_iff` supplies that correspondence. -/
def satisfies [Field F] [DecidableEq F] (source : SourceWitness F)
    (artifact : EntryCompilationArtifact F) : Prop :=
  ∃ witness, artifact.materialize source = .ok witness ∧
    (R1CSLike.Language F).satisfies witness artifact.terminal

end Source

/-- Direct object-aware satisfaction agrees with artifact-relative satisfaction
under exact lowering and layout equations and canonical input/object lengths.

Proof sketch: specialize the object-to-terminal materialization theorem, then
rewrite the artifact seed and materializer using the recorded layout equalities. -/
theorem source_artifact_iff [Field F] [DecidableEq F]
    {n i numMembers : Nat}
    (fn : FuncDef StructObjectPass.SourceSet n i F .constraint numMembers)
    (objectFree : FuncDef R1CSLikePass.SourceSet n i F .constraint numMembers)
    (hlower : StructObjectPass.lowerFunc fn = some objectFree)
    (computeParams : Nat) (artifact : EntryCompilationArtifact F)
    (source : SourceWitness F)
    (hnumParams : artifact.numParams = fn.numParams)
    (hcomputeParams : artifact.computeParams = computeParams)
    (hparamOffset : artifact.paramOffset = fn.numParams - computeParams)
    (hspan : artifact.witnessSpan = StructObjectPass.witnessSpan
      StructObjectPass.StaticState.initial.objects 0 fn.body)
    (hterminal : artifact.terminal = .mk
      ((R1CSLikePass.dialectPass F).lowerModuleBody objectFree.numParams objectFree.body)
      artifact.numPublicInputs)
    (hinputs : source.inputs.length = computeParams)
    (hobjects : source.objects.length = artifact.witnessSpan) :
    (ObjectResidualSemantics.evalBody fn.body
      (TypedSourceSemantics.initialState fn.numParams computeParams
        source.inputs source.objects)).2 ↔
      Source.satisfies source artifact := by
  have hdirect := R1CSLikePass.source_materialize_iff fn objectFree hlower
    computeParams source.inputs source.objects
  dsimp only at hdirect
  rw [hdirect]
  unfold Source.satisfies
  have hseed : artifact.seed source =
      StructObjectPass.seedCanonicalWitness fn.numParams
        (StructObjectPass.witnessSpan StructObjectPass.StaticState.initial.objects
          0 fn.body)
        (fn.numParams - computeParams) source.inputs source.objects := by
    simp only [EntryCompilationArtifact.seed, hnumParams, hparamOffset, hspan]
  have hinputsArtifact : source.inputs.length = artifact.computeParams :=
    hinputs.trans hcomputeParams.symm
  let terminalBody :=
    (R1CSLikePass.dialectPass F).lowerModuleBody objectFree.numParams objectFree.body
  have hmaterialize : ∀ witness,
      artifact.materialize source = .ok witness ↔
        R1CSLike.materializeBody terminalBody
          (StructObjectPass.seedCanonicalWitness fn.numParams
            (StructObjectPass.witnessSpan
              StructObjectPass.StaticState.initial.objects 0 fn.body)
            (fn.numParams - computeParams) source.inputs source.objects) = .ok witness := by
    intro witness
    have hentry : artifact.materialize source = .ok witness ↔
        artifact.terminal.materialize (artifact.seed source) = .ok witness := by
      have hdef : artifact.materialize source =
          match artifact.terminal.materialize (artifact.seed source) with
          | .ok result => .ok result
          | .error fault => .error s!"dialect leaf transport: {fault}" := by
        simp [EntryCompilationArtifact.materialize, hinputsArtifact, hobjects]
      rw [hdef]
      cases artifact.terminal.materialize (artifact.seed source) <;> simp
    rw [hentry, hterminal]
    change R1CSLike.materializeBody terminalBody (artifact.seed source) = .ok witness ↔ _
    rw [hseed]
  constructor
  · rintro ⟨witness, hwitness, hsatisfies⟩
    refine ⟨witness, (hmaterialize witness).mpr hwitness, ?_⟩
    rw [hterminal]
    exact hsatisfies
  · rintro ⟨witness, hwitness, hsatisfies⟩
    refine ⟨witness, (hmaterialize witness).mp hwitness, ?_⟩
    rw [hterminal] at hsatisfies
    exact hsatisfies

/-- Check finite canonical observables against the original typed module,
before Oracle, Call, or StructObject erasure. -/
def checkTypedSource [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (source : SourceWitness F) : Bool :=
  TypedSourceSemantics.checkAt module entry source.inputs source.objects

def TypedSourceSatisfies [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (source : SourceWitness F) : Prop :=
  TypedSourceSemantics.satisfiesAt module entry source.inputs source.objects

theorem checkTypedSource_true_iff [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (source : SourceWitness F) :
    checkTypedSource module entry source = true ↔
      TypedSourceSatisfies module entry source :=
  TypedSourceSemantics.checkAt_true_iff module entry source.inputs source.objects

/-- Compile an entry and package its exact R1CS target with the codec used to
materialize R1CS auxiliary variables. -/
def compileEntryArtifact {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n) :
    Except String (EntryCompilationArtifact F) := do
  let lowering ← lowerEntryCertified m entry
  pure (EntryCompilationArtifact.ofLowering m entry lowering)

/-- Original typed module bundled with exact Oracle, Call, StructObject, leaf,
and backend compilation evidence for selected entry. -/
structure TypedEntryCompilationArtifact {F : Type} [Field F] {n : Nat}
    (source : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) where
  projected : Module LLZK.DialectLowering.SourceSet n F
  oracleErasure : OracleErasure.lowerModule source = .ok projected
  lowering : EntryLoweringArtifact projected entry

namespace TypedEntryCompilationArtifact

def artifact {F : Type} [Field F] {n : Nat}
    {source : Module LLZK.DialectLowering.WitnessSourceSet n F}
    {entry : Fin n} (compiled : TypedEntryCompilationArtifact source entry) :
    EntryCompilationArtifact F :=
  EntryCompilationArtifact.ofLowering compiled.projected entry compiled.lowering

def prefixCertificate {F : Type} [Field F] {n : Nat}
    {source : Module LLZK.DialectLowering.WitnessSourceSet n F}
    {entry : Fin n} (compiled : TypedEntryCompilationArtifact source entry) :
    ObjectCallSemantics.PrefixCertificate source entry := {
  projected := compiled.projected
  oracleErasure := compiled.oracleErasure
  callFree := compiled.lowering.callErased
  callErasure := compiled.lowering.callErasure
}

end TypedEntryCompilationArtifact

/-- Compile original full typed module while retaining composable correctness
certificates for every structural stage. -/
def compileTypedEntryArtifact {F : Type} [Field F] {n : Nat}
    (source : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) : Except String (TypedEntryCompilationArtifact source entry) :=
  match horacle : OracleErasure.lowerModule source with
  | .error error => .error error
  | .ok projected =>
      match lowerEntryCertified projected entry with
      | .error error => .error error
      | .ok lowering => .ok {
          projected
          oracleErasure := horacle
          lowering
        }

namespace EntryCompilationArtifact

/-- Exact finite source shape accepted by canonical seeding/materialization. -/
def CanonicalSource {F : Type} [Field F] (artifact : EntryCompilationArtifact F)
    (source : SourceWitness F) : Prop :=
  source.inputs.length = artifact.computeParams ∧
    source.objects.length = artifact.witnessSpan

set_option linter.flexible false in
theorem canonicalSource_of_materialize [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (witness : R1CSLike.Witness F)
    (hmaterialize : artifact.materialize source = .ok witness) :
    artifact.CanonicalSource source := by
  unfold CanonicalSource
  by_cases hinputs : source.inputs.length = artifact.computeParams
  · by_cases hobjects : source.objects.length = artifact.witnessSpan
    · exact ⟨hinputs, hobjects⟩
    · simp [materialize, hinputs, hobjects] at hmaterialize
  · simp [materialize, hinputs] at hmaterialize

theorem canonicalSource_of_forward [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (target : R1CS.Witness F) (hforward : artifact.forward source = .ok target) :
    artifact.CanonicalSource source := by
  unfold forward at hforward
  cases hmaterialize : artifact.materialize source with
  | error error => simp [hmaterialize] at hforward
  | ok flat => exact canonicalSource_of_materialize artifact source flat hmaterialize

end EntryCompilationArtifact

/-- Direct typed-source satisfaction agrees with artifact-relative satisfaction
for canonical finite source witnesses and the exact certified compilation artifact.

Proof sketch: use Call certification to identify function fields, the terminal
equation to identify the leaf body, and `source_artifact_iff` for the object/leaf
bridge. Compose with `structuralPrefix_satisfies_iff` for Oracle and Call. -/
theorem typed_source_artifact_iff [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F)
    (hcanonical : compiled.artifact.CanonicalSource source) :
    TypedSourceSatisfies module entry source ↔
      Source.satisfies source compiled.artifact := by
  have hcall := CallErasure.certifyFunc_fields
    (compiled.projected.structs entry).constrain
    compiled.lowering.callErased.1 compiled.lowering.callFree
    compiled.lowering.callCertification
  have hterminal : compiled.artifact.terminal = .mk
      ((R1CSLikePass.dialectPass F).lowerModuleBody
        compiled.lowering.objectFree.numParams compiled.lowering.objectFree.body)
      compiled.artifact.numPublicInputs := by
    change R1CSLike.Program.mk compiled.lowering.terminal _ = _
    rw [compiled.lowering.terminal_eq]
    rfl
  have hobject := source_artifact_iff compiled.lowering.callFree
    compiled.lowering.objectFree compiled.lowering.objectErasure
    (compiled.projected.structs entry).compute.numParams compiled.artifact source
    rfl rfl rfl rfl hterminal hcanonical.1 hcanonical.2
  rw [hcall.1, hcall.2.1] at hobject
  have hprefix := ObjectCallSemantics.structuralPrefix_satisfies_iff
    module entry compiled.prefixCertificate source.inputs source.objects
  exact hprefix.symm.trans hobject

/-- Every satisfying compiled R1CS witness reflects to its finite source readback.

Proof sketch: target constraints force reserved parameters to zero. Terminal
reflection supplies ordinary locals, finite readback establishes the object-layout
relation, and the local object/leaf reflection composes with Oracle/Call simulation.
The witness is arbitrary: no successful forwarding or generation premise occurs. -/
theorem typed_source_of_r1cs [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (target : R1CS.Witness F)
    (hsat : R1CS.satisfies target compiled.artifact.target) :
    TypedSourceSatisfies module entry (compiled.artifact.readback target) := by
  have hz := compiled.artifact.target_reserved_zero target hsat
  have hraw := ((R1CSLike.satisfies_enforceZeroPrefix_iff _ _ _).mp hsat).1
  change R1CS.satisfies target (R1CSLike.toR1CS compiled.lowering.terminal _) at hraw
  have hleaf := R1CSLike.toR1CS_reflection _ target _ hraw
  rw [compiled.lowering.terminal_eq,
    R1CSLikePass.lowerModuleBody_eq_sourceToTargetBody] at hleaf
  have hrel := StructObjectPass.canonicalStateRel_readback
    compiled.lowering.callFree.numParams (compiled.projected.structs entry).compute.numParams
    compiled.lowering.witnessSpan (R1CSLike.readback target) hz
  have hobject := R1CSLikePass.source_of_related_terminal_satisfies
    compiled.lowering.callFree compiled.lowering.objectFree compiled.lowering.objectErasure
    (compiled.projected.structs entry).compute.numParams _ _ _ hrel hleaf
  have hcall := CallErasure.certifyFunc_fields
    (compiled.projected.structs entry).constrain compiled.lowering.callErased.1
    compiled.lowering.callFree compiled.lowering.callCertification
  rw [hcall.1, hcall.2.1] at hobject
  apply (ObjectCallSemantics.structuralPrefix_satisfies_iff module entry
    compiled.prefixCertificate _ _).mp
  simpa [TypedEntryCompilationArtifact.prefixCertificate,
    TypedEntryCompilationArtifact.artifact, EntryCompilationArtifact.readback,
    EntryCompilationArtifact.ofLowering, R1CSLike.compilationArtifact, hcall.1] using hobject

namespace EntryCompilationArtifact

/-- Successful entry materialization is successful terminal materialization of the seed. -/
theorem terminal_materialize_of_materialize [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (witness : R1CSLike.Witness F)
    (hmaterialize : artifact.materialize source = .ok witness) :
    artifact.terminal.materialize (artifact.seed source) = .ok witness := by
  unfold materialize at hmaterialize
  split at hmaterialize
  · simp at hmaterialize
  · split at hmaterialize
    · simp at hmaterialize
    · cases h : artifact.terminal.materialize (artifact.seed source) with
      | error fault => simp [h] at hmaterialize
      | ok result =>
        simp only [h, Except.ok.injEq] at hmaterialize
        rw [hmaterialize]

/-- A terminal witness agreeing with the seed on all allocated slots keeps the reserved
prefix at zero. Proof: reserved slots lie below `numParams`, where the seed is zero. -/
theorem reserved_zero_of_seed [Field F] (artifact : EntryCompilationArtifact F)
    (source : SourceWitness F) (w : R1CSLike.Witness F)
    (hpar : artifact.paramOffset = artifact.numParams - artifact.computeParams)
    (hseed : ∀ v, v < artifact.numParams + artifact.witnessSpan → w v = artifact.seed source v) :
    ∀ v < artifact.paramOffset, w v = 0 := by
  intro v hv
  have hvp : v < artifact.numParams := by omega
  rw [hseed v (by omega)]
  simp [seed, StructObjectPass.seedCanonicalWitness, hvp, hv]

/-- A terminal witness agreeing with the seed on all allocated slots reads back the
canonical source it was seeded from, for canonically sized sources and
`computeParams ≤ numParams`. Proof: compare inputs and objects index by index against the
seed, whose input and object regions are the source lists. -/
theorem readback_compileWitness_of_seed [Field F] (artifact : EntryCompilationArtifact F)
    (source : SourceWitness F) (w : R1CSLike.Witness F)
    (hcanonical : artifact.CanonicalSource source)
    (hle : artifact.computeParams ≤ artifact.numParams)
    (hseed : ∀ v, v < artifact.numParams + artifact.witnessSpan → w v = artifact.seed source v)
    (hpar : artifact.paramOffset = artifact.numParams - artifact.computeParams)
    (hback : ∀ w, artifact.backend.readback (R1CSLike.compileWitness w) = w) :
    artifact.readback (R1CSLike.compileWitness w) = source := by
  obtain ⟨hin, hobj⟩ := hcanonical
  have hread : artifact.readback (R1CSLike.compileWitness w) =
      { inputs := List.ofFn fun i : Fin artifact.computeParams ↦
          w (artifact.paramOffset + i.val)
        objects := List.ofFn fun i : Fin artifact.witnessSpan ↦
          w (artifact.numParams + i.val) } := by
    simp only [readback, hback]
  rw [hread]
  have hoff : artifact.paramOffset + artifact.computeParams = artifact.numParams := by
    omega
  obtain ⟨inputs, objects⟩ := source
  dsimp only [SourceWitness.inputs, SourceWitness.objects] at hin hobj hseed ⊢
  have hinputs : (List.ofFn fun i : Fin artifact.computeParams ↦
      w (artifact.paramOffset + i.val)) = inputs := by
    apply List.ext_getElem (by simp [hin])
    intro i h1 h2
    simp only [List.getElem_ofFn]
    have hp : artifact.paramOffset + i < artifact.numParams := by omega
    rw [hseed _ (by omega)]
    simp [seed, StructObjectPass.seedCanonicalWitness, hp, List.getElem?_eq_getElem h2]
  have hobjects : (List.ofFn fun i : Fin artifact.witnessSpan ↦
      w (artifact.numParams + i.val)) = objects := by
    apply List.ext_getElem (by simp [hobj])
    intro i h1 h2
    simp only [List.getElem_ofFn]
    have hi : i < artifact.witnessSpan := by simpa using h1
    rw [hseed _ (by omega)]
    have hs := StructObjectPass.seedCanonicalWitness_object artifact.numParams
      artifact.witnessSpan artifact.paramOffset inputs objects i hi
    simp only [seed]
    rw [hs, List.getElem?_eq_getElem h2]
    rfl
  rw [hinputs, hobjects]

end EntryCompilationArtifact

/-- Direct typed-source satisfaction yields a materialized leaf witness that keeps every
allocated slot at its seed value and satisfies the terminal program.

Proof sketch: `typed_source_artifact_iff` supplies the witness. Certified SSA keeps every
local below the object function's `numParams = callFree.numParams + span` unchanged. -/
theorem typed_source_materialize [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F)
    (hcanonical : compiled.artifact.CanonicalSource source)
    (hsat : TypedSourceSatisfies module entry source) :
    ∃ w, compiled.artifact.materialize source = .ok w ∧
      (R1CSLike.Language F).satisfies w compiled.artifact.terminal ∧
      ∀ v, v < compiled.artifact.numParams + compiled.artifact.witnessSpan →
        w v = compiled.artifact.seed source v := by
  obtain ⟨w, hmat, hw⟩ := (typed_source_artifact_iff module entry compiled source
    hcanonical).mp hsat
  have hterm := compiled.artifact.terminal_materialize_of_materialize source w hmat
  have hbody : R1CSLike.materializeBody
      (R1CSLikePass.sourceToTargetBody compiled.lowering.objectFree.body)
      (compiled.artifact.seed source) = .ok w := by
    have hE : compiled.artifact.terminal = .mk compiled.lowering.terminal _ := rfl
    rw [hE, compiled.lowering.terminal_eq,
      R1CSLikePass.lowerModuleBody_eq_sourceToTargetBody] at hterm
    exact hterm
  have hpres := R1CSLikePass.materializeBody_preserves_params _ _ _ hbody
  have hnp := (StructObjectPass.lowerFunc_fields compiled.lowering.callFree
    compiled.lowering.objectFree compiled.lowering.objectErasure).1
  exact ⟨w, hmat, hw, fun v hv ↦ hpres v (by rw [hnp]; exact hv)⟩

/-- Whole-entry existential preservation: every canonical finite observation satisfying the
independent typed-source semantics has a satisfying compiled R1CS witness that reads back to
it exactly.

The parameter-layout invariant `computeParams ≤ numParams` (reserved prefix plus compute
inputs) is certified by `lowerEntryCertified`, and is needed for the input readback. Proof
sketch: `typed_source_materialize` gives the leaf witness fixing all allocated slots, so
reserved zeros and finite readback survive. The backend codec then satisfies the base R1CS,
and `satisfies_enforceZeroPrefix_iff` adds the reserved zeros. No forwarding premise is used. -/
theorem typed_source_exists_r1cs [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F)
    (hcanonical : compiled.artifact.CanonicalSource source)
    (hsat : TypedSourceSatisfies module entry source) :
    ∃ target, R1CS.satisfies target compiled.artifact.target ∧
      compiled.artifact.readback target = source := by
  obtain ⟨w, _, hw, hseed⟩ := typed_source_materialize module entry compiled source
    hcanonical hsat
  have hzero := compiled.artifact.reserved_zero_of_seed source w rfl hseed
  refine ⟨R1CSLike.compileWitness w, ?_, ?_⟩
  · rw [EntryCompilationArtifact.target, R1CSLike.satisfies_enforceZeroPrefix_iff]
    exact ⟨(compiled.artifact.backend.satisfies_iff w _ rfl).mp hw, fun v hv ↦ hzero v hv⟩
  · exact compiled.artifact.readback_compileWitness_of_seed source w hcanonical
      compiled.lowering.computeParams_le hseed rfl (fun _ ↦ rfl)

/-- Generate the canonical source-side constraint witness. Compute execution
is modular; structural and leaf projections are delegated to their owning
passes. Constraints are not checked here, so an unsatisfying candidate remains
representable for the general pointwise theorem. -/
def generateSourceWitness {F : Type} [Field F] [DecidableEq F] {k : Nat}
    (fullModule : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (artifact : EntryCompilationArtifact F) (inputs : List F)
    (oracle : List F := []) : Except String (SourceWitness F) := do
  let sourceWitness ← match WitnessExecution.genWitness fullModule inputs oracle with
    | .ok result => pure result.1
    | .error fault => throw s!"dialect compute execution: {fault.message}"
  pure {
    inputs := List.ofFn fun i : Fin artifact.computeParams => inputs[i.val]?.getD 0
    objects := List.ofFn fun i : Fin artifact.witnessSpan =>
      sourceWitness (VarIdEncoding.decode i.val)
  }

set_option linter.flexible false in
theorem generateSourceWitness_canonical [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (artifact : EntryCompilationArtifact F) (inputs oracle : List F)
    (source : SourceWitness F)
    (hgen : generateSourceWitness module artifact inputs oracle = .ok source) :
    artifact.CanonicalSource source := by
  unfold generateSourceWitness at hgen
  cases hexec : WitnessExecution.genWitness module inputs oracle with
  | error fault =>
      simp [hexec, Except.map, Except.instMonad, instMonadExceptOfExcept] at hgen
      dsimp only [instMonadExceptOfExcept, Except.instMonad, Except.bind,
        Except.pure] at hgen
      cases hgen
  | ok result =>
      simp [hexec] at hgen
      dsimp only [Except.instMonad, Except.pure] at hgen
      have hsource := Except.ok.inj hgen
      subst source
      simp [EntryCompilationArtifact.CanonicalSource]

/-- Executable source constraint checker. -/
def checkSource [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) : Bool :=
  match artifact.materialize source with
  | .error _ => false
  | .ok witness => artifact.terminal.check witness

theorem checkSource_true_iff [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) :
    checkSource artifact source = true ↔ Source.satisfies source artifact := by
  unfold checkSource Source.satisfies
  cases hmaterialize : artifact.materialize source with
  | error error => simp
  | ok witness =>
    simpa [hmaterialize] using
      (R1CSLike.Program.check_true_iff artifact.terminal witness)

/-- Executable direct source checker and erased artifact checker agree on every
canonical source witness for a certified whole-entry compilation. -/
theorem typed_source_check_eq_artifact [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F)
    (hcanonical : compiled.artifact.CanonicalSource source) :
    checkTypedSource module entry source = checkSource compiled.artifact source := by
  apply Bool.eq_iff_iff.mpr
  exact (checkTypedSource_true_iff module entry source).trans
    ((typed_source_artifact_iff module entry compiled source hcanonical).trans
      (checkSource_true_iff compiled.artifact source).symm)

theorem generated_typed_source_check_eq_artifact [Field F] [DecidableEq F]
    {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (entry : Fin (k + 1)) (compiled : TypedEntryCompilationArtifact module entry)
    (inputs oracle : List F) (source : SourceWitness F)
    (hgen : generateSourceWitness module compiled.artifact inputs oracle = .ok source) :
    checkTypedSource module entry source = checkSource compiled.artifact source :=
  typed_source_check_eq_artifact module entry compiled source
    (generateSourceWitness_canonical module compiled.artifact inputs oracle source hgen)

/-- Successful forwarding preserves the truth value of artifact satisfaction.

Proof sketch: invert the two successful transport steps and use the backend's
pointwise codec law. This does not quantify over arbitrary target witnesses. -/
theorem pipeline_witness_iff [Field F]
    [DecidableEq F] (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (target : R1CS.Witness F) (hforward : artifact.forward source = .ok target) :
    Source.satisfies source artifact ↔
      R1CS.satisfies target artifact.target := by
  cases hmaterialize : artifact.materialize source with
  | error error =>
    simp [EntryCompilationArtifact.forward, hmaterialize] at hforward
  | ok witness =>
    cases hbackend : artifact.backend.forward witness with
    | error error =>
      simp [EntryCompilationArtifact.forward, hmaterialize, hbackend] at hforward
    | ok compiled =>
      have hforward' :
          (if artifact.readback compiled = source ∧
              (List.range artifact.paramOffset).all (fun v ↦ compiled (.var v) == 0)
            then .ok compiled
            else .error "canonical source readback or reserved-zero check failed") =
            (.ok target : Except String (R1CS.Witness F)) := by
        simpa [EntryCompilationArtifact.forward, hmaterialize, hbackend] using hforward
      split at hforward'
      next hroundtrip =>
        have htarget : compiled = target := Except.ok.inj hforward'
        subst target
        have hcodec := artifact.backend.satisfies_iff witness compiled hbackend
        have hzero : ∀ v < artifact.paramOffset, compiled (.var v) = 0 := by
          simpa using hroundtrip.2
        rw [EntryCompilationArtifact.target, R1CSLike.satisfies_enforceZeroPrefix_iff]
        have hboth : (R1CSLike.Language F).satisfies witness artifact.terminal ↔
            R1CS.satisfies compiled artifact.backend.target ∧
              ∀ v < artifact.paramOffset, compiled (.var v) = 0 :=
          hcodec.trans ⟨fun h ↦ ⟨h, hzero⟩, And.left⟩
        simpa [Source.satisfies, hmaterialize] using hboth
      next => simp at hforward'

/-- Direct typed-source satisfaction iff satisfaction of the exact internal R1CS,
for a successfully forwarded witness pair.

Proof sketch: successful forwarding implies canonical source lengths. Compose
`typed_source_artifact_iff` with `pipeline_witness_iff`. Neither arbitrary-target
reflection nor success of forwarding for all satisfying sources is asserted. -/
theorem typed_source_r1cs_iff [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F) (target : R1CS.Witness F)
    (hforward : compiled.artifact.forward source = .ok target) :
    TypedSourceSatisfies module entry source ↔
      R1CS.satisfies target compiled.artifact.target := by
  have hcanonical := EntryCompilationArtifact.canonicalSource_of_forward
    compiled.artifact source target hforward
  exact (typed_source_artifact_iff module entry compiled source hcanonical).trans
    (pipeline_witness_iff compiled.artifact source target hforward)

/-- Pointwise equivalence for a generated candidate after successful forwarding.

The generation premise records provenance but is not needed by the proof, which
applies `typed_source_r1cs_iff`. In particular, generation alone does not imply
source satisfaction or successful transport. -/
theorem generated_typed_source_r1cs_iff [Field F] [DecidableEq F] {k : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (entry : Fin (k + 1)) (compiled : TypedEntryCompilationArtifact module entry)
    (inputs oracle : List F) (source : SourceWitness F) (target : R1CS.Witness F)
    (_hgen : generateSourceWitness module compiled.artifact inputs oracle = .ok source)
    (hforward : compiled.artifact.forward source = .ok target) :
    TypedSourceSatisfies module entry source ↔
      R1CS.satisfies target compiled.artifact.target :=
  typed_source_r1cs_iff module entry compiled source target hforward

/-- Generated-witness specialization of `pipeline_witness_iff`. Generation is
kept as a premise so candidate production remains distinct from checking. -/
theorem generated_witness_iff [Field F] [DecidableEq F] {k : Nat}
    (fullModule : Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F)
    (artifact : EntryCompilationArtifact F) (inputs oracle : List F)
    (source : SourceWitness F) (target : R1CS.Witness F)
    (_hgen : generateSourceWitness fullModule artifact inputs oracle = .ok source)
    (hforward : artifact.forward source = .ok target) :
    Source.satisfies source artifact ↔
      R1CS.satisfies target artifact.target :=
  pipeline_witness_iff artifact source target hforward

/-- Successful forwarding recovers the exact finite source observation.

Proof sketch: invert forwarding and extract its final readback equality check. -/
theorem pipeline_readback [Field F]
    [DecidableEq F] (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (target : R1CS.Witness F) (hforward : artifact.forward source = .ok target) :
    artifact.readback target = source := by
  cases hmaterialize : artifact.materialize source with
  | error error =>
    simp [EntryCompilationArtifact.forward, hmaterialize] at hforward
  | ok witness =>
    cases hbackend : artifact.backend.forward witness with
    | error error =>
      simp [EntryCompilationArtifact.forward, hmaterialize, hbackend] at hforward
    | ok compiled =>
      have hforward' :
          (if artifact.readback compiled = source ∧
              (List.range artifact.paramOffset).all (fun v ↦ compiled (.var v) == 0)
            then .ok compiled
            else .error "canonical source readback or reserved-zero check failed") =
            (.ok target : Except String (R1CS.Witness F)) := by
        simpa [EntryCompilationArtifact.forward, hmaterialize, hbackend] using hforward
      split at hforward'
      next hroundtrip =>
        have htarget : compiled = target := Except.ok.inj hforward'
        subst target
        exact hroundtrip.1
      next => simp at hforward'

/-- Whole typed-source successful transport preserves exact canonical finite
observables on readback. -/
theorem typed_pipeline_readback [Field F] [DecidableEq F] {n : Nat}
    (module : Module LLZK.DialectLowering.WitnessSourceSet n F)
    (entry : Fin n) (compiled : TypedEntryCompilationArtifact module entry)
    (source : SourceWitness F) (target : R1CS.Witness F)
    (hforward : compiled.artifact.forward source = .ok target) :
    compiled.artifact.readback target = source :=
  pipeline_readback compiled.artifact source target hforward

/-- Generate the R1CS witness corresponding to the dialect-native constraint
artifact. `oracle` supplies `llzk.nondet` values positionally; exhaustion is a
named source-runtime error. -/
def witnessAST {F : Type} [Field F] [DecidableEq F] [IntCast F]
    (ast : LLZK.Module) (inputs : List F) (oracle : List F := []) :
    Except String (R1CS.System F × R1CS.Witness F) := do
  let ⟨k, fullModule⟩ ← LLZK.DialectLowering.lowerFull (F := F) ast
  let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let compiled ← compileTypedEntryArtifact fullModule entry
  let artifact := compiled.artifact
  let sourceWitness ← generateSourceWitness fullModule artifact inputs oracle
  unless checkTypedSource fullModule entry sourceWitness do
    throw "dialect typed-source checker: constraint failed"
  unless checkSource artifact sourceWitness do
    throw "dialect checker mismatch: typed source accepted but erased artifact rejected"
  let targetWitness ← artifact.forward sourceWitness
  pure (artifact.target, targetWitness)

/-- Lower parsed AST and compile last topologically sorted struct as entry circuit. -/
def compileAST {F : Type} [Field F] [IntCast F] (ast : LLZK.Module) :
    Except String (R1CS.System F) := do
  let ⟨k, full⟩ ← LLZK.DialectLowering.lowerFull (F := F) ast
  let entry : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let compiled ← compileTypedEntryArtifact full entry
  pure compiled.artifact.target

end Dialect.Pipeline
