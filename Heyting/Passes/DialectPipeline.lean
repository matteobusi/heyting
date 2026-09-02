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
import Heyting.Passes.FlatIRToR1CS
import Heyting.Passes.FlatIRWitnessCodec
import Heyting.Languages.FlatIRChecked

/-!
# Executable dialect-native constraint pipeline

```text
LLZK AST → [Call, StructObject, Felt, ConstrainEq] → call erasure
         → [StructObject, Felt, ConstrainEq]
         → StructObject erasure → [Felt, ConstrainEq]
         → R1CSLike → R1CS
```

The pipeline exposes failure from the still-partial call erasure boundary.
Compute-side execution uses the typed witness source set, then materializes the
same object-erased locals consumed by the constraint backend.
-/

namespace Dialect.Pipeline

open Dialect

abbrev CallResidual : DialectSet :=
  [StructObject.sig, Felt.sig, ConstrainEq.sig]

/-- Certified selected-entry lowering. Intermediate structural results remain
attached to exact FlatIR program consumed by backend. -/
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
  objectFree : FuncDef CallPass.TargetSet n entry.val F .constraint
    (m.structs entry).members.length
  objectErasure : StructObjectPass.lowerFunc callFree = some objectFree
  program : FlatIR.Program F
  program_eq : program = R1CSLikePass.sourceToFlatProgram objectFree.body

namespace EntryLoweringArtifact

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
          match hobject : StructObjectPass.lowerFunc callFree with
          | none => .error s!"StructObject-erased entry failed certification: \
              {(m.structs entry).name}::constrain"
          | some objectFree =>
              let pass := R1CSLikePass.dialectPass F
              let lowered := pass.lowerModuleBody objectFree.numParams objectFree.body
              let program := R1CSLike.toFlatProgram lowered
              .ok {
                callErased
                callErasure := herase
                callFree
                callCertification := hcall
                objectFree
                objectErasure := hobject
                program
                program_eq := by
                  simpa [program, lowered, pass, DialectPass.lowerModuleBody,
                    DialectPass.lowerBody, R1CSLikePass.dialectPass] using
                    (R1CSLikePass.lowerBodyFresh_toFlatProgram (F := F)
                      ((R1CSLikePass.dialectPass F).startFresh
                        objectFree.numParams objectFree.body) objectFree.body)
              }

/-- Erase calls from the primary object-aware frontend module. -/
noncomputable def eraseCalls {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) :
    Except String (Module CallResidual n F) :=
  match CallErasure.eraseModule (CallErasure.objectFeltConstrainSyntax (F := F)) m with
  | some out => .ok out
  | none => .error "call erasure failed"

/-- Typed frontend plus call erasure.  This is the Phase-11 executable
boundary, including programs that still contain StructObject operations. -/
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

/-- Lower the selected constraint function to the exact FlatIR program consumed
by the R1CS backend. The returned naturals are the original parameter count and
the inserted encoded-witness span. -/
def lowerEntryProgram {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n) :
    Except String (FlatIR.Program F × Nat × Nat) := do
  let lowering ← lowerEntryCertified m entry
  pure (lowering.program, lowering.callFree.numParams, lowering.witnessSpan)

/-- Compile the constraint function selected as a module entry. -/
def compileEntry {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n) :
    Except String (R1CS.System F) := do
  let ⟨program, _, _⟩ ← lowerEntryProgram m entry
  let numPublic := (m.structs entry).members.countP (·.isPublic)
  pure (FlatIRToR1CS.compileProgram F program numPublic)

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
  program : FlatIR.Program F
  numParams : Nat
  computeParams : Nat
  paramOffset : Nat
  witnessSpan : Nat
  numPublicInputs : Nat
  backend : WitnessCodec.CompilationArtifact
    (FlatIR.Language F) (R1CS.Language F) program

namespace EntryCompilationArtifact

def ofLowering {F : Type} [Field F] {n : Nat}
    (m : Module LLZK.DialectLowering.SourceSet n F) (entry : Fin n)
    (lowering : EntryLoweringArtifact m entry) : EntryCompilationArtifact F :=
  let numPublic := (m.structs entry).members.countP (·.isPublic)
  {
    program := lowering.program
    numParams := lowering.callFree.numParams
    computeParams := (m.structs entry).compute.numParams
    paramOffset := lowering.callFree.numParams - (m.structs entry).compute.numParams
    witnessSpan := lowering.witnessSpan
    numPublicInputs := numPublic
    backend := FlatIRToR1CS.compilationArtifact F lowering.program numPublic
  }

def target {F : Type} [Field F] (artifact : EntryCompilationArtifact F) : R1CS.System F :=
  artifact.backend.target

def seed {F : Type} [Field F] (artifact : EntryCompilationArtifact F)
    (source : SourceWitness F) : FlatIR.Witness F :=
  StructObjectPass.seedCanonicalWitness artifact.numParams artifact.witnessSpan
    artifact.paramOffset source.inputs source.objects

/-- Construct ordinary target locals. Equality assertions remain observable;
only malformed canonical lengths and backend-invalid division are failures. -/
def materialize {F : Type} [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) :
    Except String (FlatIR.Witness F) := do
  if source.inputs.length != artifact.computeParams then
    throw "canonical source witness has the wrong input length"
  if source.objects.length != artifact.witnessSpan then
    throw "canonical source witness has the wrong object span"
  match R1CSLikePass.materializeWitness artifact.program (artifact.seed source) with
  | .ok witness => pure witness
  | .error fault => throw s!"dialect leaf transport: {fault.message}"

def readback {F : Type} [Field F] (artifact : EntryCompilationArtifact F)
    (target : R1CS.Witness F) : SourceWitness F :=
  let flat := artifact.backend.readback target
  {
    inputs := List.ofFn fun i : Fin artifact.computeParams =>
      flat (artifact.paramOffset + i.val)
    objects := List.ofFn fun i : Fin artifact.witnessSpan =>
      flat (artifact.numParams + i.val)
  }

/-- Compose structural seeding, leaf materialization, and backend auxiliary
construction. A final finite readback check makes successful transport carry
its exact round-trip evidence even for independently constructed artifacts. -/
def forward {F : Type} [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) :
    Except String (R1CS.Witness F) :=
  match artifact.materialize source with
  | .error error => .error error
  | .ok flat =>
    match artifact.backend.forward flat with
    | .error error => .error error
    | .ok target =>
      if artifact.readback target = source then .ok target
      else .error "canonical source witness was overwritten during transport"

end EntryCompilationArtifact

namespace Source

def satisfies [Field F] [DecidableEq F] (source : SourceWitness F)
    (artifact : EntryCompilationArtifact F) : Prop :=
  ∃ flat, artifact.materialize source = .ok flat ∧
    FlatIR.satisfies flat artifact.program

end Source

/-- Phase-14C boundary: direct object-aware constraint satisfaction equals
Phase-13 artifact satisfaction whenever artifact records exact certified
StructObject lowering and canonical finite layout. -/
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
    (hprogram : artifact.program =
      R1CSLikePass.sourceToFlatProgram objectFree.body)
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
  have hmaterialize : ∀ flat,
      artifact.materialize source = .ok flat ↔
        R1CSLikePass.materializeWitness
          (R1CSLikePass.sourceToFlatProgram objectFree.body)
          (StructObjectPass.seedCanonicalWitness fn.numParams
            (StructObjectPass.witnessSpan
              StructObjectPass.StaticState.initial.objects 0 fn.body)
            (fn.numParams - computeParams) source.inputs source.objects) = .ok flat := by
    intro flat
    unfold EntryCompilationArtifact.materialize
    simp only [hinputsArtifact, hobjects, bne_self_eq_false, hprogram, hseed]
    cases R1CSLikePass.materializeWitness
        (R1CSLikePass.sourceToFlatProgram objectFree.body)
        (StructObjectPass.seedCanonicalWitness fn.numParams
          (StructObjectPass.witnessSpan
            StructObjectPass.StaticState.initial.objects 0 fn.body)
          (fn.numParams - computeParams) source.inputs source.objects) with
    | error fault =>
        simp only [Bool.false_eq_true, if_false]
        dsimp only [Except.instMonad, Except.pure, Except.bind,
          instMonadExceptOfExcept]
        constructor <;> intro h <;> cases h
    | ok witness =>
        simp only [Bool.false_eq_true, if_false]
        dsimp only [Except.instMonad, Except.pure, Except.bind]
        simp
  constructor
  · rintro ⟨flat, hflat, hsatisfies⟩
    exact ⟨flat, (hmaterialize flat).mpr hflat, by simpa [hprogram] using hsatisfies⟩
  · rintro ⟨flat, hflat, hsatisfies⟩
    exact ⟨flat, (hmaterialize flat).mp hflat, by simpa [hprogram] using hsatisfies⟩

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
    (flat : FlatIR.Witness F) (hmaterialize : artifact.materialize source = .ok flat) :
    artifact.CanonicalSource source := by
  unfold CanonicalSource
  by_cases hinputs : source.inputs.length = artifact.computeParams
  · by_cases hobjects : source.objects.length = artifact.witnessSpan
    · exact ⟨hinputs, hobjects⟩
    · simp [materialize, hinputs, hobjects] at hmaterialize
      dsimp only [Except.instMonad, Except.pure, Except.bind,
        instMonadExceptOfExcept] at hmaterialize
      cases hmaterialize
  · simp [materialize, hinputs] at hmaterialize
    dsimp only [Except.instMonad, Except.pure, Except.bind,
      instMonadExceptOfExcept] at hmaterialize
    cases hmaterialize

theorem canonicalSource_of_forward [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (target : R1CS.Witness F) (hforward : artifact.forward source = .ok target) :
    artifact.CanonicalSource source := by
  unfold forward at hforward
  cases hmaterialize : artifact.materialize source with
  | error error => simp [hmaterialize] at hforward
  | ok flat => exact canonicalSource_of_materialize artifact source flat hmaterialize

end EntryCompilationArtifact

/-- Whole typed-source observation equals canonical artifact observation by
ordinary composition of Oracle, Call, StructObject, and leaf certificates. -/
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
  have hobject := source_artifact_iff compiled.lowering.callFree
    compiled.lowering.objectFree compiled.lowering.objectErasure
    (compiled.projected.structs entry).compute.numParams compiled.artifact source
    rfl rfl rfl rfl compiled.lowering.program_eq hcanonical.1 hcanonical.2
  rw [hcall.1, hcall.2.1] at hobject
  have hprefix := ObjectCallSemantics.structuralPrefix_satisfies_iff
    module entry compiled.prefixCertificate source.inputs source.objects
  exact hprefix.symm.trans hobject

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
  | .ok flat => FlatIRChecked.checkProgram flat artifact.program

theorem checkSource_true_iff [Field F] [DecidableEq F]
    (artifact : EntryCompilationArtifact F) (source : SourceWitness F) :
    checkSource artifact source = true ↔ Source.satisfies source artifact := by
  unfold checkSource Source.satisfies
  cases hmaterialize : artifact.materialize source with
  | error error => simp
  | ok flat =>
    simpa [hmaterialize] using
      (FlatIRChecked.checkProgram_true_iff_satisfies flat artifact.program)

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

/-- Whole executable constraint-pipeline pointwise correctness. -/
theorem pipeline_witness_iff [Field F]
    [DecidableEq F] (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (target : R1CS.Witness F) (hforward : artifact.forward source = .ok target) :
    Source.satisfies source artifact ↔
      R1CS.satisfies target artifact.target := by
  cases hmaterialize : artifact.materialize source with
  | error error =>
    simp [EntryCompilationArtifact.forward, hmaterialize] at hforward
  | ok flat =>
    cases hbackend : artifact.backend.forward flat with
    | error error =>
      simp [EntryCompilationArtifact.forward, hmaterialize, hbackend] at hforward
    | ok compiled =>
      have hforward' :
          (if artifact.readback compiled = source then .ok compiled
            else .error "canonical source witness was overwritten during transport") =
            (.ok target : Except String (R1CS.Witness F)) := by
        simpa [EntryCompilationArtifact.forward, hmaterialize, hbackend] using hforward
      split at hforward'
      next hroundtrip =>
        have htarget : compiled = target := Except.ok.inj hforward'
        subst target
        simpa [Source.satisfies, hmaterialize] using
          (artifact.backend.satisfies_iff flat compiled hbackend)
      next => simp at hforward'

/-- Final pointwise compiler theorem from original typed module to exact R1CS
stored in successful whole-entry compilation artifact. -/
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

/-- Generated-source specialization of whole typed-source correctness. -/
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

theorem pipeline_readback [Field F]
    [DecidableEq F] (artifact : EntryCompilationArtifact F) (source : SourceWitness F)
    (target : R1CS.Witness F) (hforward : artifact.forward source = .ok target) :
    artifact.readback target = source := by
  cases hmaterialize : artifact.materialize source with
  | error error =>
    simp [EntryCompilationArtifact.forward, hmaterialize] at hforward
  | ok flat =>
    cases hbackend : artifact.backend.forward flat with
    | error error =>
      simp [EntryCompilationArtifact.forward, hmaterialize, hbackend] at hforward
    | ok compiled =>
      have hforward' :
          (if artifact.readback compiled = source then .ok compiled
            else .error "canonical source witness was overwritten during transport") =
            (.ok target : Except String (R1CS.Witness F)) := by
        simpa [EntryCompilationArtifact.forward, hmaterialize, hbackend] using hforward
      split at hforward'
      next hroundtrip =>
        have htarget : compiled = target := Except.ok.inj hforward'
        subst target
        exact hroundtrip
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
