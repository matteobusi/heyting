/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.CallSemantics
import Heyting.Dialects.R1CSLike
import Heyting.Dialects.StructObjectPass

/-!
# Felt/ConstrainEq to R1CS-like dialect

One source operation becomes one target instruction. Consequently destinations,
reads, capabilities, SSA structure, and semantic state threading are preserved
exactly; no fresh locals are allocated.
-/

namespace Dialect.R1CSLikePass

open Dialect

inductive WitnessError where
  | divisionByZero (denominator : LocalVar)
  deriving Repr, DecidableEq

def WitnessError.message : WitnessError → String
  | .divisionByZero v => s!"division by zero at local {v}"

def writeWitness (w : FlatIR.Witness F) (dest : LocalVar) (value : F) :
    FlatIR.Witness F :=
  fun v => if v = dest then value else w v

/-- Materialize one leaf assignment. Equality is deliberately observational:
it remains a constraint and never turns witness transport into failure. -/
def materializeStep [Field F] [DecidableEq F]
    (w : FlatIR.Witness F) (instr : FlatIR.Instr F) :
    Except WitnessError (FlatIR.Witness F) :=
  match instr with
  | .assignAdd dest a b => .ok (writeWitness w dest (w a + w b))
  | .assignSub dest a b => .ok (writeWitness w dest (w a - w b))
  | .assignMul dest a b => .ok (writeWitness w dest (w a * w b))
  | .assignDiv dest a b =>
      if w b = 0 then .error (.divisionByZero b)
      else .ok (writeWitness w dest (w a * (w b)⁻¹))
  | .assignNeg dest a => .ok (writeWitness w dest (-w a))
  | .assignInv dest a => .ok (writeWitness w dest (w a)⁻¹)
  | .assignConst dest c => .ok (writeWitness w dest c)
  | .assertEq _ _ => .ok w

/-- Execute all leaf assignments to produce the exact FlatIR witness consumed
by the backend. Partiality is exactly the backend-invalid division case. -/
def materializeWitness [Field F] [DecidableEq F]
    (program : FlatIR.Program F) (initial : FlatIR.Witness F) :
    Except WitnessError (FlatIR.Witness F) :=
  program.foldlM (materializeStep (F := F)) initial

@[simp] theorem materializeWitness_nil [Field F] [DecidableEq F]
    (initial : FlatIR.Witness F) :
    materializeWitness [] initial = .ok initial := rfl

@[simp] theorem materializeWitness_cons [Field F] [DecidableEq F]
    (instr : FlatIR.Instr F) (rest : FlatIR.Program F)
    (initial : FlatIR.Witness F) :
    materializeWitness (instr :: rest) initial =
      (materializeStep initial instr).bind (materializeWitness rest) := rfl

abbrev SourceSet := CallPass.TargetSet
abbrev TargetSet := R1CSLike.Set

/-! ## Constructive leaf correspondence -/

/-- Direct flattening of object-erasure target syntax. -/
def sourceToFlatInstr {ctx : OpCtx} : Stmt SourceSet ctx F → FlatIR.Instr F
  | .op ⟨0, _⟩ op => R1CSLike.toFlatInstr (.assign op)
  | .op ⟨1, _⟩ op =>
      match op with
      | .eq left right => .assertEq left right

def sourceToFlatProgram {ctx : OpCtx} :
    List (Stmt SourceSet ctx F) → FlatIR.Program F
  | [] => []
  | stmt :: rest => sourceToFlatInstr stmt :: sourceToFlatProgram rest

def evalSourceStmt [Field F] {ctx : OpCtx} :
    Stmt SourceSet ctx F → (LocalVar → F) → (LocalVar → F) × Prop
  | .op ⟨0, _⟩ op, env =>
      (Felt.applyOp op env, Felt.backendValid op env)
  | .op ⟨1, _⟩ op, env =>
      match op with
      | .eq left right => (env, env left = env right)

def evalSourceBody [Field F] {ctx : OpCtx} :
    List (Stmt SourceSet ctx F) → (LocalVar → F) → (LocalVar → F) × Prop
  | [], env => (env, True)
  | stmt :: rest, env =>
      let step := evalSourceStmt stmt env
      let tail := evalSourceBody rest step.1
      (tail.1, step.2 ∧ tail.2)

def Preserves (defined : LocalVar → Bool)
    (before after : LocalVar → F) : Prop :=
  ∀ v, defined v = true → after v = before v

/-- Exact leaf materialization contract. Error means backend-invalid direct
observation; success yields precisely same satisfaction result and preserves
all locals defined before body. -/
def MaterializeSpec [Field F] [DecidableEq F] {ctx : OpCtx}
    (defined : LocalVar → Bool) (body : List (Stmt SourceSet ctx F))
    (initial : LocalVar → F) : Prop :=
  match materializeWitness (sourceToFlatProgram body) initial with
  | .error _ => ¬ (evalSourceBody body initial).2
  | .ok final =>
      (FlatIR.satisfies final (sourceToFlatProgram body) ↔
        (evalSourceBody body initial).2) ∧
      Preserves defined initial final

def FlatBodySpec [Field F] [DecidableEq F]
    (defined : LocalVar → Bool) (program : FlatIR.Program F)
    (initial : LocalVar → F) (truth : Prop) : Prop :=
  match materializeWitness program initial with
  | .error _ => ¬ truth
  | .ok final =>
      (FlatIR.satisfies final program ↔ truth) ∧
      Preserves defined initial final

theorem flat_cons_of_ok [Field F] [DecidableEq F]
    (defined extended : LocalVar → Bool)
    (initial step : LocalVar → F) (instr : FlatIR.Instr F)
    (program : FlatIR.Program F) (headTruth tailTruth : Prop)
    (hstep : materializeStep initial instr = .ok step)
    (htail : FlatBodySpec extended program step tailTruth)
    (hhead : ∀ final, Preserves extended step final →
      (FlatIR.satisfiesInstr final instr ↔ headTruth))
    (hextend : ∀ v, defined v = true → extended v = true)
    (hstepPreserves : Preserves defined initial step) :
    FlatBodySpec defined (instr :: program) initial (headTruth ∧ tailTruth) := by
  unfold FlatBodySpec at htail ⊢
  rw [materializeWitness_cons, hstep]
  simp only [Except.bind]
  cases hmaterialize : materializeWitness program step with
  | error error =>
      rw [hmaterialize] at htail
      change ¬ tailTruth at htail
      change ¬ (headTruth ∧ tailTruth)
      exact fun h => htail h.2
  | ok final =>
      rw [hmaterialize] at htail
      change (FlatIR.satisfies final program ↔ tailTruth) ∧
        Preserves extended step final at htail
      change (FlatIR.satisfies final (instr :: program) ↔
          headTruth ∧ tailTruth) ∧ Preserves defined initial final
      constructor
      · constructor
        · intro hall
          have hheadSat := hall instr (by simp)
          have htailSat : FlatIR.satisfies final program := by
            intro candidate hmem
            exact hall candidate (by simp [hmem])
          exact ⟨(hhead final htail.2).mp hheadSat, htail.1.mp htailSat⟩
        · rintro ⟨hheadTruth, htailTruth⟩ candidate hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact (hhead final htail.2).mpr hheadTruth
          · exact htail.1.mpr htailTruth candidate hmem
      · intro v hv
        exact (htail.2 v (hextend v hv)).trans (hstepPreserves v hv)

theorem flat_cons_of_error [Field F] [DecidableEq F]
    (defined : LocalVar → Bool) (initial : LocalVar → F)
    (instr : FlatIR.Instr F) (program : FlatIR.Program F)
    (headTruth tailTruth : Prop) (error : WitnessError)
    (hstep : materializeStep initial instr = .error error)
    (hfalse : ¬ headTruth) :
    FlatBodySpec defined (instr :: program) initial (headTruth ∧ tailTruth) := by
  unfold FlatBodySpec
  rw [materializeWitness_cons, hstep]
  change ¬ (headTruth ∧ tailTruth)
  exact fun h => hfalse h.1

theorem isSSA_cons_dest_fresh {ctx : OpCtx} {F : Type}
    (defined : LocalVar → Bool) (stmt : Stmt SourceSet ctx F)
    (rest : List (Stmt SourceSet ctx F)) (dest : LocalVar)
    (hssa : isSSA defined (stmt :: rest) = true)
    (hdest : stmt.dest = some dest) : defined dest = false := by
  simp only [isSSA] at hssa
  rw [hdest] at hssa
  simp only [Bool.and_eq_true] at hssa
  simpa using hssa.2.1

theorem felt_head_satisfies_iff [Field F] {ctx : OpCtx}
    (defined : LocalVar → Bool) (op : Felt.Op ctx F)
    (initial final : LocalVar → F)
    (hreads : (Felt.reads op).all defined = true)
    (hfresh : defined (Felt.destVar op) = false)
    (hpreserves : Preserves (fun v => defined v || v == Felt.destVar op)
      (Felt.applyOp op initial) final) :
    FlatIR.satisfiesInstr final (R1CSLike.toFlatInstr (.assign op)) ↔
      Felt.backendValid op initial := by
  have hdest : final (Felt.destVar op) = Felt.evalVal op initial := by
    rw [hpreserves (Felt.destVar op) (by simp), Felt.applyOp_at_dest]
  have hread : ∀ v ∈ Felt.reads op, final v = initial v := by
    intro v hv
    have hvDefined := (List.all_eq_true.mp hreads) v hv
    have hvne : v ≠ Felt.destVar op := by
      intro heq
      subst v
      rw [hfresh] at hvDefined
      contradiction
    rw [hpreserves v (by simp [hvDefined]), Felt.applyOp_at_other op initial v hvne]
  cases op with
  | add dest left right | sub dest left right | mul dest left right =>
      have hd := hdest
      simp only [Felt.destVar, Felt.evalVal] at hd
      simp only [R1CSLike.toFlatInstr, FlatIR.satisfiesInstr, Felt.backendValid]
      rw [hd, hread left (by simp [Felt.reads]),
        hread right (by simp [Felt.reads])]
      simp
  | div dest left right =>
      have hd := hdest
      simp only [Felt.destVar, Felt.evalVal] at hd
      simp only [R1CSLike.toFlatInstr, FlatIR.satisfiesInstr, Felt.backendValid]
      rw [hd, hread left (by simp [Felt.reads]),
        hread right (by simp [Felt.reads])]
      simp [div_eq_mul_inv]
  | neg dest source | inv dest source =>
      have hd := hdest
      simp only [Felt.destVar, Felt.evalVal] at hd
      simp only [R1CSLike.toFlatInstr, FlatIR.satisfiesInstr, Felt.backendValid]
      rw [hd, hread source (by simp [Felt.reads])]
      simp
  | const dest value =>
      have hd : final dest = value := by
        simpa [Felt.destVar, Felt.evalVal] using hdest
      simpa [R1CSLike.toFlatInstr, FlatIR.satisfiesInstr,
        Felt.backendValid] using hd

theorem materialize_spec [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt SourceSet ctx F)) (defined : LocalVar → Bool)
    (initial : LocalVar → F) (hssa : isSSA defined body = true) :
    MaterializeSpec defined body initial := by
  induction body generalizing defined initial with
  | nil =>
      change (FlatIR.satisfies initial [] ↔ True) ∧ Preserves defined initial initial
      exact ⟨by simp [FlatIR.satisfies], fun _ _ => rfl⟩
  | cons stmt rest ih =>
      cases stmt with
      | op d payload =>
        have hparts := CallPass.isSSA_cons_parts defined (.op d payload) rest hssa
        rcases d with ⟨index, hindex⟩
        have hcases : index = 0 ∨ index = 1 := by
          simp [SourceSet, CallPass.TargetSet] at hindex
          omega
        rcases hcases with rfl | rfl
        · have hreads : (Felt.reads payload).all defined = true := by
            simpa [SourceSet, CallPass.TargetSet] using hparts.1
          have hfresh : defined (Felt.destVar payload) = false :=
            isSSA_cons_dest_fresh defined (.op ⟨0, hindex⟩ payload) rest
              (Felt.destVar payload) hssa
              (by simpa [SourceSet, CallPass.TargetSet] using Felt.dest_eq payload)
          have hstmtDest :
              (Stmt.op ⟨0, hindex⟩ payload : Stmt SourceSet ctx F).dest =
                some (Felt.destVar payload) := by
            simpa [SourceSet, CallPass.TargetSet] using Felt.dest_eq payload
          rw [hstmtDest] at hparts
          let extended := fun v => defined v || v == Felt.destVar payload
          let step := Felt.applyOp payload initial
          have htail : FlatBodySpec extended (sourceToFlatProgram rest) step
              (evalSourceBody rest step).2 := by
            simpa [MaterializeSpec] using ih extended step (by
              simpa [extended] using hparts.2)
          have hextend : ∀ v, defined v = true → extended v = true := by
            intro v hv
            simp [extended, hv]
          have hstepPreserves : Preserves defined initial step := by
            intro v hv
            have hvne : v ≠ Felt.destVar payload := by
              intro heq
              subst v
              rw [hfresh] at hv
              contradiction
            simp [step, Felt.applyOp, hvne]
          cases payload with
          | div dest left right =>
              by_cases hzero : initial right = 0
              · have herr : materializeStep initial (.assignDiv dest left right) =
                    .error (.divisionByZero right) := by
                    simp [materializeStep, hzero]
                simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                  sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                  R1CSLike.toFlatInstr, Felt.backendValid, hzero]
                  using flat_cons_of_error defined initial (.assignDiv dest left right)
                    (sourceToFlatProgram rest) (initial right ≠ 0)
                    (evalSourceBody rest step).2
                    (.divisionByZero right) herr (fun hne => hne hzero)
              · have hok : materializeStep initial (.assignDiv dest left right) =
                    .ok step := by
                    simp only [materializeStep, hzero, if_false, Except.ok.injEq]
                    funext v
                    simp [step, writeWitness, Felt.applyOp, Felt.evalVal,
                      Felt.destVar, div_eq_mul_inv]
                simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                  sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                  R1CSLike.toFlatInstr, Felt.backendValid, hzero]
                  using flat_cons_of_ok defined extended initial step
                    (.assignDiv dest left right) (sourceToFlatProgram rest)
                    (initial right ≠ 0)
                    (evalSourceBody rest step).2 hok htail
                    (fun final hpres => felt_head_satisfies_iff defined
                      (.div dest left right) initial final hreads hfresh hpres)
                    hextend hstepPreserves
          | add dest left right =>
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                R1CSLike.toFlatInstr, Felt.backendValid]
                using flat_cons_of_ok defined extended initial step
                  (.assignAdd dest left right) (sourceToFlatProgram rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.add dest left right) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | sub dest left right =>
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                R1CSLike.toFlatInstr, Felt.backendValid]
                using flat_cons_of_ok defined extended initial step
                  (.assignSub dest left right) (sourceToFlatProgram rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.sub dest left right) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | mul dest left right =>
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                R1CSLike.toFlatInstr, Felt.backendValid]
                using flat_cons_of_ok defined extended initial step
                  (.assignMul dest left right) (sourceToFlatProgram rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.mul dest left right) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | neg dest source =>
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                R1CSLike.toFlatInstr, Felt.backendValid]
                using flat_cons_of_ok defined extended initial step
                  (.assignNeg dest source) (sourceToFlatProgram rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.neg dest source) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | inv dest source =>
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                R1CSLike.toFlatInstr, Felt.backendValid]
                using flat_cons_of_ok defined extended initial step
                  (.assignInv dest source) (sourceToFlatProgram rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.inv dest source) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | const dest value =>
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt,
                R1CSLike.toFlatInstr, Felt.backendValid]
                using flat_cons_of_ok defined extended initial step
                  (.assignConst dest value) (sourceToFlatProgram rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.const dest value) initial final hreads hfresh hpres)
                  hextend hstepPreserves
        · cases payload with
          | eq left right =>
              have htailSSA : isSSA defined rest = true := by
                simpa [SourceSet, CallPass.TargetSet] using hparts.2
              have htail : FlatBodySpec defined (sourceToFlatProgram rest) initial
                  (evalSourceBody rest initial).2 := by
                simpa [MaterializeSpec] using ih defined initial htailSSA
              have hhead : ∀ final, Preserves defined initial final →
                  (FlatIR.satisfiesInstr final (.assertEq left right) ↔
                    initial left = initial right) := by
                intro final hpres
                have hleft := hpres left ((List.all_eq_true.mp hparts.1) left (by
                  change left ∈ [left, right]
                  simp))
                have hright := hpres right ((List.all_eq_true.mp hparts.1) right (by
                  change right ∈ [left, right]
                  simp))
                simp [FlatIR.satisfiesInstr, hleft, hright]
              simpa [MaterializeSpec, FlatBodySpec, sourceToFlatProgram,
                sourceToFlatInstr, evalSourceBody, evalSourceStmt]
                using flat_cons_of_ok defined defined initial initial
                  (.assertEq left right) (sourceToFlatProgram rest)
                  (initial left = initial right)
                  (evalSourceBody rest initial).2 rfl htail hhead
                  (fun _ h => h) (fun _ _ => rfl)

theorem evalSourceBody_eq_evalTargetBody [Field F] {ctx : OpCtx}
    (body : List (Stmt SourceSet ctx F)) (env : LocalVar → F) :
    evalSourceBody body env = StructObjectPass.evalTargetBody body env := by
  induction body generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
      cases stmt with
      | op d payload =>
          rcases d with ⟨index, hindex⟩
          have hcases : index = 0 ∨ index = 1 := by
            simp [SourceSet, CallPass.TargetSet] at hindex
            omega
          rcases hcases with rfl | rfl
          · simp only [evalSourceBody, StructObjectPass.evalTargetBody]
            rw [ih]
            rfl
          · cases payload with
            | eq left right =>
                simp only [evalSourceBody, StructObjectPass.evalTargetBody]
                rw [ih]
                rfl

/-- Successful materialization produces a satisfying FlatIR witness exactly
when direct object-erasure target semantics accepts same initial witness. -/
theorem materialize_satisfies_iff [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt SourceSet ctx F)) (defined : LocalVar → Bool)
    (initial : LocalVar → F) (hssa : isSSA defined body = true) :
    (∃ final, materializeWitness (sourceToFlatProgram body) initial = .ok final ∧
        FlatIR.satisfies final (sourceToFlatProgram body)) ↔
      (StructObjectPass.evalTargetBody body initial).2 := by
  rw [← evalSourceBody_eq_evalTargetBody]
  have hspec := materialize_spec body defined initial hssa
  unfold MaterializeSpec at hspec
  cases hmaterialize : materializeWitness (sourceToFlatProgram body) initial with
  | error error =>
      rw [hmaterialize] at hspec
      simp [hspec]
  | ok final =>
      rw [hmaterialize] at hspec
      constructor
      · rintro ⟨candidate, hcandidate, hsatisfies⟩
        cases hcandidate
        exact hspec.1.mp hsatisfies
      · intro htruth
        exact ⟨final, rfl, hspec.1.mpr htruth⟩

/-- Object-aware direct satisfaction equals successful canonical leaf
materialization for every successfully certified StructObject lowering. -/
theorem source_materialize_iff [Field F] [DecidableEq F]
    {n i numMembers : Nat}
    (fn : FuncDef StructObjectPass.SourceSet n i F .constraint numMembers)
    (out : FuncDef SourceSet n i F .constraint numMembers)
    (hlower : StructObjectPass.lowerFunc fn = some out)
    (computeParams : Nat) (inputs objects : List F) :
    let span := StructObjectPass.witnessSpan
      StructObjectPass.StaticState.initial.objects 0 fn.body
    let seed := StructObjectPass.seedCanonicalWitness fn.numParams span
      (fn.numParams - computeParams) inputs objects
    (ObjectResidualSemantics.evalBody fn.body
      (TypedSourceSemantics.initialState fn.numParams computeParams
        inputs objects)).2 ↔
      ∃ final,
        materializeWitness (sourceToFlatProgram out.body) seed = .ok final ∧
        FlatIR.satisfies final (sourceToFlatProgram out.body) := by
  dsimp only
  have hfields := StructObjectPass.lowerFunc_fields fn out hlower
  have hleaf := materialize_satisfies_iff out.body
    (fun v => decide (v < out.numParams))
    (StructObjectPass.seedCanonicalWitness fn.numParams
      (StructObjectPass.witnessSpan StructObjectPass.StaticState.initial.objects
        0 fn.body)
      (fn.numParams - computeParams) inputs objects)
    out.wf_ssa
  rw [hfields.2] at hleaf
  have hobject := StructObjectPass.lowerBody_canonical_iff fn computeParams
    inputs objects
  simpa only [hfields.2] using hobject.symm.trans hleaf.symm

private abbrev feltIx : Fin SourceSet.length := ⟨0, by simp [SourceSet, CallPass.TargetSet]⟩
private abbrev constrIx : Fin SourceSet.length := ⟨1, by simp [SourceSet, CallPass.TargetSet]⟩
private abbrev targetIx : Fin TargetSet.length := ⟨0, by simp [TargetSet, R1CSLike.Set]⟩

private theorem source_ix_cases (d : Fin SourceSet.length) :
    d = feltIx ∨ d = constrIx := by
  rcases d with ⟨d, hd⟩
  have : d = 0 ∨ d = 1 := by
    simp [SourceSet, CallPass.TargetSet] at hd
    omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem target_ix_eq (d : Fin TargetSet.length) : d = targetIx := by
  ext
  exact Nat.lt_one_iff.mp d.isLt

abbrev sourceHandlers (F : Type) [Field F] : HandlerFamily SourceSet F :=
  CallSemantics.targetHandlers F

abbrev targetHandlers (F : Type) [Field F] : HandlerFamily TargetSet F :=
  fun d => by
    have hd : d = targetIx := target_ix_eq d
    subst d
    simpa [TargetSet, R1CSLike.Set, targetIx] using
      (R1CSLike.sem F TargetSet)

@[simp] theorem targetHandlers_targetIx (F : Type) [Field F] :
    targetHandlers F targetIx = R1CSLike.sem F TargetSet := by
  simp [targetHandlers, TargetSet, R1CSLike.Set]

@[simp] theorem sourceHandlers_feltIx (F : Type) [Field F] :
    sourceHandlers F feltIx = Felt.sem F SourceSet := by
  simp [sourceHandlers, CallSemantics.targetHandlers, SourceSet,
    CallPass.TargetSet]

@[simp] theorem sourceHandlers_constrIx (F : Type) [Field F] :
    sourceHandlers F constrIx = ConstrainEq.sem F SourceSet := by
  simp [sourceHandlers, CallSemantics.targetHandlers, SourceSet,
    CallPass.TargetSet]

def lowerOp : ∀ {γ : OpCtx} (d : Fin SourceSet.length),
    (SourceSet.get d).Op γ F → List (Stmt TargetSet γ F) :=
  fun d op =>
    match d, d.isLt with
    | ⟨0, _⟩, _ => [.op targetIx (.assign op)]
    | ⟨1, _⟩, _ =>
      match op with
      | .eq a b => [.op targetIx (.assertEq a b)]

def lowerOpFresh : FreshLowerOp SourceSet TargetSet F :=
  fun next d op => (lowerOp d op, next)

theorem lowerOpFresh_mono : FreshLowerMono (lowerOpFresh (F := F)) := by
  intro γ next d op
  rfl

theorem simple_constrainSim (F : Type) [Field F] :
    SimpleConstrainSim (sourceHandlers F) (lowerOp (F := F))
      (targetHandlers F) := by
  intro n n' γ ctx ctx' d op env
  rcases source_ix_cases d with hd | hd
  · subst d
    cases op <;>
      simp [lowerOp, sourceHandlers, targetHandlers, CallSemantics.targetHandlers,
        R1CSLike.sem, Felt.sem, evalConstrainEnv, evalConstrainBody,
        evalConstrainStep, TargetSet, R1CSLike.Set]
  · subst d
    cases op with
    | eq a b =>
      simp [lowerOp, sourceHandlers, targetHandlers, CallSemantics.targetHandlers,
        R1CSLike.sem, ConstrainEq.sem, evalConstrainEnv, evalConstrainBody,
        evalConstrainStep, TargetSet, R1CSLike.Set]

theorem simple_computeSim (F : Type) [Field F] :
    SimpleComputeSim (sourceHandlers F) (lowerOp (F := F))
      (targetHandlers F) := by
  intro n n' γ ctx ctx' d op env
  rcases source_ix_cases d with hd | hd
  · subst d
    cases op <;>
      simp [lowerOp, sourceHandlers, targetHandlers, CallSemantics.targetHandlers,
        R1CSLike.sem, Felt.sem, evalComputeBody, evalComputeStep,
        TargetSet, R1CSLike.Set]
  · subst d
    cases op with
    | eq a b =>
      simp [lowerOp, sourceHandlers, targetHandlers, CallSemantics.targetHandlers,
        R1CSLike.sem, ConstrainEq.sem, evalComputeBody, evalComputeStep,
        TargetSet, R1CSLike.Set]

theorem fresh_constrainSim (F : Type) [Field F] :
    FreshConstrainSim (sourceHandlers F) (lowerOpFresh (F := F))
      (targetHandlers F) := by
  intro n n' γ ctx ctx' next d op env _
  obtain ⟨henv, hprop⟩ := simple_constrainSim F ctx ctx' d op env
  exact ⟨fun v _ => congrFun henv v, hprop⟩

theorem fresh_computeSim (F : Type) [Field F] :
    FreshComputeSim (sourceHandlers F) (lowerOpFresh (F := F))
      (targetHandlers F) := by
  intro n n' γ ctx ctx' next d op env _
  have h := simple_computeSim F ctx ctx' d op env
  simp only [lowerOpFresh]
  rw [h]
  cases (sourceHandlers F d).computeStep ctx op env <;> simp

def startFresh {γ : OpCtx} (numParams : Nat)
    (body : List (Stmt SourceSet γ F)) : LocalVar :=
  max (maxVarBody body) numParams

theorem startFresh_above {γ : OpCtx} (numParams : Nat)
    (body : List (Stmt SourceSet γ F)) :
    bodyFreshAbove (startFresh numParams body) body :=
  bodyFreshAbove_mono (bodyFreshAbove_maxVarBody body) (Nat.le_max_left _ _)

theorem startFresh_init {γ : OpCtx} (numParams : Nat)
    (body : List (Stmt SourceSet γ F)) (v : LocalVar) :
    startFresh numParams body ≤ v → ¬ v < numParams := by
  intro hv hlt
  exact (Nat.not_lt_of_ge (Nat.le_trans (Nat.le_max_right _ _) hv)) hlt

set_option linter.flexible false in
theorem lowerBodyFresh_caps (k : Capability) {γ : OpCtx} (next : LocalVar)
    (body : List (Stmt SourceSet γ F)) :
    capsLE k (lowerBodyFresh (lowerOpFresh (F := F)) next body).1 =
      capsLE k body := by
  induction body generalizing next with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d op =>
      rcases source_ix_cases d with hd | hd
      · subst d
        cases op <;>
          change (decide (Capability.pure ≤ k) &&
              capsLE k (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) =
            (decide (Capability.pure ≤ k) && capsLE k rest) <;>
          rw [ih]
      · subst d
        cases op
        change (decide (Capability.constraint ≤ k) &&
            capsLE k (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) =
          (decide (Capability.constraint ≤ k) && capsLE k rest)
        rw [ih]

set_option linter.flexible false in
theorem lowerBodyFresh_ssa (init : LocalVar → Bool) {γ : OpCtx}
    (next : LocalVar) (body : List (Stmt SourceSet γ F)) :
    isSSA init (lowerBodyFresh (lowerOpFresh (F := F)) next body).1 =
      isSSA init body := by
  induction body generalizing init next with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d op =>
      rcases source_ix_cases d with hd | hd
      · subst d
        cases op <;> simp [lowerBodyFresh, lowerOpFresh, lowerOp, isSSA,
          Stmt.reads, Stmt.dest, TargetSet, R1CSLike.Set,
          R1CSLike.sig, R1CSLike.reads, R1CSLike.dest, SourceSet,
          CallPass.TargetSet, Felt.sig, Felt.reads, Felt.dest, ih]
      · subst d
        cases op
        simp [lowerBodyFresh, lowerOpFresh, lowerOp, isSSA, Stmt.reads,
          Stmt.dest, TargetSet, R1CSLike.Set, R1CSLike.sig,
          R1CSLike.reads, R1CSLike.dest, SourceSet, CallPass.TargetSet,
          ConstrainEq.sig, ConstrainEq.reads, ConstrainEq.dest, ih]

/-- R1CS-like dialect packaging erases to same FlatIR program as direct leaf
adapter. Fresh counter is unchanged and therefore absent from result. -/
theorem lowerBodyFresh_toFlatProgram {γ : OpCtx} (next : LocalVar)
    (body : List (Stmt SourceSet γ F)) :
    R1CSLike.toFlatProgram
        (lowerBodyFresh (lowerOpFresh (F := F)) next body).1 =
      sourceToFlatProgram body := by
  induction body generalizing next with
  | nil => rfl
  | cons stmt rest ih =>
      cases stmt with
      | op d op =>
          rcases source_ix_cases d with hd | hd
          · subst d
            cases op <;>
              simp [lowerBodyFresh, lowerOpFresh, lowerOp,
                R1CSLike.toFlatProgram, sourceToFlatProgram, sourceToFlatInstr, ih]
          · subst d
            cases op
            simp [lowerBodyFresh, lowerOpFresh, lowerOp,
              R1CSLike.toFlatProgram, R1CSLike.toFlatInstr,
              sourceToFlatProgram, sourceToFlatInstr, ih]

/-- Unified composable pass for Phase 7's dialect boundary. -/
def dialectPass (F : Type) [Field F] : DialectPass SourceSet TargetSet F where
  handlers := sourceHandlers F
  handlers' := targetHandlers F
  lowerOp := lowerOpFresh
  next_mono := lowerOpFresh_mono
  constrain := fresh_constrainSim F
  compute := fresh_computeSim F
  startFresh := startFresh
  startFresh_above := startFresh_above
  startFresh_init := startFresh_init
  lower_caps := by
    intro γ k numParams body h
    rw [lowerBodyFresh_caps]
    exact h
  lower_ssa := by
    intro γ init next body _ _ h
    rw [lowerBodyFresh_ssa]
    exact h

/-- Total module-level constraint wrapper, ready to compose after call erasure. -/
def moduleConstraintPass (F : Type) [Field F] :
    ModuleConstraintPass SourceSet TargetSet F :=
  ModuleConstraintPass.ofDialectPass (dialectPass F)

/-- Phase-6 call erasure followed by the Phase-7 instruction lowering. -/
noncomputable def callToR1CSLike (F : Type) [Field F] :
    CallSemantics.CallModuleConstraintPass TargetSet F :=
  CallSemantics.CallModuleConstraintPass.compose
    (CallSemantics.moduleConstraintPass (F := F))
    (moduleConstraintPass F) rfl

/-- Compile one lowered module entry's constraint body with the verified legacy
FlatIR-to-R1CS backend. -/
def compileEntryConstrain (F : Type) [Field F] {n : Nat}
    (m : Module TargetSet n F) (entry : Fin n) : R1CS.System F :=
  R1CSLike.toR1CS (m.structs entry).constrain.body
    (m.structs entry).members.length

end Dialect.R1CSLikePass
