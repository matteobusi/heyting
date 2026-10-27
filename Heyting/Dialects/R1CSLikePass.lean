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

## Main results and proof sketch

`dialectPass` proves handler-level equivalence by case analysis on source operations.
`materialize_spec` and `materialize_satisfies_iff` relate sequential evaluation to
a fixed terminal witness: SSA ensures later assignments cannot change earlier reads
or destinations. `source_materialize_iff` combines this argument with certified
object erasure and identifies the exact terminal body via `lowerModuleBody_eq_sourceToTargetBody`.

The handler interpretation and terminal fixed-witness satisfaction are distinct.
In particular, division validity is explicit in `evalSourceStmt` and materialization;
the generic handler equivalence alone is not the entire R1CS correctness argument.
-/

namespace Dialect.R1CSLikePass

open Dialect

abbrev SourceSet := CallPass.TargetSet
abbrev TargetSet := R1CSLike.Set

/-- Package object-erasure target syntax in terminal R1CSLike dialect. -/
def sourceToTargetStmt {ctx : OpCtx} :
    Stmt SourceSet ctx F → Stmt TargetSet ctx F
  | .op ⟨0, _⟩ op => .op R1CSLike.ix (.assign op)
  | .op ⟨1, _⟩ op =>
      match op with
      | .eq left right => .op R1CSLike.ix (.assertEq left right)

def sourceToTargetBody {ctx : OpCtx} :
    List (Stmt SourceSet ctx F) → List (Stmt TargetSet ctx F)
  | [] => []
  | stmt :: rest => sourceToTargetStmt stmt :: sourceToTargetBody rest

/-- The object-erasure target and terminal-lowering source share one statement semantics. -/
abbrev evalSourceStmt [Field F] {ctx : OpCtx} :=
  StructObjectPass.evalTargetStmt (F := F) (ctx := ctx)

/-- The object-erasure target and terminal-lowering source share one body semantics.
This includes backend division validity, unlike the generic field-local handler. -/
abbrev evalSourceBody [Field F] {ctx : OpCtx} :=
  StructObjectPass.evalTargetBody (F := F) (ctx := ctx)

def Preserves (defined : LocalVar → Bool)
    (before after : LocalVar → F) : Prop :=
  ∀ v, defined v = true → after v = before v

/-- Exact direct leaf materialization contract. -/
def MaterializeSpec [Field F] [DecidableEq F] {ctx : OpCtx}
    (defined : LocalVar → Bool) (body : List (Stmt SourceSet ctx F))
    (initial : LocalVar → F) : Prop :=
  match R1CSLike.materializeBody (sourceToTargetBody body) initial with
  | .error _ => ¬ (evalSourceBody body initial).2
  | .ok final =>
      (R1CSLike.satisfies final (sourceToTargetBody body) ↔
        (evalSourceBody body initial).2) ∧
      Preserves defined initial final

def TargetBodySpec [Field F] [DecidableEq F] {ctx : OpCtx}
    (defined : LocalVar → Bool) (body : List (Stmt TargetSet ctx F))
    (initial : LocalVar → F) (truth : Prop) : Prop :=
  match R1CSLike.materializeBody body initial with
  | .error _ => ¬ truth
  | .ok final =>
      (R1CSLike.satisfies final body ↔ truth) ∧
      Preserves defined initial final

theorem target_cons_of_ok [Field F] [DecidableEq F] {ctx : OpCtx}
    (defined extended : LocalVar → Bool)
    (initial step : LocalVar → F) (op : R1CSLike.Op ctx F)
    (body : List (Stmt TargetSet ctx F)) (headTruth tailTruth : Prop)
    (hstep : R1CSLike.materializeOp initial op = .ok step)
    (htail : TargetBodySpec extended body step tailTruth)
    (hhead : ∀ final, Preserves extended step final →
      (R1CSLike.satisfiesOp final op ↔ headTruth))
    (hextend : ∀ v, defined v = true → extended v = true)
    (hstepPreserves : Preserves defined initial step) :
    TargetBodySpec defined (.op R1CSLike.ix op :: body) initial
      (headTruth ∧ tailTruth) := by
  unfold TargetBodySpec at htail ⊢
  rw [R1CSLike.materializeBody, R1CSLike.stmtOp_op, hstep]
  dsimp only [Except.instMonad, Except.bind]
  cases hmaterialize : R1CSLike.materializeBody body step with
  | error error =>
      rw [hmaterialize] at htail
      change ¬ tailTruth at htail
      change ¬ (headTruth ∧ tailTruth)
      exact fun h => htail h.2
  | ok final =>
      rw [hmaterialize] at htail
      change (R1CSLike.satisfies final body ↔ tailTruth) ∧
        Preserves extended step final at htail
      change (R1CSLike.satisfies final (.op R1CSLike.ix op :: body) ↔
          headTruth ∧ tailTruth) ∧ Preserves defined initial final
      constructor
      · simp only [R1CSLike.satisfies, List.forall_mem_cons]
        exact and_congr (hhead final htail.2) htail.1
      · intro v hv
        exact (htail.2 v (hextend v hv)).trans (hstepPreserves v hv)

theorem target_cons_of_error [Field F] [DecidableEq F] {ctx : OpCtx}
    (defined : LocalVar → Bool) (initial : LocalVar → F)
    (op : R1CSLike.Op ctx F) (body : List (Stmt TargetSet ctx F))
    (headTruth tailTruth : Prop) (error : String)
    (hstep : R1CSLike.materializeOp initial op = .error error)
    (hfalse : ¬ headTruth) :
    TargetBodySpec defined (.op R1CSLike.ix op :: body) initial
      (headTruth ∧ tailTruth) := by
  unfold TargetBodySpec
  rw [R1CSLike.materializeBody, R1CSLike.stmtOp_op, hstep]
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
    R1CSLike.satisfiesOp final (.assign op) ↔
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
      simp only [R1CSLike.satisfiesOp, Felt.backendValid]
      rw [hd, hread left (by simp [Felt.reads]),
        hread right (by simp [Felt.reads])]
      simp
  | div dest left right =>
      have hd := hdest
      simp only [Felt.destVar, Felt.evalVal] at hd
      simp only [R1CSLike.satisfiesOp, Felt.backendValid]
      rw [hd, hread left (by simp [Felt.reads]),
        hread right (by simp [Felt.reads])]
      simp [div_eq_mul_inv]
  | neg dest source | inv dest source =>
      have hd := hdest
      simp only [Felt.destVar, Felt.evalVal] at hd
      simp only [R1CSLike.satisfiesOp, Felt.backendValid]
      rw [hd, hread source (by simp [Felt.reads])]
      simp
  | const dest value =>
      have hd : final dest = value := by
        simpa [Felt.destVar, Felt.evalVal] using hdest
      simpa [R1CSLike.satisfiesOp, Felt.backendValid] using hd

/-- SSA body materialization satisfies `MaterializeSpec`: successful execution
relates terminal satisfaction to source evaluation and preserves initially defined locals.

Proof sketch: induct on the body and extend the defined-local predicate at assignments.
SSA freshness and read validity let the tail preserve the head equation. Division by
zero follows the fault branch rather than producing a satisfying terminal equation. -/
theorem materialize_spec [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt SourceSet ctx F)) (defined : LocalVar → Bool)
    (initial : LocalVar → F) (hssa : isSSA defined body = true) :
    MaterializeSpec defined body initial := by
  induction body generalizing defined initial with
  | nil =>
      change (R1CSLike.satisfies initial [] ↔ True) ∧
        Preserves defined initial initial
      exact ⟨by simp [R1CSLike.satisfies], fun _ _ => rfl⟩
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
          have htail : TargetBodySpec extended (sourceToTargetBody rest) step
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
              · have herr : R1CSLike.materializeOp initial
                    (.assign (.div dest left right) : R1CSLike.Op ctx F) =
                    .error s!"division by zero at local {right}" := by
                    simp [R1CSLike.materializeOp, hzero]
                simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                  sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                  Felt.backendValid, hzero]
                  using target_cons_of_error defined initial
                    (.assign (.div dest left right))
                    (sourceToTargetBody rest) (initial right ≠ 0)
                    (evalSourceBody rest step).2
                    s!"division by zero at local {right}" herr (fun hne => hne hzero)
              · have hok : R1CSLike.materializeOp initial
                    (.assign (.div dest left right) : R1CSLike.Op ctx F) =
                    .ok step := by
                    simp only [R1CSLike.materializeOp, hzero, if_false,
                      Except.ok.injEq]
                    funext v
                    simp [step, R1CSLike.writeWitness, Felt.applyOp, Felt.evalVal,
                      Felt.destVar, div_eq_mul_inv]
                simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                  sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                  Felt.backendValid, hzero]
                  using target_cons_of_ok defined extended initial step
                    (.assign (.div dest left right)) (sourceToTargetBody rest)
                    (initial right ≠ 0)
                    (evalSourceBody rest step).2 hok htail
                    (fun final hpres => felt_head_satisfies_iff defined
                      (.div dest left right) initial final hreads hfresh hpres)
                    hextend hstepPreserves
          | add dest left right =>
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                Felt.backendValid]
                using target_cons_of_ok defined extended initial step
                  (.assign (.add dest left right)) (sourceToTargetBody rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.add dest left right) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | sub dest left right =>
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                Felt.backendValid]
                using target_cons_of_ok defined extended initial step
                  (.assign (.sub dest left right)) (sourceToTargetBody rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.sub dest left right) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | mul dest left right =>
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                Felt.backendValid]
                using target_cons_of_ok defined extended initial step
                  (.assign (.mul dest left right)) (sourceToTargetBody rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.mul dest left right) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | neg dest source =>
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                Felt.backendValid]
                using target_cons_of_ok defined extended initial step
                  (.assign (.neg dest source)) (sourceToTargetBody rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.neg dest source) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | inv dest source =>
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                Felt.backendValid]
                using target_cons_of_ok defined extended initial step
                  (.assign (.inv dest source)) (sourceToTargetBody rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.inv dest source) initial final hreads hfresh hpres)
                  hextend hstepPreserves
          | const dest value =>
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                  StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt,
                Felt.backendValid]
                using target_cons_of_ok defined extended initial step
                  (.assign (.const dest value)) (sourceToTargetBody rest) True
                  (evalSourceBody rest step).2 rfl htail
                  (fun final hpres => felt_head_satisfies_iff defined
                    (.const dest value) initial final hreads hfresh hpres)
                  hextend hstepPreserves
        · cases payload with
          | eq left right =>
              have htailSSA : isSSA defined rest = true := by
                simpa [SourceSet, CallPass.TargetSet] using hparts.2
              have htail : TargetBodySpec defined (sourceToTargetBody rest) initial
                  (evalSourceBody rest initial).2 := by
                simpa [MaterializeSpec] using ih defined initial htailSSA
              have hhead : ∀ final, Preserves defined initial final →
                  (R1CSLike.satisfiesOp final
                    (.assertEq left right : R1CSLike.Op ctx F) ↔
                    initial left = initial right) := by
                intro final hpres
                have hleft := hpres left ((List.all_eq_true.mp hparts.1) left (by
                  change left ∈ [left, right]
                  simp))
                have hright := hpres right ((List.all_eq_true.mp hparts.1) right (by
                  change right ∈ [left, right]
                  simp))
                simp [R1CSLike.satisfiesOp, hleft, hright]
              simpa [MaterializeSpec, TargetBodySpec, sourceToTargetBody,
                sourceToTargetStmt, evalSourceBody, evalSourceStmt,
                StructObjectPass.evalTargetBody, StructObjectPass.evalTargetStmt]
                using target_cons_of_ok defined defined initial initial
                  (.assertEq left right) (sourceToTargetBody rest)
                  (initial left = initial right)
                  (evalSourceBody rest initial).2 rfl htail hhead
                  (fun _ h => h) (fun _ _ => rfl)

/-- Object erasure and terminal lowering use definitionally identical leaf semantics. -/
theorem evalSourceBody_eq_evalTargetBody [Field F] {ctx : OpCtx}
    (body : List (Stmt SourceSet ctx F)) (env : LocalVar → F) :
    evalSourceBody body env = StructObjectPass.evalTargetBody body env := rfl

/-- Successful direct materialization produces a satisfying terminal witness exactly
when direct object-erasure target semantics accepts same initial witness. -/
theorem materialize_satisfies_iff [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt SourceSet ctx F)) (defined : LocalVar → Bool)
    (initial : LocalVar → F) (hssa : isSSA defined body = true) :
    (∃ final,
        R1CSLike.materializeBody (sourceToTargetBody body) initial = .ok final ∧
        R1CSLike.satisfies final (sourceToTargetBody body)) ↔
      (StructObjectPass.evalTargetBody body initial).2 := by
  rw [← evalSourceBody_eq_evalTargetBody]
  have hspec := materialize_spec body defined initial hssa
  unfold MaterializeSpec at hspec
  cases hmaterialize : R1CSLike.materializeBody
      (sourceToTargetBody body) initial with
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

/-- Successful materialization of a certified leaf body leaves every initially defined
local unchanged.

Proof sketch: `materialize_spec` supplies `Preserves` for the body's SSA `defined`
predicate, which is exactly `v < out.numParams` by `FuncDef.wf_ssa`. -/
theorem materializeBody_preserves_params [Field F] [DecidableEq F]
    {n i numMembers : Nat} (out : FuncDef SourceSet n i F .constraint numMembers)
    (initial final : LocalVar → F)
    (hmaterialize : R1CSLike.materializeBody (sourceToTargetBody out.body) initial = .ok final) :
    ∀ v, v < out.numParams → final v = initial v := by
  have hspec := materialize_spec out.body _ initial out.wf_ssa
  unfold MaterializeSpec at hspec
  rw [hmaterialize] at hspec
  intro v hv
  exact hspec.2 v (by simpa using hv)

/-- Object observations and terminal materialization agree for any initial leaf
environment with the certified layout's observable slots.

Proof sketch: compose the related-state object simulation with leaf materialization
correctness. This is a local relational bridge, not arbitrary-terminal-witness reflection. -/
theorem source_target_related_materialize_iff [Field F] [DecidableEq F]
    {n i numMembers : Nat}
    (fn : FuncDef StructObjectPass.SourceSet n i F .constraint numMembers)
    (out : FuncDef SourceSet n i F .constraint numMembers)
    (hlower : StructObjectPass.lowerFunc fn = some out)
    (computeParams : Nat) (inputs objects : List F) (initial : LocalVar → F)
    (hrel : StructObjectPass.CanonicalStateRel fn.numParams computeParams
      (StructObjectPass.witnessSpan StructObjectPass.StaticState.initial.objects 0 fn.body)
      inputs objects initial) :
    (ObjectResidualSemantics.evalBody fn.body
      (TypedSourceSemantics.initialState fn.numParams computeParams inputs objects)).2 ↔
      ∃ final, R1CSLike.materializeBody (sourceToTargetBody out.body) initial = .ok final ∧
        R1CSLike.satisfies final (sourceToTargetBody out.body) := by
  exact (StructObjectPass.lowerFunc_related_iff fn out hlower computeParams
    inputs objects initial hrel).symm.trans
    (materialize_satisfies_iff out.body _ initial out.wf_ssa).symm

/-- An arbitrary satisfying terminal witness reflects to related finite object
observations. Proof sketch: satisfaction makes materialization a fixed point, then
the related-state bridge reflects it to independent object semantics. No successful
forwarding hypothesis or generated-witness provenance is required. -/
theorem source_of_related_terminal_satisfies [Field F]
    {n i numMembers : Nat}
    (fn : FuncDef StructObjectPass.SourceSet n i F .constraint numMembers)
    (out : FuncDef SourceSet n i F .constraint numMembers)
    (hlower : StructObjectPass.lowerFunc fn = some out)
    (computeParams : Nat) (inputs objects : List F) (witness : LocalVar → F)
    (hrel : StructObjectPass.CanonicalStateRel fn.numParams computeParams
      (StructObjectPass.witnessSpan StructObjectPass.StaticState.initial.objects 0 fn.body)
      inputs objects witness)
    (hsat : R1CSLike.satisfies witness (sourceToTargetBody out.body)) :
    (ObjectResidualSemantics.evalBody fn.body
      (TypedSourceSemantics.initialState fn.numParams computeParams inputs objects)).2 := by
  classical
  exact (source_target_related_materialize_iff fn out hlower computeParams
    inputs objects witness hrel).mpr
    ⟨witness, R1CSLike.materializeBody_of_satisfies _ witness hsat, hsat⟩

/-- Canonical specialization of the related-state materialization bridge.
Proof sketch: the canonical seed agrees with itself on every allocated slot. -/
theorem source_target_materialize_iff [Field F] [DecidableEq F]
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
        R1CSLike.materializeBody (sourceToTargetBody out.body) seed = .ok final ∧
        R1CSLike.satisfies final (sourceToTargetBody out.body) := by
  exact source_target_related_materialize_iff fn out hlower computeParams inputs objects _
    (StructObjectPass.canonicalStateRel_seed _ _ _ _ _)

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

/-- Dialect lowering produces exact direct terminal body. -/
theorem lowerBodyFresh_toTargetBody {γ : OpCtx} (next : LocalVar)
    (body : List (Stmt SourceSet γ F)) :
    (lowerBodyFresh (lowerOpFresh (F := F)) next body).1 =
      sourceToTargetBody body := by
  induction body generalizing next with
  | nil => rfl
  | cons stmt rest ih =>
      cases stmt with
      | op d op =>
          rcases source_ix_cases d with hd | hd
          · subst d
            cases op <;>
              simp [lowerBodyFresh, lowerOpFresh, lowerOp,
                sourceToTargetBody, sourceToTargetStmt, R1CSLike.ix, ih]
          · subst d
            cases op
            simp [lowerBodyFresh, lowerOpFresh, lowerOp,
              sourceToTargetBody, sourceToTargetStmt, R1CSLike.ix, ih]

/-- Leaf-dialect lowering with fresh-variable, SSA, and handler simulation certificates. -/
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

theorem lowerModuleBody_eq_sourceToTargetBody [Field F] {ctx : OpCtx}
    (numParams : Nat) (body : List (Stmt SourceSet ctx F)) :
    (dialectPass F).lowerModuleBody numParams body = sourceToTargetBody body := by
  change (lowerBodyFresh (lowerOpFresh (F := F)) (startFresh numParams body) body).1 =
    sourceToTargetBody body
  exact lowerBodyFresh_toTargetBody (startFresh numParams body) body

/-- Certified object erasure followed by direct terminal materialization. -/
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
    let terminal := (dialectPass F).lowerModuleBody out.numParams out.body
    (ObjectResidualSemantics.evalBody fn.body
      (TypedSourceSemantics.initialState fn.numParams computeParams
        inputs objects)).2 ↔
      ∃ final,
        R1CSLike.materializeBody terminal seed = .ok final ∧
        R1CSLike.satisfies final terminal := by
  dsimp only
  rw [lowerModuleBody_eq_sourceToTargetBody]
  exact source_target_materialize_iff fn out hlower computeParams inputs objects

/-- Total module-level constraint wrapper, ready to compose after call erasure. -/
def moduleConstraintPass (F : Type) [Field F] :
    ModuleConstraintPass SourceSet TargetSet F :=
  ModuleConstraintPass.ofDialectPass (dialectPass F)

/-- Field-local Call erasure followed by terminal dialect lowering. -/
noncomputable def callToR1CSLike (F : Type) [Field F] :
    CallSemantics.CallModuleConstraintPass TargetSet F :=
  CallSemantics.CallModuleConstraintPass.compose
    (CallSemantics.moduleConstraintPass (F := F))
    (moduleConstraintPass F) rfl

/-- Compile one lowered module entry through direct terminal R1CS backend. -/
def compileEntryConstrain (F : Type) [Field F] {n : Nat}
    (m : Module TargetSet n F) (entry : Fin n) : R1CS.System F :=
  R1CSLike.toR1CS (m.structs entry).constrain.body

end Dialect.R1CSLikePass
