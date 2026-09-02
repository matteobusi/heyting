/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.OracleErasure
import Heyting.Dialects.ObjectResidualSemantics
import Heyting.Dialects.CallSemantics

/-!
# Object-aware Call erasure semantics

This file relates direct recursive constraint execution over
`[Call, StructObject, Felt, ConstrainEq]` to hygienic Call expansion into
`[StructObject, Felt, ConstrainEq]`.
-/

namespace Dialect.ObjectCallSemantics

open Dialect

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

abbrev SourceSet : DialectSet := TypedSourceSemantics.ProjectedSet
abbrev TargetSet : DialectSet := ObjectResidualSemantics.Set
abbrev State (F : Type) := StructObject.State F

def DestinationsAbove {ctx : OpCtx} {F : Type}
    (floor : LocalVar) (body : List (Stmt TargetSet ctx F)) : Prop :=
  ∀ stmt ∈ body, ∀ dest, stmt.dest = some dest → floor ≤ dest

def DestinationsBelow {ctx : OpCtx} {F : Type}
    (ceiling : LocalVar) (body : List (Stmt TargetSet ctx F)) : Prop :=
  ∀ stmt ∈ body, ∀ dest, stmt.dest = some dest → dest < ceiling

def EmptyObjectsAbove (floor : LocalVar) (state : State F) : Prop :=
  ∀ v, floor ≤ v → state.objects v = []

/-- Source and expanded states agree on every currently defined local and on
global object-machine state. -/
structure StateAgreesOn (defined : LocalVar → Bool)
    (rename : LocalVar → LocalVar) (source target : State F) : Prop where
  values : ∀ v, defined v = true → target.values (rename v) = source.values v
  witness : target.witness = source.witness
  nextPath : target.nextPath = source.nextPath

def BodyObjectsAgree {ctx : OpCtx} (body : List (Stmt SourceSet ctx F))
    (rename : LocalVar → LocalVar) (source target : State F) : Prop :=
  ∀ stmt ∈ body, ∀ v ∈ stmt.vars,
    target.objects (rename v) = source.objects v

theorem StateAgreesOn.mono {defined defined' : LocalVar → Bool}
    {rename : LocalVar → LocalVar} {source target : State F}
    (h : StateAgreesOn defined rename source target)
    (hle : ∀ v, defined' v = true → defined v = true) :
    StateAgreesOn defined' rename source target where
  values v hv := h.values v (hle v hv)
  witness := h.witness
  nextPath := h.nextPath

/-- Argument binding agrees with hygienic parameter renaming in both local
channels. -/
theorem stateAgreesOn_bindArgs_inlineVar [Field F]
    (defined : LocalVar → Bool) (rename : LocalVar → LocalVar)
    (args : List LocalVar) (numParams base : Nat)
    (hargs : args.length = numParams) (source target : State F)
    (hdefined : args.all defined = true)
    (hagrees : StateAgreesOn defined rename source target) :
    StateAgreesOn (fun v => decide (v < numParams))
      (CallPass.inlineVar rename args numParams base hargs)
      { values := TypedSourceSemantics.bindValues source.values args
        objects := TypedSourceSemantics.bindObjects source.objects args
        witness := source.witness
        nextPath := source.nextPath }
      target := by
  constructor
  · intro v hv
    have hvlt : v < numParams := by simpa using hv
    rw [CallPass.inlineVar_param rename args numParams base v hargs hvlt]
    have hargDefined := (List.all_eq_true.mp hdefined)
      (args.get ⟨v, by simpa [hargs] using hvlt⟩)
      (List.get_mem args ⟨v, by simpa [hargs] using hvlt⟩)
    simpa [TypedSourceSemantics.bindValues, List.getElem?_eq_getElem,
      hargs, hvlt] using hagrees.values _ hargDefined
  · exact hagrees.witness
  · exact hagrees.nextPath

theorem DestinationsAbove.tail {ctx : OpCtx} {F : Type}
    {floor : LocalVar} {head : Stmt TargetSet ctx F}
    {tail : List (Stmt TargetSet ctx F)}
    (h : DestinationsAbove floor (head :: tail)) : DestinationsAbove floor tail := by
  intro stmt hmem dest hdest
  exact h stmt (by simp [hmem]) dest hdest

theorem DestinationsBelow.tail {ctx : OpCtx} {F : Type}
    {ceiling : LocalVar} {head : Stmt TargetSet ctx F}
    {tail : List (Stmt TargetSet ctx F)}
    (h : DestinationsBelow ceiling (head :: tail)) : DestinationsBelow ceiling tail := by
  intro stmt hmem dest hdest
  exact h stmt (by simp [hmem]) dest hdest

theorem destinationsBelow_append {ctx : OpCtx} {F : Type}
    {ceiling : LocalVar} {left right : List (Stmt TargetSet ctx F)}
    (hleft : DestinationsBelow ceiling left)
    (hright : DestinationsBelow ceiling right) :
    DestinationsBelow ceiling (left ++ right) := by
  intro stmt hmem dest hdest
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft stmt hmem dest hdest
  · exact hright stmt hmem dest hdest

/-- Executable Boolean semantics for a call-free object-aware body. -/
def evalTargetBody [Field F] [DecidableEq F] {ctx : OpCtx} :
    List (Stmt TargetSet ctx F) → State F → State F × Bool
  | [], state => (state, true)
  | stmt :: rest, state =>
    let step := TypedSourceSemantics.evalProjectedLeaf stmt state
    let tail := evalTargetBody rest step.1
    (tail.1, step.2 && tail.2)

theorem evalTargetBody_append [Field F] [DecidableEq F] {ctx : OpCtx}
    (left right : List (Stmt TargetSet ctx F)) (state : State F) :
    evalTargetBody (left ++ right) state =
      let first := evalTargetBody left state
      let second := evalTargetBody right first.1
      (second.1, first.2 && second.2) := by
  induction left generalizing state with
  | nil => rfl
  | cons stmt rest ih =>
    simp only [List.cons_append, evalTargetBody]
    rw [ih]
    simp only [Bool.and_assoc]

/-- Call-free execution cannot change object locals below every destination. -/
theorem evalTargetBody_objects_frame_below [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt TargetSet ctx F)) (floor v : LocalVar) (state : State F)
    (habove : DestinationsAbove floor body) (hv : v < floor) :
    (evalTargetBody body state).1.objects v = state.objects v := by
  induction body generalizing state with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d payload =>
      rcases d with ⟨index, hindex⟩
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
        simp [TargetSet, ObjectResidualSemantics.Set] at hindex
        omega
      rcases hcases with rfl | rfl | rfl
      · cases payload with
        | newStruct dest =>
          have hdest : floor ≤ dest := by
            apply habove (.op ⟨0, hindex⟩ (.newStruct dest)) (by simp) dest
            rfl
          have hne : v ≠ dest := Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hdest)
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.newStruct dest) state) habove.tail]
          simp [StructObject.apply, StructObject.ObjEnv.update, hne]
        | readMember dest self member =>
          have hdest : floor ≤ dest := by
            apply habove (.op ⟨0, hindex⟩ (.readMember dest self member))
              (by simp) dest
            rfl
          have hne : v ≠ dest := Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hdest)
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.readMember dest self member) state) habove.tail]
          simp [StructObject.apply, StructObject.ObjEnv.update, hne]
        | writeMember self member src =>
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.writeMember self member src) state) habove.tail]
          rfl
      · simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
        rw [ih _ habove.tail]
      · cases payload
        simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
        rw [ih state habove.tail]

/-- Call-free execution cannot change field locals below every destination. -/
theorem evalTargetBody_values_frame_below [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt TargetSet ctx F)) (floor v : LocalVar) (state : State F)
    (habove : DestinationsAbove floor body) (hv : v < floor) :
    (evalTargetBody body state).1.values v = state.values v := by
  induction body generalizing state with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d payload =>
      rcases d with ⟨index, hindex⟩
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
        simp [TargetSet, ObjectResidualSemantics.Set] at hindex
        omega
      rcases hcases with rfl | rfl | rfl
      · cases payload with
        | newStruct dest =>
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.newStruct dest) state) habove.tail]
          rfl
        | readMember dest self member =>
          have hdest : floor ≤ dest := by
            apply habove (.op ⟨0, hindex⟩ (.readMember dest self member))
              (by simp) dest
            rfl
          have hne : v ≠ dest := Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hdest)
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.readMember dest self member) state) habove.tail]
          simp [StructObject.apply, StructObject.ValueEnv.update, hne]
        | writeMember self member src =>
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.writeMember self member src) state) habove.tail]
          rfl
      · have hdest : floor ≤ Felt.destVar payload := by
          apply habove (.op ⟨1, hindex⟩ payload) (by simp) (Felt.destVar payload)
          exact Felt.dest_eq payload
        have hne : v ≠ Felt.destVar payload :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hdest)
        simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
        rw [ih _ habove.tail]
        exact Felt.applyOp_at_other payload state.values v hne
      · cases payload
        simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
        rw [ih state habove.tail]

/-- Call-free execution cannot change object locals above every destination. -/
theorem evalTargetBody_objects_frame_above [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt TargetSet ctx F)) (ceiling v : LocalVar) (state : State F)
    (hbelow : DestinationsBelow ceiling body) (hv : ceiling ≤ v) :
    (evalTargetBody body state).1.objects v = state.objects v := by
  induction body generalizing state with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d payload =>
      rcases d with ⟨index, hindex⟩
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
        simp [TargetSet, ObjectResidualSemantics.Set] at hindex
        omega
      rcases hcases with rfl | rfl | rfl
      · cases payload with
        | newStruct dest =>
          have hdest : dest < ceiling := by
            apply hbelow (.op ⟨0, hindex⟩ (.newStruct dest)) (by simp) dest
            rfl
          have hne : v ≠ dest := Nat.ne_of_gt (Nat.lt_of_lt_of_le hdest hv)
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.newStruct dest) state) hbelow.tail]
          simp [StructObject.apply, StructObject.ObjEnv.update, hne]
        | readMember dest self member =>
          have hdest : dest < ceiling := by
            apply hbelow (.op ⟨0, hindex⟩ (.readMember dest self member))
              (by simp) dest
            rfl
          have hne : v ≠ dest := Nat.ne_of_gt (Nat.lt_of_lt_of_le hdest hv)
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.readMember dest self member) state) hbelow.tail]
          simp [StructObject.apply, StructObject.ObjEnv.update, hne]
        | writeMember self member src =>
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
          rw [ih (StructObject.apply (.writeMember self member src) state) hbelow.tail]
          rfl
      · simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
        rw [ih _ hbelow.tail]
      · cases payload
        simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf]
        rw [ih state hbelow.tail]

/-- If every write destination is below `ceiling`, execution preserves empty
object storage at and above `ceiling`. -/
theorem evalTargetBody_emptyObjectsAbove [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt TargetSet ctx F)) (start ceiling : LocalVar)
    (state : State F) (hstart : EmptyObjectsAbove start state)
    (hle : start ≤ ceiling) (hbelow : DestinationsBelow ceiling body) :
    EmptyObjectsAbove ceiling (evalTargetBody body state).1 := by
  intro v hv
  rw [evalTargetBody_objects_frame_above body ceiling v state hbelow hv]
  exact hstart v (Nat.le_trans hle hv)

/-- Boolean target execution and existing propositional residual execution
thread identical states. -/
theorem evalTargetBody_state_eq [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt TargetSet ctx F)) (state : State F) :
    (evalTargetBody body state).1 =
      (ObjectResidualSemantics.evalBody body state).1 := by
  induction body generalizing state with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d payload =>
      rcases d with ⟨index, hindex⟩
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
        simp [TargetSet, ObjectResidualSemantics.Set] at hindex
        omega
      rcases hcases with rfl | rfl | rfl
      · simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf,
          ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt]
        exact ih (StructObject.apply payload state)
      · simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf,
          ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt]
        exact ih ({ state with values := Felt.applyOp payload state.values })
      · cases payload
        simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf,
          ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt]
        exact ih state

/-- Boolean truth is exactly existing propositional object-residual truth. -/
theorem evalTargetBody_true_iff [Field F] [DecidableEq F] {ctx : OpCtx}
    (body : List (Stmt TargetSet ctx F)) (state : State F) :
    (evalTargetBody body state).2 = true ↔
      (ObjectResidualSemantics.evalBody body state).2 := by
  induction body generalizing state with
  | nil => simp [evalTargetBody, ObjectResidualSemantics.evalBody]
  | cons stmt rest ih =>
    cases stmt with
    | op d payload =>
      rcases d with ⟨index, hindex⟩
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
        simp [TargetSet, ObjectResidualSemantics.Set] at hindex
        omega
      rcases hcases with rfl | rfl | rfl
      · simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf,
          ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
          Bool.true_and, true_and]
        exact ih (StructObject.apply payload state)
      · simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf,
          ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
          Bool.and_eq_true]
        rw [Felt.backendValidBool_eq_true]
        exact and_congr Iff.rfl
          (ih ({ state with values := Felt.applyOp payload state.values }))
      · cases payload with
        | eq left right =>
          simp only [evalTargetBody, TypedSourceSemantics.evalProjectedLeaf,
            ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
            Bool.and_eq_true, decide_eq_true_eq]
          exact and_congr Iff.rfl (ih state)

def ConstrainDestinationsBelow [Zero F] {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) : Prop :=
  ∀ (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar),
    CallErasure.eraseBodyInto (CallErasure.objectFeltConstrainSyntax (F := F))
      m caller current .constrain rename next stmts = some result →
    CallPass.BodyRenameInvariant stmts rename next →
    DestinationsBelow result.2 result.1

set_option linter.flexible false in
theorem eraseBodyInto_constrain_destinationsBelow
    [Zero F]
    {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) :
    ConstrainDestinationsBelow (callerMembers := callerMembers)
      m caller current rename next stmts := by
  let motive := fun (currentMembers : Nat) (current : Fin n)
      (kind : CallErasure.BodyKind)
      (rename : LocalVar → LocalVar) (next : LocalVar)
      (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) =>
    match kind with
    | .compute => True
    | .constrain => ConstrainDestinationsBelow (callerMembers := callerMembers)
        m caller current rename next stmts
  change motive currentMembers current .constrain rename next stmts
  apply CallErasure.eraseBodyInto.induct
    (config := CallErasure.objectFeltConstrainSyntax (F := F))
    (callerMembers := callerMembers) (m := m) (caller := caller)
    (motive := motive) (currentMembers := currentMembers)
    (current := current) (kind := .constrain)
  · intro _ _ kind _ _
    simp only [motive]
    cases kind
    · trivial
    · unfold ConstrainDestinationsBelow
      intro result herase _
      simp [CallErasure.eraseBodyInto] at herase
      subst result
      simp [DestinationsBelow]
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · simp only [motive]
    unfold ConstrainDestinationsBelow
    intros _ current rename next rest isLt target selector args hselector dest
      result herase
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector] at herase
  · simp only [motive]
    unfold ConstrainDestinationsBelow
    intros _ current rename next rest isLt target selector args hselector hargs
      hcalleeNone _ result herase _
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargs, hcalleeNone] at herase
  · simp only [motive]
    unfold ConstrainDestinationsBelow
    intros _ current rename next rest isLt target selector args hselector hargs
      calleeBody afterCallee hcallee htailNone _ _ result herase
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargs, hcallee, htailNone] at herase
  · simp only [motive]
    unfold ConstrainDestinationsBelow
    intros _ current rename next rest isLt target selector args hselector hargs
      calleeBody afterCallee hcallee tail afterTail htail ihCallee ihTail
      result herase hren
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargs, hcallee, htail] at herase
    subst result
    let fn := (Call.targetStructAt m current target).constrain
    let calleeRename := CallPass.inlineVar rename args fn.numParams next hargs
    have hparamsBelow : ∀ k (hk : k < fn.numParams),
        rename (args.get ⟨k, by simpa [hargs] using hk⟩) < next := by
      intro k hk
      apply hren.1 (.op ⟨0, isLt⟩ (.call none target selector args)) (by simp)
      change args.get ⟨k, by simpa [hargs] using hk⟩ ∈ args
      exact List.get_mem _ _
    have hcalleeRen :=
      (CallPass.renameInvariant_inlineVar fn rename args next hargs hparamsBelow).body
    have hcalleeBelow := ihCallee (calleeBody, afterCallee) hcallee hcalleeRen
    have hreserved : next + CallErasure.funcVarBound fn ≤ afterCallee :=
      CallErasure.eraseBodyInto_next_mono
        (CallErasure.objectFeltConstrainSyntax (F := F))
        CallErasure.objectFeltConstrainReturnMonotone m caller
        (Call.moduleTarget target current.isLt) .constrain calleeRename
        (next + CallErasure.funcVarBound fn) fn.body
        (calleeBody, afterCallee) hcallee
    have htailRen := hren.tail.mono (Nat.le_trans
      (Nat.le_add_right next _) hreserved)
    have htailBelow := ihTail (tail, afterTail) htail htailRen
    apply destinationsBelow_append
    · exact fun stmt hmem dest hdest =>
        Nat.lt_of_lt_of_le (hcalleeBelow stmt hmem dest hdest)
          (CallErasure.eraseBodyInto_next_mono
            (CallErasure.objectFeltConstrainSyntax (F := F))
            CallErasure.objectFeltConstrainReturnMonotone m caller current
            .constrain rename afterCallee rest (tail, afterTail) htail)
    · exact htailBelow
  · simp only [motive]
    unfold ConstrainDestinationsBelow
    intros _ current rename next rest isLt target selector args hselector
      hargsFalse result herase _
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargsFalse] at herase
  · simp only [motive]
    intros _ current kind rename next rest isLt dest target selector args
      hselectorFalse
    cases kind
    · trivial
    · unfold ConstrainDestinationsBelow
      intro result herase
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hselectorFalse] at herase
  · simp only [motive]
    intros _ current kind rename next rest index hindex payload hlowerNone
    cases kind
    · trivial
    · unfold ConstrainDestinationsBelow
      intro result herase
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hlowerNone] at herase
  · simp only [motive]
    intros _ current kind rename next rest index hindex lowered htailNone payload
      hlower ih
    cases kind
    · trivial
    · unfold ConstrainDestinationsBelow
      intro result herase
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hlower, htailNone] at herase
  · simp only [motive]
    intros _ current kind rename next rest index hindex lowered tail afterTail htail
      payload hlower ih
    cases kind
    · trivial
    · unfold ConstrainDestinationsBelow
      intro result herase hren
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hlower, htail] at herase
      subst result
      intro stmt hmem dest hdest
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have hsourceDest := CallErasure.lowerResidualStmt_dest
          (CallErasure.objectFeltConstrainSyntax (F := F))
          CallErasure.objectFeltConstrainRenameStable rename
          ⟨index, by simp [SourceSet] at hindex; simp [TargetSet]; omega⟩
          payload stmt hlower
        rw [hsourceDest] at hdest
        cases hpayloadDest : (TargetSet.get ⟨index, by
            simp [SourceSet] at hindex; simp [TargetSet]; omega⟩).dest payload with
        | none => rw [hpayloadDest] at hdest; contradiction
        | some sourceDest =>
          simp only [hpayloadDest, Option.map_some, Option.some.injEq] at hdest
          subst dest
          apply Nat.lt_of_lt_of_le
          · exact hren.1 (.op ⟨index + 1, hindex⟩ payload) (by simp) sourceDest
              (by
                rw [Stmt.vars]
                apply List.mem_append_left
                change sourceDest ∈ ((TargetSet.get ⟨index, _⟩).dest payload).toList
                rw [hpayloadDest]
                simp)
          · exact CallErasure.eraseBodyInto_next_mono
              (CallErasure.objectFeltConstrainSyntax (F := F))
              CallErasure.objectFeltConstrainReturnMonotone m caller current
              .constrain rename next rest (tail, afterTail) htail
      · exact ih (tail, afterTail) htail hren.tail stmt hmem dest hdest

def extendDefined (defined : LocalVar → Bool) (dest : Option LocalVar) :
    LocalVar → Bool :=
  match dest with
  | none => defined
  | some d => fun v => defined v || v == d

set_option linter.flexible false in
/-- One successfully transported residual statement preserves both object
state and Boolean constraint observation under hygienic renaming. -/
theorem evalProjectedLeaf_lowerResidualStmt [Field F] [DecidableEq F]
    {sourceCtx targetCtx : OpCtx} (rename : LocalVar → LocalVar)
    (d : Fin TargetSet.length) (payload : (TargetSet.get d).Op sourceCtx F)
    (lowered : Stmt TargetSet targetCtx F)
    (hlower : CallErasure.lowerResidualStmt
      (CallErasure.objectFeltConstrainSyntax (F := F)) rename d payload =
        some lowered)
    (defined : LocalVar → Bool)
    (hreads : ((TargetSet.get d).reads payload).all defined = true)
    (hcap : (TargetSet.get d).cap payload ≤ .constraint)
    (hfresh : ∀ dest, (TargetSet.get d).dest payload = some dest →
      defined dest = false)
    (hseparate : ∀ dest, (TargetSet.get d).dest payload = some dest →
      ∀ v, v ≠ dest → rename v ≠ rename dest)
    (source target : State F)
    (hobjects : ∀ v ∈ (TargetSet.get d).reads payload,
      target.objects (rename v) = source.objects v)
    (hagrees : StateAgreesOn defined rename source target) :
    let sourceStep := TypedSourceSemantics.evalProjectedLeaf (.op d payload) source
    let targetStep := TypedSourceSemantics.evalProjectedLeaf lowered target
    targetStep.2 = sourceStep.2 ∧
      StateAgreesOn (extendDefined defined ((TargetSet.get d).dest payload)) rename
        sourceStep.1 targetStep.1 := by
  rcases d with ⟨index, hindex⟩
  have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
    simp [TargetSet, ObjectResidualSemantics.Set] at hindex
    omega
  rcases hcases with rfl | rfl | rfl
  · cases payload with
    | newStruct dest =>
      change StructObject.cap
        (.newStruct dest : StructObject.Op sourceCtx F) ≤ .constraint at hcap
      change Capability.witness = .pure ∨ Capability.witness = .constraint at hcap
      contradiction
    | readMember dest self member =>
      by_cases hmember : member.val < targetCtx.numMembers
      · simp [CallErasure.lowerResidualStmt,
          CallErasure.objectFeltConstrainSyntax,
          CallErasure.recontextualizeObjectFeltConstrain, hmember] at hlower
        subst lowered
        have hself : target.objects (rename self) = source.objects self := by
          apply hobjects self
          change self ∈ [self]
          simp
        constructor
        · rfl
        · constructor
          · intro v hv
            change (defined v || v == dest) = true at hv
            simp only [Bool.or_eq_true, beq_iff_eq] at hv
            rcases hv with hv | rfl
            · have hvne : v ≠ dest := by
                intro heq
                subst v
                rw [hfresh dest rfl] at hv
                contradiction
              have hne := hseparate dest rfl v hvne
              change StructObject.ValueEnv.update target.values (rename dest)
                  (target.witness (target.objects (rename self), member.val))
                  (rename v) =
                StructObject.ValueEnv.update source.values dest
                  (source.witness (source.objects self, member.val)) v
              simp [StructObject.ValueEnv.update, hne, hvne,
                hagrees.values v hv]
            · change StructObject.ValueEnv.update target.values (rename v)
                  (target.witness (target.objects (rename self), member.val))
                  (rename v) =
                StructObject.ValueEnv.update source.values v
                  (source.witness (source.objects self, member.val)) v
              simp [StructObject.ValueEnv.update, hself, hagrees.witness]
          · simpa [StructObject.apply] using hagrees.witness
          · simpa [StructObject.apply] using hagrees.nextPath
      · simp [CallErasure.lowerResidualStmt,
          CallErasure.objectFeltConstrainSyntax,
          CallErasure.recontextualizeObjectFeltConstrain, hmember] at hlower
    | writeMember self member src =>
      change StructObject.cap
        (.writeMember self member src : StructObject.Op sourceCtx F) ≤
          .constraint at hcap
      change Capability.witness = .pure ∨ Capability.witness = .constraint at hcap
      contradiction
  · have hreadsFelt : (Felt.reads payload).all defined = true := by
      simpa [TargetSet, ObjectResidualSemantics.Set] using hreads
    have hseparateFelt : ∀ v, v ≠ Felt.destVar payload →
        rename v ≠ rename (Felt.destVar payload) := by
      intro v hv
      apply hseparate (Felt.destVar payload)
      · simpa [TargetSet, ObjectResidualSemantics.Set] using Felt.dest_eq payload
      · exact hv
    have hvalues := CallSemantics.applyOp_lowerFeltOp_agreesOn defined rename
      (γ' := targetCtx) payload source.values target.values hreadsFelt
      hagrees.values hseparateFelt
    have hvalid := Felt.backendValidBool_mapVars rename payload source.values
      target.values (by
        intro v hv
        exact hagrees.values v ((List.all_eq_true.mp hreadsFelt) v hv))
    cases payload <;>
      simp [CallErasure.lowerResidualStmt,
        CallErasure.objectFeltConstrainSyntax,
        CallErasure.recontextualizeObjectFeltConstrain] at hlower <;>
      subst lowered
    all_goals
      constructor
      · simpa [TypedSourceSemantics.evalProjectedLeaf] using hvalid
      · constructor
        · simpa [extendDefined, TargetSet, ObjectResidualSemantics.Set,
              Felt.dest, TypedSourceSemantics.evalProjectedLeaf] using hvalues
        · simpa [Felt.applyOp] using hagrees.witness
        · simpa [Felt.applyOp] using hagrees.nextPath
  · cases payload with
    | eq left right =>
      simp [CallErasure.lowerResidualStmt,
        CallErasure.objectFeltConstrainSyntax,
        CallErasure.recontextualizeObjectFeltConstrain] at hlower
      subst lowered
      have hleft : target.values (rename left) = source.values left := by
        apply hagrees.values left
        change [left, right].all defined = true at hreads
        apply (List.all_eq_true.mp hreads) left
        simp
      have hright : target.values (rename right) = source.values right := by
        apply hagrees.values right
        change [left, right].all defined = true at hreads
        apply (List.all_eq_true.mp hreads) right
        simp
      constructor
      · change decide (target.values (rename left) = target.values (rename right)) =
          decide (source.values left = source.values right)
        simp [hleft, hright]
      · simpa [extendDefined, ConstrainEq.dest,
          TypedSourceSemantics.evalProjectedLeaf] using hagrees

set_option linter.flexible false in
/-- Residual step preserves object-path agreement needed by remaining body. -/
theorem bodyObjectsAgree_lowerResidualStmt [Field F] [DecidableEq F]
    {sourceCtx targetCtx : OpCtx} (rename : LocalVar → LocalVar)
    (d : Fin TargetSet.length) (payload : (TargetSet.get d).Op sourceCtx F)
    (rest : List (Stmt SourceSet sourceCtx F))
    (lowered : Stmt TargetSet targetCtx F)
    (hlower : CallErasure.lowerResidualStmt
      (CallErasure.objectFeltConstrainSyntax (F := F)) rename d payload =
        some lowered)
    (hcap : (TargetSet.get d).cap payload ≤ .constraint)
    (hseparate : ∀ dest, (TargetSet.get d).dest payload = some dest →
      ∀ v, v ≠ dest → rename v ≠ rename dest)
    (source target : State F)
    (hobjects : BodyObjectsAgree (.op ⟨d.val + 1, by
        simp [SourceSet, TargetSet, TypedSourceSemantics.ProjectedSet,
          TypedSourceSemantics.ProjectedResidualSet]
        omega⟩ payload :: rest)
      rename source target) :
    BodyObjectsAgree rest rename
      (TypedSourceSemantics.evalProjectedLeaf (.op d payload) source).1
      (TypedSourceSemantics.evalProjectedLeaf lowered target).1 := by
  rcases d with ⟨index, hindex⟩
  have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
    simp [TargetSet, ObjectResidualSemantics.Set] at hindex
    omega
  rcases hcases with rfl | rfl | rfl
  · cases payload with
    | newStruct dest =>
      change Capability.witness ≤ .constraint at hcap
      change Capability.witness = .pure ∨ Capability.witness = .constraint at hcap
      contradiction
    | readMember dest self member =>
      by_cases hmember : member.val < targetCtx.numMembers
      · simp [CallErasure.lowerResidualStmt,
          CallErasure.objectFeltConstrainSyntax,
          CallErasure.recontextualizeObjectFeltConstrain, hmember] at hlower
        subst lowered
        have hself : target.objects (rename self) = source.objects self := by
          apply hobjects (.op ⟨1, by simpa using hindex⟩
            (.readMember dest self member)) (by simp) self
          change self ∈ [dest] ++ [self]
          simp
        intro stmt hmem v hv
        by_cases heq : v = dest
        · subst v
          change StructObject.ObjEnv.update target.objects (rename dest)
              (target.objects (rename self) ++ [member.val]) (rename dest) =
            StructObject.ObjEnv.update source.objects dest
              (source.objects self ++ [member.val]) dest
          simp [StructObject.ObjEnv.update, hself]
        · have hrenameNe := hseparate dest rfl v heq
          change StructObject.ObjEnv.update target.objects (rename dest)
              (target.objects (rename self) ++ [member.val]) (rename v) =
            StructObject.ObjEnv.update source.objects dest
              (source.objects self ++ [member.val]) v
          simp [StructObject.ObjEnv.update, hrenameNe, heq,
            hobjects stmt (by simp [hmem]) v hv]
      · simp [CallErasure.lowerResidualStmt,
          CallErasure.objectFeltConstrainSyntax,
          CallErasure.recontextualizeObjectFeltConstrain, hmember] at hlower
    | writeMember self member src =>
      change Capability.witness ≤ .constraint at hcap
      change Capability.witness = .pure ∨ Capability.witness = .constraint at hcap
      contradiction
  · cases payload <;>
      simp [CallErasure.lowerResidualStmt,
        CallErasure.objectFeltConstrainSyntax,
        CallErasure.recontextualizeObjectFeltConstrain] at hlower <;>
      subst lowered
    all_goals
      intro stmt hmem v hv
      simpa [TypedSourceSemantics.evalProjectedLeaf] using
        hobjects stmt (by simp [hmem]) v hv
  · cases payload
    simp [CallErasure.lowerResidualStmt,
      CallErasure.objectFeltConstrainSyntax,
      CallErasure.recontextualizeObjectFeltConstrain] at hlower
    subst lowered
    intro stmt hmem v hv
    simpa [TypedSourceSemantics.evalProjectedLeaf] using
      hobjects stmt (by simp [hmem]) v hv

theorem isSSA_cons_dest_fresh {ctx : OpCtx}
    (defined : LocalVar → Bool) (stmt : Stmt SourceSet ctx F)
    (rest : List (Stmt SourceSet ctx F)) (dest : LocalVar)
    (hssa : isSSA defined (stmt :: rest) = true)
    (hdest : stmt.dest = some dest) : defined dest = false := by
  simp only [isSSA] at hssa
  rw [hdest] at hssa
  simp only [Bool.and_eq_true] at hssa
  simpa using hssa.2.1

theorem capsLE_tail {Δ : DialectSet} {ctx : OpCtx} {kind : Capability}
    {head : Stmt Δ ctx F} {tail : List (Stmt Δ ctx F)}
    (hcap : capsLE kind (head :: tail) = true) :
    capsLE kind tail = true := by
  apply List.all_eq_true.mpr
  intro stmt hmem
  exact (List.all_eq_true.mp hcap) stmt (by simp [hmem])

/-- Callee parameter objects reuse caller arguments; every other callee local
starts in fresh empty storage. -/
theorem bodyObjectsAgree_bindArgs_inlineVar [Field F]
    {n i numMembers : Nat}
    (fn : FuncDef SourceSet n i F .constraint numMembers)
    (rename : LocalVar → LocalVar) (args : List LocalVar) (base : LocalVar)
    (hargs : args.length = fn.numParams) (source target : State F)
    (hargsObjects : ∀ v ∈ args,
      target.objects (rename v) = source.objects v)
    (hempty : EmptyObjectsAbove base target) :
    BodyObjectsAgree fn.body
      (CallPass.inlineVar rename args fn.numParams base hargs)
      { values := TypedSourceSemantics.bindValues source.values args
        objects := TypedSourceSemantics.bindObjects source.objects args
        witness := source.witness
        nextPath := source.nextPath }
      target := by
  intro stmt hmem v hv
  by_cases hparam : v < fn.numParams
  · rw [CallPass.inlineVar_param rename args fn.numParams base v hargs hparam]
    have hvArgs : v < args.length := by simpa [hargs] using hparam
    simpa [TypedSourceSemantics.bindObjects, List.getElem?_eq_getElem,
      hvArgs] using hargsObjects
        (args.get ⟨v, hvArgs⟩) (List.get_mem args ⟨v, hvArgs⟩)
  · rw [CallPass.inlineVar_local rename args fn.numParams base v hargs
      (Nat.le_of_not_gt hparam)]
    rw [hempty (CallPass.shiftLocal base v) (Nat.le_add_right base v)]
    simp [TypedSourceSemantics.bindObjects, List.getElem?_eq_getElem,
      hparam, hargs]

/-- Complete semantic invariant for recursive constraint Call expansion. -/
def ConstrainErasureSimulation [Field F] [DecidableEq F]
    {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) : Prop :=
  ∀ (defined : LocalVar → Bool), isSSA defined stmts = true →
    capsLE .constraint stmts = true →
    CallPass.BodyRenameInvariant stmts rename next →
    (∀ v, defined v = true → rename v < next) →
    ∀ (result : List (Stmt TargetSet
        ⟨n, caller.val, callerMembers⟩ F) × LocalVar),
      CallErasure.eraseBodyInto (CallErasure.objectFeltConstrainSyntax (F := F))
          m caller current .constrain rename next stmts = some result →
      ∀ source target,
        StateAgreesOn defined rename source target →
        BodyObjectsAgree stmts rename source target →
        EmptyObjectsAbove next target →
        (evalTargetBody result.1 target).2 =
            (TypedSourceSemantics.evalProjectedBodyIn m current source stmts).2 ∧
          StateAgreesOn (CallPass.definedLocalsAfter defined stmts) rename
            (TypedSourceSemantics.evalProjectedBodyIn m current source stmts).1
            (evalTargetBody result.1 target).1 ∧
          EmptyObjectsAbove result.2 (evalTargetBody result.1 target).1

set_option linter.flexible false in
/-- Hygienic constraint Call expansion preserves direct object-aware
execution, including witness cursor and fresh object storage. -/
theorem eraseBodyInto_constrain_simulation [Field F] [DecidableEq F]
    {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) :
    ConstrainErasureSimulation (callerMembers := callerMembers)
      m caller current rename next stmts := by
  let motive := fun (currentMembers : Nat) (current : Fin n)
      (kind : CallErasure.BodyKind)
      (rename : LocalVar → LocalVar) (next : LocalVar)
      (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) =>
    match kind with
    | .compute => True
    | .constrain => ConstrainErasureSimulation (callerMembers := callerMembers)
        m caller current rename next stmts
  change motive currentMembers current .constrain rename next stmts
  apply CallErasure.eraseBodyInto.induct
    (config := CallErasure.objectFeltConstrainSyntax (F := F))
    (callerMembers := callerMembers) (m := m) (caller := caller)
    (motive := motive) (currentMembers := currentMembers)
    (current := current) (kind := .constrain)
  · intro _ _ kind _ _
    simp only [motive]
    cases kind
    · trivial
    · unfold ConstrainErasureSimulation
      intro defined _ _ _ _ result herase source target hagrees _ hempty
      simp [CallErasure.eraseBodyInto] at herase
      subst result
      simp only [evalTargetBody, TypedSourceSemantics.evalProjectedBodyIn]
      exact ⟨True.intro, by simpa [CallPass.definedLocalsAfter] using hagrees,
        by simpa using hempty⟩
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · simp only [motive]
    unfold ConstrainErasureSimulation
    intros _ current rename next rest isLt target selector args hselector dest
      defined hssa hcaps hren hbelow result herase
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector] at herase
  · simp only [motive]
    unfold ConstrainErasureSimulation
    intros _ current rename next rest isLt target selector args hselector hargs
      hcalleeNone _ defined hssa hcaps hren hbelow result herase
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargs, hcalleeNone] at herase
  · simp only [motive]
    unfold ConstrainErasureSimulation
    intros _ current rename next rest isLt target selector args hselector hargs
      calleeBody afterCallee hcallee htailNone _ _ defined hssa hcaps hren
      hbelow result herase
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargs, hcallee, htailNone] at herase
  · simp only [motive]
    unfold ConstrainErasureSimulation
    intros currentMembers' current rename next rest isLt target selector args
      hselector hargs calleeBody afterCallee hcallee tail afterTail htail
      ihCallee ihTail defined hssa hcaps hren hbelow result herase
      source targetState hagrees hobjects hempty
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargs, hcallee, htail] at herase
    subst result
    let fn := (Call.targetStructAt m current target).constrain
    let calleeRename := CallPass.inlineVar rename args fn.numParams next hargs
    let calleeSource : State F := {
      values := TypedSourceSemantics.bindValues source.values args
      objects := TypedSourceSemantics.bindObjects source.objects args
      witness := source.witness
      nextPath := source.nextPath
    }
    have hparts := CallPass.isSSA_cons_parts defined
      (.op ⟨0, isLt⟩ (.call none target selector args)) rest hssa
    have hargsDefined : args.all defined = true := by
      simpa [Stmt.reads, Call.reads] using hparts.1
    have htailCaps := capsLE_tail hcaps
    have hparamsBelow : ∀ k (hk : k < fn.numParams),
        rename (args.get ⟨k, by simpa [hargs] using hk⟩) < next := by
      intro k hk
      apply hbelow
      exact (List.all_eq_true.mp hargsDefined) _
        (List.get_mem args ⟨k, by simpa [hargs] using hk⟩)
    have hcalleeRen :=
      (CallPass.renameInvariant_inlineVar fn rename args next hargs hparamsBelow).body
    have hcalleeBelow : ∀ v, decide (v < fn.numParams) = true →
        calleeRename v < next + CallErasure.funcVarBound fn := by
      intro v hv
      have hvlt : v < fn.numParams := by simpa using hv
      exact (CallPass.renameInvariant_inlineVar fn rename args next hargs
        hparamsBelow).1 v (Nat.lt_of_lt_of_le hvlt
          (CallPass.numParams_le_funcVarBound fn))
    have hcalleeInitial : StateAgreesOn
        (fun v => decide (v < fn.numParams)) calleeRename calleeSource
        targetState := by
      simpa [calleeSource] using stateAgreesOn_bindArgs_inlineVar defined rename
        args fn.numParams next hargs source targetState hargsDefined hagrees
    have hargObjects : ∀ v ∈ args,
        targetState.objects (rename v) = source.objects v := by
      intro v hv
      apply hobjects (.op ⟨0, isLt⟩ (.call none target selector args)) (by simp)
        v
      rw [Stmt.vars]
      change v ∈ ([] : List LocalVar) ++ args
      simpa using hv
    have hcalleeObjects : BodyObjectsAgree fn.body calleeRename calleeSource
        targetState := by
      simpa [calleeSource] using bodyObjectsAgree_bindArgs_inlineVar fn rename
        args next hargs source targetState hargObjects hempty
    have hcalleeEmpty : EmptyObjectsAbove
        (next + CallErasure.funcVarBound fn) targetState := by
      intro v hv
      exact hempty v (Nat.le_trans (Nat.le_add_right next _) hv)
    rcases ihCallee (fun v => decide (v < fn.numParams)) fn.wf_ssa fn.wf_caps
        hcalleeRen hcalleeBelow (calleeBody, afterCallee) hcallee
        calleeSource targetState hcalleeInitial hcalleeObjects hcalleeEmpty with
      ⟨htruthCallee, hagreeCallee, hemptyCallee⟩
    have hreservedAfter : next + CallErasure.funcVarBound fn ≤ afterCallee :=
      CallErasure.eraseBodyInto_next_mono
        (CallErasure.objectFeltConstrainSyntax (F := F))
        CallErasure.objectFeltConstrainReturnMonotone m caller
        (Call.moduleTarget target current.isLt) .constrain calleeRename
        (next + CallErasure.funcVarBound fn) fn.body
        (calleeBody, afterCallee) hcallee
    have hnextAfter : next ≤ afterCallee :=
      Nat.le_trans (Nat.le_add_right next _) hreservedAfter
    have hcalleeAbove : CallErasure.DestinationsAbove next calleeBody := by
      apply CallErasure.eraseBodyInto_destinationsAbove
        (CallErasure.objectFeltConstrainSyntax (F := F))
        CallErasure.objectFeltConstrainRenameStable
        CallErasure.objectFeltConstrainReturnMonotone
        CallErasure.objectFeltConstrainReturnFrame m caller
        (Call.moduleTarget target current.isLt) .constrain calleeRename
        (next + CallErasure.funcVarBound fn) next fn.body
        (calleeBody, afterCallee)
      · exact Nat.le_add_right next _
      · intro stmt hmem dest hdest
        exact CallPass.inlineVar_stmt_dest_ge_base fn rename args next hargs
          hmem hdest
      · exact hcallee
    let sourceAfterCall : State F := {
      source with
      witness := (TypedSourceSemantics.evalProjectedBodyIn m
        (Call.moduleTarget target current.isLt) calleeSource fn.body).1.witness
      nextPath := (TypedSourceSemantics.evalProjectedBodyIn m
        (Call.moduleTarget target current.isLt) calleeSource fn.body).1.nextPath
    }
    have hcallerAfter : StateAgreesOn defined rename sourceAfterCall
        (evalTargetBody calleeBody targetState).1 := by
      constructor
      · intro v hv
        change (evalTargetBody calleeBody targetState).1.values (rename v) =
          source.values v
        rw [evalTargetBody_values_frame_below calleeBody next (rename v)
          targetState hcalleeAbove (hbelow v hv)]
        exact hagrees.values v hv
      · exact hagreeCallee.witness
      · exact hagreeCallee.nextPath
    have htailObjects : BodyObjectsAgree rest rename sourceAfterCall
        (evalTargetBody calleeBody targetState).1 := by
      intro stmt hmem v hv
      change (evalTargetBody calleeBody targetState).1.objects (rename v) =
        source.objects v
      rw [evalTargetBody_objects_frame_below calleeBody next (rename v)
        targetState hcalleeAbove (hren.1 stmt (by simp [hmem]) v hv)]
      exact hobjects stmt (by simp [hmem]) v hv
    have htailRen := hren.tail.mono hnextAfter
    have htailBelow : ∀ v, defined v = true → rename v < afterCallee := by
      intro v hv
      exact Nat.lt_of_lt_of_le (hbelow v hv) hnextAfter
    rcases ihTail defined hparts.2 htailCaps htailRen htailBelow
        (tail, afterTail) htail sourceAfterCall
        (evalTargetBody calleeBody targetState).1 hcallerAfter htailObjects
        hemptyCallee with ⟨htruthTail, hagreeTail, hemptyTail⟩
    have hselectorZero : selector = 0 := by
      simpa [Call.selectorSupported] using hselector
    constructor
    · rw [evalTargetBody_append]
      rw [TypedSourceSemantics.evalProjectedBodyIn.eq_def]
      simp only [hselectorZero, if_true]
      exact congrArg₂ (· && ·) htruthCallee htruthTail
    · constructor
      · rw [evalTargetBody_append]
        rw [TypedSourceSemantics.evalProjectedBodyIn.eq_def]
        simp only [hselectorZero, if_true]
        simpa [CallPass.definedLocalsAfter, sourceAfterCall, calleeSource, fn]
          using hagreeTail
      · rw [evalTargetBody_append]
        exact hemptyTail
  · simp only [motive]
    unfold ConstrainErasureSimulation
    intros _ current rename next rest isLt target selector args hselector
      hargsFalse defined hssa hcaps hren hbelow result herase
    rw [CallErasure.eraseBodyInto.eq_def] at herase
    simp [hselector, hargsFalse] at herase
  · simp only [motive]
    unfold ConstrainErasureSimulation
    intros _ current kind rename next rest isLt dest target selector args
      hselectorFalse
    cases kind
    · trivial
    · intro defined hssa hcaps hren hbelow result herase
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hselectorFalse] at herase
  · simp only [motive]
    intros _ current kind rename next rest index hindex payload hlowerNone
    cases kind
    · trivial
    · unfold ConstrainErasureSimulation
      intro defined hssa hcaps hren hbelow result herase
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hlowerNone] at herase
  · simp only [motive]
    intros _ current kind rename next rest index hindex lowered htailNone payload
      hlower ih
    cases kind
    · trivial
    · unfold ConstrainErasureSimulation
      intro defined hssa hcaps hren hbelow result herase
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hlower, htailNone] at herase
  · simp only [motive]
    intros currentMembers' current kind rename next rest index hindex lowered
      tail afterTail htail payload hlower ih
    cases kind
    · trivial
    · unfold ConstrainErasureSimulation
      intro defined hssa hcaps hren hbelow result herase source targetState
        hagrees hobjects hempty
      rw [CallErasure.eraseBodyInto.eq_def] at herase
      simp [hlower, htail] at herase
      subst result
      let d : Fin TargetSet.length := ⟨index, by
        simp [SourceSet] at hindex
        simp [TargetSet]
        omega⟩
      let sourceStmt : Stmt SourceSet
          ⟨n, current.val, currentMembers'⟩ F :=
        .op ⟨index + 1, hindex⟩ payload
      have hdestSource : sourceStmt.dest = (TargetSet.get d).dest payload := rfl
      have hparts := CallPass.isSSA_cons_parts defined sourceStmt rest hssa
      rw [hdestSource] at hparts
      have htailCaps := capsLE_tail hcaps
      have hcap : (TargetSet.get d).cap payload ≤ .constraint := by
        simpa [sourceStmt] using
          (Dialect.cap_le_of_capsLE hcaps (stmt := sourceStmt)
            (by simp [sourceStmt]))
      have hfresh : ∀ dest, (TargetSet.get d).dest payload = some dest →
          defined dest = false := by
        intro dest hdest
        apply isSSA_cons_dest_fresh defined sourceStmt rest dest hssa
        simpa [hdestSource] using hdest
      have hseparate : ∀ dest, (TargetSet.get d).dest payload = some dest →
          ∀ v, v ≠ dest → rename v ≠ rename dest := by
        intro dest hdest v hv
        apply hren.2 sourceStmt (by simp [sourceStmt]) dest
        · simpa [hdestSource] using hdest
        · exact hv
      have hreadObjects : ∀ v ∈ (TargetSet.get d).reads payload,
          targetState.objects (rename v) = source.objects v := by
        intro v hv
        apply hobjects sourceStmt (by simp [sourceStmt]) v
        rw [Stmt.vars]
        apply List.mem_append_right
        simpa [sourceStmt] using hv
      have hstep := evalProjectedLeaf_lowerResidualStmt rename d payload lowered
        (by simpa [d] using hlower) defined hparts.1 hcap hfresh hseparate
        source targetState hreadObjects hagrees
      have htailObjects := bodyObjectsAgree_lowerResidualStmt rename d payload
        rest lowered (by simpa [d] using hlower) hcap hseparate source targetState
        (by simpa [sourceStmt, d] using hobjects)
      have hsingleBelow : DestinationsBelow next [lowered] := by
        intro stmt hmem dest hdest
        simp only [List.mem_singleton] at hmem
        subst stmt
        have hsourceDest := CallErasure.lowerResidualStmt_dest
          (CallErasure.objectFeltConstrainSyntax (F := F))
          CallErasure.objectFeltConstrainRenameStable rename d payload lowered
          (by simpa [d] using hlower)
        rw [hsourceDest] at hdest
        cases hpayloadDest : (TargetSet.get d).dest payload with
        | none => rw [hpayloadDest] at hdest; contradiction
        | some sourceDest =>
          simp only [hpayloadDest, Option.map_some, Option.some.injEq] at hdest
          subst dest
          apply hren.1 sourceStmt (by simp [sourceStmt]) sourceDest
          rw [Stmt.vars]
          apply List.mem_append_left
          change sourceDest ∈ ((TargetSet.get d).dest payload).toList
          rw [hpayloadDest]
          simp
      have hemptyStep : EmptyObjectsAbove next
          (TypedSourceSemantics.evalProjectedLeaf lowered targetState).1 := by
        simpa [evalTargetBody] using evalTargetBody_emptyObjectsAbove [lowered]
          next next targetState hempty (Nat.le_refl next) hsingleBelow
      have hextendDefined :
          extendDefined defined ((TargetSet.get d).dest payload) =
            match (TargetSet.get d).dest payload with
            | some dest => fun v => defined v || v == dest
            | none => defined := by
        cases (TargetSet.get d).dest payload <;> rfl
      have htailSSA : isSSA
          (extendDefined defined ((TargetSet.get d).dest payload)) rest = true := by
        rw [hextendDefined]
        exact hparts.2
      rcases ih (extendDefined defined ((TargetSet.get d).dest payload))
          htailSSA htailCaps hren.tail
          (fun v hv => by
            simp only [extendDefined] at hv
            cases hpayloadDest : (TargetSet.get d).dest payload with
            | none =>
              rw [hpayloadDest] at hv
              exact hbelow v hv
            | some assigned =>
              rw [hpayloadDest] at hv
              simp only [Bool.or_eq_true, beq_iff_eq] at hv
              rcases hv with hv | rfl
              · exact hbelow v hv
              · apply hren.1 sourceStmt (by simp [sourceStmt]) v
                rw [Stmt.vars]
                apply List.mem_append_left
                change v ∈ ((TargetSet.get d).dest payload).toList
                rw [hpayloadDest]
                simp)
          (tail, afterTail) htail
          (TypedSourceSemantics.evalProjectedLeaf (.op d payload) source).1
          (TypedSourceSemantics.evalProjectedLeaf lowered targetState).1
          hstep.2 htailObjects hemptyStep with
        ⟨htruthTail, hagreeTail, hemptyTail⟩
      constructor
      · rw [evalTargetBody, TypedSourceSemantics.evalProjectedBodyIn.eq_def]
        exact congrArg₂ (· && ·) hstep.1 htruthTail
      · constructor
        · rw [evalTargetBody, TypedSourceSemantics.evalProjectedBodyIn.eq_def]
          rw [hextendDefined] at hagreeTail
          simpa [CallPass.definedLocalsAfter, sourceStmt, hdestSource, d]
            using hagreeTail
        · simpa [evalTargetBody] using hemptyTail

/-- Selected-function Call certificate over canonical finite inputs. -/
theorem eraseConstrainFunc_checkProjectedAt_eq [Field F] [DecidableEq F]
    {n : Nat} (m : Module SourceSet n F) (entry : Fin n)
    (result : List (Stmt TargetSet
      ⟨n, entry.val, (m.structs entry).members.length⟩ F) × LocalVar)
    (herase : CallErasure.eraseConstrainFunc
      (CallErasure.objectFeltConstrainSyntax (F := F)) m entry = some result)
    (inputs objects : List F) :
    (evalTargetBody result.1
      (TypedSourceSemantics.initialState
        (m.structs entry).constrain.numParams
        (m.structs entry).compute.numParams inputs objects)).2 =
      TypedSourceSemantics.checkProjectedAt m entry inputs objects := by
  let fn := (m.structs entry).constrain
  let initial := TypedSourceSemantics.initialState fn.numParams
    (m.structs entry).compute.numParams inputs objects
  have hagrees : StateAgreesOn (fun v => decide (v < fn.numParams)) id
      initial initial := ⟨fun _ _ => rfl, rfl, rfl⟩
  have hbodyObjects : BodyObjectsAgree fn.body id initial initial := by
    intro _ _ _ _
    rfl
  have hempty : EmptyObjectsAbove (CallErasure.funcVarBound fn) initial := by
    intro v hv
    simp [initial, TypedSourceSemantics.initialState,
      StructObject.ObjEnv.update]
  have hsim := eraseBodyInto_constrain_simulation m entry entry id
    (CallErasure.funcVarBound fn) fn.body
    (fun v => decide (v < fn.numParams)) fn.wf_ssa fn.wf_caps
    (CallPass.renameInvariant_id fn).body
    (fun v hv => by
      have hvlt : v < fn.numParams := by simpa using hv
      exact Nat.lt_of_lt_of_le hvlt (CallPass.numParams_le_funcVarBound fn))
    result (by simpa [CallErasure.eraseConstrainFunc, fn] using herase)
    initial initial hagrees hbodyObjects hempty
  simpa [TypedSourceSemantics.checkProjectedAt, initial, fn] using hsim.1

/-- Pointwise Oracle→Call structural-prefix evidence. -/
structure PrefixCertificate [Field F] {n : Nat}
    (source : Module OracleErasure.SourceSet n F) (entry : Fin n) where
  projected : Module SourceSet n F
  oracleErasure : OracleErasure.lowerModule source = .ok projected
  callFree : List (Stmt TargetSet
    ⟨n, entry.val, (projected.structs entry).members.length⟩ F) × LocalVar
  callErasure : CallErasure.eraseConstrainFunc
    (CallErasure.objectFeltConstrainSyntax (F := F)) projected entry = some callFree

/-- Successful Oracle projection followed by selected Call expansion preserves
the original full typed-source Boolean observation. -/
theorem structuralPrefix_check_eq [Field F] [DecidableEq F]
    {n : Nat} (source : Module OracleErasure.SourceSet n F) (entry : Fin n)
    (certificate : PrefixCertificate source entry) (inputs objects : List F) :
    (evalTargetBody certificate.callFree.1
      (TypedSourceSemantics.initialState
        (certificate.projected.structs entry).constrain.numParams
        (certificate.projected.structs entry).compute.numParams
        inputs objects)).2 =
      TypedSourceSemantics.checkAt source entry inputs objects := by
  exact (eraseConstrainFunc_checkProjectedAt_eq certificate.projected entry
    certificate.callFree certificate.callErasure inputs objects).trans
      (OracleErasure.checkAt_eq_checkProjectedAt source certificate.projected
        certificate.oracleErasure entry inputs objects).symm

/-- Structural prefix preserves and reflects satisfaction at selected entry. -/
theorem structuralPrefix_satisfies_iff [Field F] [DecidableEq F]
    {n : Nat} (source : Module OracleErasure.SourceSet n F) (entry : Fin n)
    (certificate : PrefixCertificate source entry) (inputs objects : List F) :
    (ObjectResidualSemantics.evalBody certificate.callFree.1
      (TypedSourceSemantics.initialState
        (certificate.projected.structs entry).constrain.numParams
        (certificate.projected.structs entry).compute.numParams
        inputs objects)).2 ↔
      TypedSourceSemantics.satisfiesAt source entry inputs objects := by
  rw [← TypedSourceSemantics.checkAt_true_iff]
  rw [← structuralPrefix_check_eq source entry certificate inputs objects]
  exact (evalTargetBody_true_iff certificate.callFree.1 _).symm

end Dialect.ObjectCallSemantics
