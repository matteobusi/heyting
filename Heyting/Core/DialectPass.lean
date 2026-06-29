/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Module
import Heyting.Core.ModuleSemantics
import Heyting.Core.Semantics

/-!
# Generic Dialect Passes

Phase-0 body-level macro-expansion theorem for dialect ops.

A lowering maps each source op into a list of target statements. If each op's
lowering simulates the source op in constrain and compute semantics, then
lowering a whole body preserves constrain satisfaction and compute results.
-/

namespace Dialect

variable {F : Type} [Field F]

/-! ## Body lowering -/

/--
Lower a statement list by replacing each dialect op with the result of
`lowerOp`.

`lowerOp` is generic over `OpCtx` so it can be used in any body; Lean infers
`γ` at each call site from the op's type.
-/
def lowerBody
    {Δ Δ' : DialectSet}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F))
    {γ : OpCtx} : List (Stmt Δ γ F) → List (Stmt Δ' γ F)
  | [] => []
  | .op d p :: rest => lowerOp d p ++ lowerBody lowerOp rest

omit [Field F] in
@[simp] theorem lowerBody_nil
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F)) :
    lowerBody lowerOp ([] : List (Stmt Δ γ F)) = [] := rfl

omit [Field F] in
@[simp] theorem lowerBody_op
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F))
    (d : Fin Δ.length) (p : (Δ.get d).Op γ F) (rest : List (Stmt Δ γ F)) :
    lowerBody lowerOp (.op d p :: rest) = lowerOp d p ++ lowerBody lowerOp rest := rfl

/-! ## Fresh-variable support -/

/-- Variables mentioned by a statement: destination, if present, followed by reads. -/
def Stmt.vars {Δ : DialectSet} {γ : OpCtx} {F : Type} (s : Stmt Δ γ F) : List LocalVar :=
  s.dest.toList ++ s.reads

/-- A statement only mentions variables strictly below `next`. -/
def Stmt.freshAbove {Δ : DialectSet} {γ : OpCtx} {F : Type}
    (next : LocalVar) (s : Stmt Δ γ F) : Prop :=
  ∀ v, v ∈ s.vars → v < next

/-- A body only mentions variables strictly below `next`. -/
def bodyFreshAbove {Δ : DialectSet} {γ : OpCtx} {F : Type}
    (next : LocalVar) (body : List (Stmt Δ γ F)) : Prop :=
  ∀ s, s ∈ body → s.freshAbove next

/-- Computable strict upper bound for a list of locals. -/
def maxVarList : List LocalVar → LocalVar
  | [] => 0
  | v :: vs => max (v + 1) (maxVarList vs)

/-- Computable strict upper bound for variables mentioned by one statement. -/
def Stmt.maxVar {Δ : DialectSet} {γ : OpCtx} {F : Type} (s : Stmt Δ γ F) : LocalVar :=
  maxVarList s.vars

/-- Computable strict upper bound for variables mentioned by a body. -/
def maxVarBody {Δ : DialectSet} {γ : OpCtx} {F : Type} : List (Stmt Δ γ F) → LocalVar
  | [] => 0
  | s :: rest => max s.maxVar (maxVarBody rest)

omit [Field F] in
theorem lt_maxVarList_of_mem {v : LocalVar} : ∀ {vs : List LocalVar},
    v ∈ vs → v < maxVarList vs
  | [], h => by cases h
  | x :: xs, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_maxVarList_of_mem h) (Nat.le_max_right _ _)

omit [Field F] in
theorem Stmt.freshAbove_mono
    {Δ : DialectSet} {γ : OpCtx} {F : Type} {next next' : LocalVar}
    {s : Stmt Δ γ F} (h : s.freshAbove next) (hle : next ≤ next') :
    s.freshAbove next' := by
  intro v hv
  exact Nat.lt_of_lt_of_le (h v hv) hle

omit [Field F] in
theorem Stmt.freshAbove_maxVar {Δ : DialectSet} {γ : OpCtx} {F : Type}
    (s : Stmt Δ γ F) : s.freshAbove s.maxVar := by
  intro v hv
  exact lt_maxVarList_of_mem hv

omit [Field F] in
theorem bodyFreshAbove_maxVarBody {Δ : DialectSet} {γ : OpCtx} {F : Type}
    (body : List (Stmt Δ γ F)) : bodyFreshAbove (maxVarBody body) body := by
  induction body with
  | nil => intro s hs; cases hs
  | cons hd rest ih =>
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Stmt.freshAbove_mono (Stmt.freshAbove_maxVar t) (Nat.le_max_left _ _)
    · exact Stmt.freshAbove_mono (ih t ht) (Nat.le_max_right _ _)

omit [Field F] in
theorem bodyFreshAbove_cons
    {Δ : DialectSet} {γ : OpCtx} {F : Type} {next : LocalVar}
    {s : Stmt Δ γ F} {rest : List (Stmt Δ γ F)} :
    bodyFreshAbove next (s :: rest) ↔ s.freshAbove next ∧ bodyFreshAbove next rest := by
  constructor
  · intro h
    constructor
    · exact h s (by simp)
    · intro t ht
      exact h t (by simp [ht])
  · rintro ⟨hs, hrest⟩ t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hs
    · exact hrest t ht

omit [Field F] in
theorem bodyFreshAbove_mono
    {Δ : DialectSet} {γ : OpCtx} {F : Type} {next next' : LocalVar}
    {body : List (Stmt Δ γ F)} (h : bodyFreshAbove next body) (hle : next ≤ next') :
    bodyFreshAbove next' body := by
  intro s hs
  exact Stmt.freshAbove_mono (h s hs) hle

omit [Field F] in
theorem Stmt.read_lt_of_freshAbove
    {Δ : DialectSet} {γ : OpCtx} {F : Type}
    {next v : LocalVar} {s : Stmt Δ γ F}
    (hfresh : s.freshAbove next)
    (hv : v ∈ s.reads) :
    v < next :=
  hfresh v (by simp [Stmt.vars, hv])

omit [Field F] in
theorem Stmt.dest_lt_of_freshAbove
    {Δ : DialectSet} {γ : OpCtx} {F : Type}
    {next d : LocalVar} {s : Stmt Δ γ F}
    (hfresh : s.freshAbove next)
    (hd : s.dest = some d) :
    d < next :=
  hfresh d (by simp [Stmt.vars, hd])

/-! ## SSA helper lemmas -/

theorem evalConstrainStep_agree_below
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F)
    (next : LocalVar)
    (env₁ env₂ : LocalVar → F)
    (hfresh : s.freshAbove next)
    (hagree : ∀ v, v < next → env₁ v = env₂ v) :
    ((evalConstrainStep handlers s env₁).2 ↔
      (evalConstrainStep handlers s env₂).2) ∧
    ∀ v, v < next →
      (evalConstrainStep handlers s env₁).1 v =
        (evalConstrainStep handlers s env₂).1 v := by
  cases s with
  | op d p =>
      have hreads : ∀ v, v ∈ (Δ.get d).reads p → env₁ v = env₂ v := by
        intro v hv
        exact hagree v (Stmt.read_lt_of_freshAbove hfresh hv)
      obtain ⟨hprop, hdest⟩ := (handlers d).constrainStep_reads_congr p env₁ env₂ hreads
      constructor
      · exact hprop
      · intro v hv
        by_cases hd : (Δ.get d).dest p = some v
        · change ((handlers d).constrainStep p env₁).1 v =
            ((handlers d).constrainStep p env₂).1 v
          exact hdest v hd
        · change ((handlers d).constrainStep p env₁).1 v =
            ((handlers d).constrainStep p env₂).1 v
          rw [(handlers d).constrainStep_frame p env₁ v hd,
            (handlers d).constrainStep_frame p env₂ v hd]
          exact hagree v hv

/-! ## Environment agreement helpers -/

/-- Theorems below let suffix proofs ignore fresh temporaries above `next`. -/
theorem evalConstrainBodyEnv_agree_below
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) :
    ∀ (body : List (Stmt Δ γ F)) (next : LocalVar)
      (env₁ env₂ : LocalVar → F),
      bodyFreshAbove next body →
      (∀ v, v < next → env₁ v = env₂ v) →
      (evalConstrainBody handlers body env₁ ↔
        evalConstrainBody handlers body env₂) ∧
      (∀ v, v < next →
        evalConstrainEnv handlers body env₁ v =
          evalConstrainEnv handlers body env₂ v)
  | [], _, env₁, env₂, _, hagree => by
      constructor
      · simp
      · exact hagree
  | s :: rest, next, env₁, env₂, hfresh, hagree => by
      obtain ⟨hs, hrest⟩ := bodyFreshAbove_cons.mp hfresh
      obtain ⟨hstepProp, hstepEnv⟩ :=
        evalConstrainStep_agree_below handlers s next env₁ env₂ hs hagree
      obtain ⟨hrestProp, hrestEnv⟩ :=
        evalConstrainBodyEnv_agree_below handlers rest next
          (evalConstrainStep handlers s env₁).1
          (evalConstrainStep handlers s env₂).1
          hrest hstepEnv
      constructor
      · simp [evalConstrainBody_cons, hstepProp, hrestProp]
      · intro v hv
        simp [evalConstrainEnv_cons, hrestEnv v hv]

theorem evalConstrainBody_agree_below
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (body : List (Stmt Δ γ F))
    (next : LocalVar)
    (env₁ env₂ : LocalVar → F)
    (hfresh : bodyFreshAbove next body)
    (hagree : ∀ v, v < next → env₁ v = env₂ v) :
    evalConstrainBody handlers body env₁ ↔
      evalConstrainBody handlers body env₂ :=
  (evalConstrainBodyEnv_agree_below handlers body next env₁ env₂ hfresh hagree).1

theorem evalConstrainEnv_agree_below
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (body : List (Stmt Δ γ F))
    (next : LocalVar)
    (env₁ env₂ : LocalVar → F)
    (hfresh : bodyFreshAbove next body)
    (hagree : ∀ v, v < next → env₁ v = env₂ v) :
    ∀ v, v < next →
      evalConstrainEnv handlers body env₁ v =
        evalConstrainEnv handlers body env₂ v :=
  (evalConstrainBodyEnv_agree_below handlers body next env₁ env₂ hfresh hagree).2

set_option linter.flexible false in
theorem evalComputeStep_agree_below
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (s : Stmt Δ γ F)
    (next : LocalVar)
    (env₁ env₂ : LocalVar → F)
    (hfresh : s.freshAbove next)
    (hagree : ∀ v, v < next → env₁ v = env₂ v) :
    match evalComputeStep handlers s env₁,
        evalComputeStep handlers s env₂ with
    | some env₁', some env₂' => ∀ v, v < next → env₁' v = env₂' v
    | none, none => True
    | _, _ => False := by
  cases s with
  | op d p =>
      have hreads : ∀ v, v ∈ (Δ.get d).reads p → env₁ v = env₂ v := by
        intro v hv
        exact hagree v (Stmt.read_lt_of_freshAbove hfresh hv)
      have hstatus := (handlers d).computeStep_status_congr p env₁ env₂ hreads
      cases h₁ : (handlers d).computeStep p env₁ <;>
        cases h₂ : (handlers d).computeStep p env₂
      · simp [evalComputeStep, h₁, h₂]
      · simp [h₁, h₂] at hstatus
      · simp [h₁, h₂] at hstatus
      · simp [evalComputeStep, h₁, h₂]
        intro v hv
        by_cases hd : (Δ.get d).dest p = some v
        · have hdest := (handlers d).computeStep_reads_congr p env₁ env₂ hreads v hd
          simp [h₁, h₂] at hdest
          exact hdest
        · have hframe₁ := (handlers d).computeStep_frame p env₁ _ v h₁ hd
          have hframe₂ := (handlers d).computeStep_frame p env₂ _ v h₂ hd
          rw [hframe₁, hframe₂]
          exact hagree v hv

set_option linter.flexible false in
theorem evalComputeBody_agree_below
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F) :
    ∀ (body : List (Stmt Δ γ F)) (next : LocalVar)
      (env₁ env₂ : LocalVar → F),
      bodyFreshAbove next body →
      (∀ v, v < next → env₁ v = env₂ v) →
      match evalComputeBody handlers body env₁,
          evalComputeBody handlers body env₂ with
      | some env₁', some env₂' => ∀ v, v < next → env₁' v = env₂' v
      | none, none => True
      | _, _ => False
  | [], _, env₁, env₂, _, hagree => by
      exact hagree
  | s :: rest, next, env₁, env₂, hfresh, hagree => by
      obtain ⟨hs, hrest⟩ := bodyFreshAbove_cons.mp hfresh
      have hstep := evalComputeStep_agree_below handlers s next env₁ env₂ hs hagree
      simp only [evalComputeBody_cons]
      cases h₁ : evalComputeStep handlers s env₁ <;>
        cases h₂ : evalComputeStep handlers s env₂
      · trivial
      · simp [h₁, h₂] at hstep
      · simp [h₁, h₂] at hstep
      · simp [h₁, h₂] at hstep
        exact evalComputeBody_agree_below handlers rest next _ _ hrest (by
          intro v hv
          exact hstep v hv)

/-! ## SSA helper lemmas -/


/-- Two initial-defined predicates agree on every variable mentioned by a body. -/
def bodyInitAgree {Δ : DialectSet} {γ : OpCtx} {F : Type}
    (init init' : LocalVar → Bool) (body : List (Stmt Δ γ F)) : Prop :=
  ∀ s, s ∈ body → ∀ v, v ∈ s.vars → init v = init' v

omit [Field F] in
theorem list_all_congr_bool {l : List LocalVar} {p q : LocalVar → Bool}
    (h : ∀ v, v ∈ l → p v = q v) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x (by simp)]
    exact congrArg (fun b => q x && b) (ih (by
      intro v hv
      exact h v (by simp [hv])))

omit [Field F] in
theorem isSSA_congr_init {Δ : DialectSet} {γ : OpCtx} {F : Type}
    {init init' : LocalVar → Bool} : ∀ (body : List (Stmt Δ γ F)),
    bodyInitAgree init init' body → isSSA init body = isSSA init' body
  | [] => by intro _; rfl
  | s :: rest => by
    intro hagree
    have hs : ∀ v, v ∈ s.vars → init v = init' v := hagree s (by simp)
    have hrest : bodyInitAgree init init' rest := by
      intro t ht v hv
      exact hagree t (by simp [ht]) v hv
    simp only [isSSA]
    have hreads : s.reads.all init = s.reads.all init' := by
      apply list_all_congr_bool
      intro v hv
      exact hs v (by simp [Stmt.vars, hv])
    rw [hreads]
    cases hd : s.dest with
    | none =>
      change (s.reads.all init' && isSSA init rest) =
        (s.reads.all init' && isSSA init' rest)
      exact congrArg (fun b => s.reads.all init' && b) (isSSA_congr_init rest hrest)
    | some d =>
      have hdagree : init d = init' d := hs d (by simp [Stmt.vars, hd])
      change (s.reads.all init' && (!init d && isSSA (fun x => init x || x == d) rest)) =
        (s.reads.all init' && (!init' d && isSSA (fun x => init' x || x == d) rest))
      rw [hdagree]
      apply congrArg (fun b => s.reads.all init' && (!init' d && b))
      apply isSSA_congr_init
      intro t ht v hv
      have hvagree := hrest t ht v hv
      by_cases hveq : v = d
      · subst v
        simp
      · simp [hvagree]

/-! ## Fresh body lowering -/

/-- Fresh-aware op lowering. The returned local is the next unused variable. -/
abbrev FreshLowerOp (Δ Δ' : DialectSet) (F : Type) :=
  ∀ {γ : OpCtx} (_next : LocalVar) (d : Fin Δ.length),
    (Δ.get d).Op γ F → List (Stmt Δ' γ F) × LocalVar

/-- Lower a statement list while threading a fresh-local counter. -/
def lowerBodyFresh
    {Δ Δ' : DialectSet}
    (lowerOp : FreshLowerOp Δ Δ' F)
    {γ : OpCtx} (next : LocalVar) :
    List (Stmt Δ γ F) → List (Stmt Δ' γ F) × LocalVar
  | [] => ([], next)
  | .op d p :: rest =>
    let r := lowerOp next d p
    let r' := lowerBodyFresh lowerOp r.2 rest
    (r.1 ++ r'.1, r'.2)

omit [Field F] in
@[simp] theorem lowerBodyFresh_nil
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (lowerOp : FreshLowerOp Δ Δ' F) (next : LocalVar) :
    lowerBodyFresh lowerOp (γ := γ) next [] = ([], next) := rfl

omit [Field F] in
@[simp] theorem lowerBodyFresh_op
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (lowerOp : FreshLowerOp Δ Δ' F) (next : LocalVar)
    (d : Fin Δ.length) (p : (Δ.get d).Op γ F) (rest : List (Stmt Δ γ F)) :
    lowerBodyFresh lowerOp next (.op d p :: rest) =
      let r := lowerOp next d p
      let r' := lowerBodyFresh lowerOp r.2 rest
      (r.1 ++ r'.1, r'.2) := rfl

/-! ## Append lemmas -/

/-- Constrain body over a concatenated list splits into two sequential evaluations. -/
theorem evalConstrainBody_append
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (l1 l2 : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalConstrainBody handlers (l1 ++ l2) env ↔
    evalConstrainBody handlers l1 env ∧
    evalConstrainBody handlers l2 (evalConstrainEnv handlers l1 env) := by
  induction l1 generalizing env with
  | nil => simp
  | cons s rest ih =>
    simp only [List.cons_append, evalConstrainBody_cons, evalConstrainEnv_cons, ih]
    tauto

/-- Compute body over a concatenated list faults if the first half faults. -/
theorem evalComputeBody_append
    {Δ : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (l1 l2 : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalComputeBody handlers (l1 ++ l2) env =
    (evalComputeBody handlers l1 env).bind (evalComputeBody handlers l2) := by
  induction l1 generalizing env with
  | nil => simp
  | cons s rest ih =>
    simp only [List.cons_append, evalComputeBody_cons, Option.bind_assoc]
    congr 1; funext e; exact ih e

/-! ## Simple pass simulation conditions -/

/--
Per-op constrain-context simulation condition.

For each dialect `d`, op `op`, and env `env`, the lowered op list must produce
the same final env (`.1`) and the same constraint (`.2`) as the original
`constrainStep`.
-/
def SimpleConstrainSim
    {Δ Δ' : DialectSet}
    (handlers : HandlerFamily Δ F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F))
    (handlers' : HandlerFamily Δ' F) : Prop :=
  ∀ {γ : OpCtx} (d : Fin Δ.length) (op : (Δ.get d).Op γ F)
    (env : LocalVar → F),
    evalConstrainEnv handlers' (lowerOp d op) env =
      ((handlers d).constrainStep op env).1 ∧
    (evalConstrainBody handlers' (lowerOp d op) env ↔
      ((handlers d).constrainStep op env).2)

/--
Per-op compute-context simulation condition.

For each dialect `d`, op `op`, and env, the lowered op list must produce the
same `Option (LocalVar → F)` as `computeStep`.
-/
def SimpleComputeSim
    {Δ Δ' : DialectSet}
    (handlers : HandlerFamily Δ F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F))
    (handlers' : HandlerFamily Δ' F) : Prop :=
  ∀ {γ : OpCtx} (d : Fin Δ.length) (op : (Δ.get d).Op γ F)
    (env : LocalVar → F),
    evalComputeBody handlers' (lowerOp d op) env =
      (handlers d).computeStep op env

/-! ## Fresh pass simulation conditions -/

/-- Per-op constrain-context simulation for a fresh-aware lowering.

The lowered chunk may write fresh temporaries, so final environments only need to
agree below the incoming fresh counter. -/
def FreshConstrainSim
    {Δ Δ' : DialectSet}
    (handlers : HandlerFamily Δ F)
    (lowerOp : FreshLowerOp Δ Δ' F)
    (handlers' : HandlerFamily Δ' F) : Prop :=
  ∀ {γ : OpCtx} (next : LocalVar) (d : Fin Δ.length) (op : (Δ.get d).Op γ F)
    (env : LocalVar → F),
    Stmt.freshAbove next (.op d op : Stmt Δ γ F) →
    (∀ v, v < next →
      evalConstrainEnv handlers' (lowerOp next d op).1 env v =
        ((handlers d).constrainStep op env).1 v) ∧
    (evalConstrainBody handlers' (lowerOp next d op).1 env ↔
      ((handlers d).constrainStep op env).2)

/-- Per-op compute-context simulation for a fresh-aware lowering.

On success, output environments agree below the incoming fresh counter. -/
def FreshComputeSim
    {Δ Δ' : DialectSet}
    (handlers : HandlerFamily Δ F)
    (lowerOp : FreshLowerOp Δ Δ' F)
    (handlers' : HandlerFamily Δ' F) : Prop :=
  ∀ {γ : OpCtx} (next : LocalVar) (d : Fin Δ.length) (op : (Δ.get d).Op γ F)
    (env : LocalVar → F),
    Stmt.freshAbove next (.op d op : Stmt Δ γ F) →
    match evalComputeBody handlers' (lowerOp next d op).1 env,
        (handlers d).computeStep op env with
    | some env', some env₀ => ∀ v, v < next → env' v = env₀ v
    | none, none => True
    | _, _ => False

/-- Fresh counters returned by each op lowering never move backwards. -/
def FreshLowerMono {Δ Δ' : DialectSet} (lowerOp : FreshLowerOp Δ Δ' F) : Prop :=
  ∀ {γ : OpCtx} (next : LocalVar) (d : Fin Δ.length) (op : (Δ.get d).Op γ F),
    next ≤ (lowerOp next d op).2

/-! ## simple macro-expansion theorem (body level) -/

/--
**Simple constrain theorem.** Under `SimpleConstrainSim`, lowering a constrain body
preserves the emitted constraint set (iff) for any initial environment.
-/
theorem simple_constrainBody
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (handlers' : HandlerFamily Δ' F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F))
    (sim : SimpleConstrainSim handlers lowerOp handlers')
    (stmts : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalConstrainBody handlers' (lowerBody lowerOp stmts) env ↔
    evalConstrainBody handlers stmts env := by
  induction stmts generalizing env with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | op d p =>
      simp only [lowerBody_op, evalConstrainBody_cons, evalConstrainStep]
      rw [evalConstrainBody_append]
      obtain ⟨env_eq, body_iff⟩ := sim d p env
      rw [env_eq, body_iff]
      exact and_congr Iff.rfl (ih _)

/--
**Simple compute theorem.** Under `SimpleComputeSim`, lowering a compute body preserves
the `Option (LocalVar → F)` result.
-/
theorem simple_computeBody
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (handlers' : HandlerFamily Δ' F)
    (lowerOp : ∀ {γ : OpCtx} (d : Fin Δ.length), (Δ.get d).Op γ F → List (Stmt Δ' γ F))
    (sim : SimpleComputeSim handlers lowerOp handlers')
    (stmts : List (Stmt Δ γ F)) (env : LocalVar → F) :
    evalComputeBody handlers' (lowerBody lowerOp stmts) env =
    evalComputeBody handlers stmts env := by
  induction stmts generalizing env with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | op d p =>
      simp only [lowerBody_op, evalComputeBody_cons, evalComputeStep]
      rw [evalComputeBody_append, sim d p env]
      congr 1; funext e; exact ih e

/-! ## fresh macro-expansion theorem (body level) -/

theorem fresh_constrainBody
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (handlers' : HandlerFamily Δ' F)
    (lowerOp : FreshLowerOp Δ Δ' F)
    (mono : FreshLowerMono lowerOp)
    (sim : FreshConstrainSim handlers lowerOp handlers')
    (body : List (Stmt Δ γ F))
    (next : LocalVar)
    (env : LocalVar → F)
    (hfresh : bodyFreshAbove next body) :
    evalConstrainBody handlers'
        (lowerBodyFresh lowerOp next body).1 env ↔
      evalConstrainBody handlers body env := by
  induction body generalizing next env with
  | nil => simp [lowerBodyFresh]
  | cons s rest ih =>
      obtain ⟨hs, hrest⟩ := bodyFreshAbove_cons.mp hfresh
      cases s with
      | op d p =>
          simp only [lowerBodyFresh_op, evalConstrainBody_cons]
          rw [evalConstrainBody_append]
          let r := lowerOp next d p
          obtain ⟨hbelow, hprop⟩ := sim next d p env hs
          have hmono : next ≤ r.2 := mono next d p
          have hrest' : bodyFreshAbove r.2 rest := bodyFreshAbove_mono hrest hmono
          have hih' := ih r.2 (evalConstrainEnv handlers' r.1 env) hrest'
          have hsrcTail :
              evalConstrainBody handlers rest (evalConstrainEnv handlers' r.1 env) ↔
                evalConstrainBody handlers rest ((handlers d).constrainStep p env).1 :=
            evalConstrainBody_agree_below handlers rest next
              (evalConstrainEnv handlers' r.1 env)
              ((handlers d).constrainStep p env).1
              hrest hbelow
          simpa [r, evalConstrainStep, hprop] using (and_congr Iff.rfl (hih'.trans hsrcTail))

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
set_option linter.style.longLine false in
theorem fresh_computeBody
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (handlers : HandlerFamily Δ F)
    (handlers' : HandlerFamily Δ' F)
    (lowerOp : FreshLowerOp Δ Δ' F)
    (mono : FreshLowerMono lowerOp)
    (sim : FreshComputeSim handlers lowerOp handlers')
    (body : List (Stmt Δ γ F))
    (next : LocalVar)
    (env : LocalVar → F)
    (hfresh : bodyFreshAbove next body) :
    match evalComputeBody handlers'
            (lowerBodyFresh lowerOp next body).1 env,
          evalComputeBody handlers body env with
    | some env', some env₀ => ∀ v, v < next → env' v = env₀ v
    | none, none => True
    | _, _ => False := by
  induction body generalizing next env with
  | nil =>
      intro v _
      rfl
  | cons s rest ih =>
      obtain ⟨hs, hrest⟩ := bodyFreshAbove_cons.mp hfresh
      cases s with
      | op d p =>
          let r := lowerOp next d p
          have hmono : next ≤ r.2 := mono next d p
          have hrest' : bodyFreshAbove r.2 rest := bodyFreshAbove_mono hrest hmono
          have hsim := sim next d p env hs
          simp only [lowerBodyFresh_op, evalComputeBody_append, evalComputeBody_cons,
            evalComputeStep]
          cases hlow : evalComputeBody handlers' r.1 env with
          | none =>
              cases hsrc : (handlers d).computeStep p env with
              | none => simp [r, hlow, hsrc]
              | some envS =>
                  simp [r, hlow, hsrc] at hsim
          | some envT =>
              cases hsrc : (handlers d).computeStep p env with
              | none =>
                  simp [r, hlow, hsrc] at hsim
              | some envS =>
                  simp [r, hlow, hsrc] at hsim
                  have hih := ih r.2 envT hrest'
                  have hsrcAgree := evalComputeBody_agree_below handlers rest next envT envS hrest hsim
                  cases htailTarget : evalComputeBody handlers' (lowerBodyFresh lowerOp r.2 rest).1 envT with
                  | none =>
                      cases htailSourceA : evalComputeBody handlers rest envT with
                      | none =>
                          cases htailSourceB : evalComputeBody handlers rest envS with
                          | none => exact by simp [r, htailTarget, htailSourceB]
                          | some envB => simp [htailSourceA, htailSourceB] at hsrcAgree
                      | some envA => simp [htailTarget, htailSourceA] at hih
                  | some envT' =>
                      cases htailSourceA : evalComputeBody handlers rest envT with
                      | none => simp [htailTarget, htailSourceA] at hih
                      | some envA =>
                          cases htailSourceB : evalComputeBody handlers rest envS with
                          | none => simp [htailSourceA, htailSourceB] at hsrcAgree
                          | some envB =>
                              simp [htailTarget, htailSourceA] at hih
                              simp [htailSourceA, htailSourceB] at hsrcAgree
                              exact by
                                simp [r, htailTarget, htailSourceB]
                                intro v hv
                                exact Eq.trans (hih v (Nat.lt_of_lt_of_le hv hmono)) (hsrcAgree v hv)

omit [Field F] in
theorem lowerBodyFresh_next_ge
    {Δ Δ' : DialectSet} {γ : OpCtx}
    (lowerOp : FreshLowerOp Δ Δ' F)
    (mono : FreshLowerMono lowerOp)
    (body : List (Stmt Δ γ F)) (next : LocalVar) :
    next ≤ (lowerBodyFresh lowerOp next body).2 := by
  induction body generalizing next with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | op d p =>
      simp only [lowerBodyFresh_op]
      exact Nat.le_trans (mono next d p) (ih (lowerOp next d p).2)

/-- Unified fresh-aware body/module-level dialect pass abstraction. -/
structure DialectPass (Δ Δ' : DialectSet) (F : Type) [Field F] where
  handlers  : HandlerFamily Δ F
  handlers' : HandlerFamily Δ' F
  lowerOp   : FreshLowerOp Δ Δ' F
  next_mono : FreshLowerMono lowerOp
  constrain : FreshConstrainSim handlers lowerOp handlers'
  compute   : FreshComputeSim handlers lowerOp handlers'
  startFresh : ∀ {γ : OpCtx} (_numParams : Nat) (_body : List (Stmt Δ γ F)), LocalVar
  startFresh_above : ∀ {γ : OpCtx} (numParams : Nat) (body : List (Stmt Δ γ F)),
    bodyFreshAbove (startFresh numParams body) body
  startFresh_init : ∀ {γ : OpCtx} (numParams : Nat) (body : List (Stmt Δ γ F))
      (v : LocalVar), startFresh numParams body ≤ v → ¬ v < numParams
  lower_caps : ∀ {γ : OpCtx} (k : Capability) (numParams : Nat) (body : List (Stmt Δ γ F)),
    capsLE k body = true →
      capsLE k (lowerBodyFresh lowerOp (startFresh numParams body) body).1 = true
  lower_ssa : ∀ {γ : OpCtx} (init : LocalVar → Bool) (next : LocalVar)
      (body : List (Stmt Δ γ F)),
    (∀ v, next ≤ v → init v = false) →
    bodyFreshAbove next body →
    isSSA init body = true →
      isSSA init (lowerBodyFresh lowerOp next body).1 = true

namespace DialectPass

/-- Apply a unified pass to a body, threading an explicit fresh counter. -/
def lowerBody {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F) {γ : OpCtx}
    (next : LocalVar) (body : List (Stmt Δ γ F)) : List (Stmt Δ' γ F) × LocalVar :=
  Dialect.lowerBodyFresh pass.lowerOp next body

/-- Lower a body using the pass's module-level fresh-start policy. -/
def lowerModuleBody {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F) {γ : OpCtx}
    (numParams : Nat) (body : List (Stmt Δ γ F)) : List (Stmt Δ' γ F) :=
  (pass.lowerBody (pass.startFresh numParams body) body).1

theorem constrainBody {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F) {γ : OpCtx}
    (body : List (Stmt Δ γ F))
    (next : LocalVar)
    (env : LocalVar → F)
    (hfresh : bodyFreshAbove next body) :
    evalConstrainBody pass.handlers' (pass.lowerBody next body).1 env ↔
      evalConstrainBody pass.handlers body env :=
  Dialect.fresh_constrainBody
    pass.handlers pass.handlers' pass.lowerOp pass.next_mono pass.constrain
    body next env hfresh

theorem computeBody {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F) {γ : OpCtx}
    (body : List (Stmt Δ γ F))
    (next : LocalVar)
    (env : LocalVar → F)
    (hfresh : bodyFreshAbove next body) :
    match evalComputeBody pass.handlers' (pass.lowerBody next body).1 env,
          evalComputeBody pass.handlers body env with
    | some env', some env₀ => ∀ v, v < next → env' v = env₀ v
    | none, none => True
    | _, _ => False :=
  Dialect.fresh_computeBody
    pass.handlers pass.handlers' pass.lowerOp pass.next_mono pass.compute
    body next env hfresh

theorem lowerBody_next_ge {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F) {γ : OpCtx}
    (stmts : List (Stmt Δ γ F)) (next : LocalVar) :
    next ≤ (pass.lowerBody next stmts).2 :=
  Dialect.lowerBodyFresh_next_ge pass.lowerOp pass.next_mono stmts next

def lowerFunc {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n i : Nat} {kind : Capability} {numMembers : Nat}
    (fn : FuncDef Δ n i F kind numMembers) : FuncDef Δ' n i F kind numMembers where
  numParams := fn.numParams
  body      := pass.lowerModuleBody fn.numParams fn.body
  returnVar := fn.returnVar
  wf_caps   := pass.lower_caps kind fn.numParams fn.body fn.wf_caps
  wf_ssa    := pass.lower_ssa (fun v => decide (v < fn.numParams))
    (pass.startFresh fn.numParams fn.body) fn.body
    (by
      intro v hv
      simp [pass.startFresh_init fn.numParams fn.body v hv])
    (pass.startFresh_above fn.numParams fn.body) fn.wf_ssa

def lowerStruct {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n : Nat} {i : Fin n} (s : StructDef Δ n i F) : StructDef Δ' n i F where
  name      := s.name
  members   := s.members
  compute   := pass.lowerFunc s.compute
  constrain := pass.lowerFunc s.constrain

def lowerModule {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n : Nat} (m : Module Δ n F) : Module Δ' n F where
  structs := fun i => pass.lowerStruct (m.structs i)

/-- Constraint-function semantics is preserved and reflected by a dialect pass. -/
theorem evalFuncConstrain_iff {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n i : Nat} {numMembers : Nat}
    (fn : FuncDef Δ n i F .constraint numMembers)
    (env : LocalVar → F) :
    evalFuncConstrain pass.handlers' (pass.lowerFunc fn) env ↔
      evalFuncConstrain pass.handlers fn env := by
  change evalConstrainBody pass.handlers'
      (pass.lowerModuleBody fn.numParams fn.body) env ↔
    evalConstrainBody pass.handlers fn.body env
  exact pass.constrainBody fn.body (pass.startFresh fn.numParams fn.body) env
    (pass.startFresh_above fn.numParams fn.body)

/-- Compute-function execution status is preserved by a dialect pass. -/
theorem evalFuncCompute_status {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n i : Nat} {numMembers : Nat}
    (fn : FuncDef Δ n i F .witness numMembers)
    (input : FuncInput F) (default : F) :
    (evalFuncCompute pass.handlers' (pass.lowerFunc fn) input default).isSome =
      (evalFuncCompute pass.handlers fn input default).isSome := by
  unfold evalFuncCompute
  simp only [Option.isSome_map]
  have h := pass.computeBody fn.body (pass.startFresh fn.numParams fn.body)
    (bindParams input.args default) (pass.startFresh_above fn.numParams fn.body)
  cases ht : evalComputeBody pass.handlers'
      (pass.lowerBody (pass.startFresh fn.numParams fn.body) fn.body).1
      (bindParams input.args default) <;>
    cases hs : evalComputeBody pass.handlers fn.body (bindParams input.args default)
  · simp [DialectPass.lowerFunc, DialectPass.lowerModuleBody, ht]
  · simp [ht, hs] at h
  · simp [ht, hs] at h
  · simp [DialectPass.lowerFunc, DialectPass.lowerModuleBody, ht]

/-- Constraint part of struct satisfaction is preserved for any target compute output. -/
theorem lowerStruct_constrain_iff {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n : Nat} {i : Fin n} (s : StructDef Δ n i F) (env : LocalVar → F) :
    evalFuncConstrain pass.handlers' (pass.lowerStruct s).constrain env ↔
      evalFuncConstrain pass.handlers s.constrain env :=
  pass.evalFuncConstrain_iff s.constrain env

/-- Module entry constraint semantics is preserved for any target compute output. -/
theorem lowerModule_entryConstrain_iff {Δ Δ' : DialectSet} (pass : DialectPass Δ Δ' F)
    {n : Nat} (m : Module Δ n F) (entry : Fin n) (env : LocalVar → F) :
    evalFuncConstrain pass.handlers' ((pass.lowerModule m).structs entry).constrain env ↔
      evalFuncConstrain pass.handlers (m.structs entry).constrain env :=
  pass.lowerStruct_constrain_iff (m.structs entry) env

end DialectPass

end Dialect
