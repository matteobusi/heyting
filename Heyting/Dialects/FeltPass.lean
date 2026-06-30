/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.DialectPass
import Heyting.Dialects.Felt

/-!
# Felt Dialect Passes

Proof-of-concept body-level no-fresh macro expansion for safe `neg` ops.

This is not a module-safe pass in simple mode: the no-fresh lowering writes `d` twice
(`const d 0; sub d d s`) and therefore does not preserve SSA. A module-level
version needs fresh temporary allocation.
-/

namespace Dialect.FeltPass

open Dialect

abbrev FeltSet : DialectSet := [Felt.sig]

private def feltIx : Fin FeltSet.length := ⟨0, by simp [FeltSet]⟩

private theorem fin_felt_eq (d : Fin FeltSet.length) : d = feltIx := by
  ext
  exact Nat.lt_one_iff.mp d.isLt

abbrev feltHandlers (F : Type) [Field F] : HandlerFamily FeltSet F :=
  fun d => by
    have hd : d = feltIx := fin_felt_eq d
    subst d
    exact (by simpa [FeltSet, feltIx] using (Felt.sem F))

@[simp] theorem feltHandlers_feltIx (F : Type) [Field F] :
    feltHandlers F feltIx = Felt.sem F := by simp [feltHandlers, feltIx, FeltSet]

def lowerNegNoFresh {γ : OpCtx} [Field F]
    (d s : LocalVar) : List (Stmt FeltSet γ F) :=
  if d = s then
    [.op feltIx (Felt.Op.neg d s)]
  else
    [.op feltIx (Felt.Op.const d 0), .op feltIx (Felt.Op.sub d d s)]

def lowerOp [Field F] :
    ∀ {γ : OpCtx} (d : Fin FeltSet.length),
      (FeltSet.get d).Op γ F → List (Stmt FeltSet γ F) :=
  fun d op => by
    have hd : d = feltIx := fin_felt_eq d
    subst d
    exact match op with
      | Felt.Op.neg d s => lowerNegNoFresh d s
      | other => [.op feltIx other]

private theorem negNoFresh_apply [Field F] {γ : OpCtx} (env : LocalVar → F) {d s : LocalVar}
    (h : d ≠ s) :
    Felt.applyOp (Felt.Op.sub (γ := γ) (F := F) d d s)
        (Felt.applyOp (Felt.Op.const (γ := γ) (F := F) d 0) env) =
      Felt.applyOp (Felt.Op.neg (γ := γ) (F := F) d s) env := by
  funext v
  by_cases hv : v = d
  · subst v
    have hs : s ≠ d := fun hs => h hs.symm
    simp [Felt.applyOp, Felt.evalVal, Felt.destVar, hs]
  · simp [Felt.applyOp, Felt.destVar, hv]

theorem simple_constrainSim (F : Type) [Field F] :
    SimpleConstrainSim (feltHandlers F) (lowerOp (F := F) ) (feltHandlers F) := by
  intro n n' γ ctx ctx' d op env
  have hd : d = feltIx := fin_felt_eq d
  subst d
  cases op with
  | add d s1 s2 | sub d s1 s2 | mul d s1 s2 | div d s1 s2 | inv d s | const d c =>
      simp [lowerOp, feltHandlers, evalConstrainEnv, evalConstrainBody, evalConstrainStep, Felt.sem]
  | neg d s =>
      by_cases h : d = s
      · subst s
        simp [lowerOp, lowerNegNoFresh, feltHandlers, evalConstrainEnv, evalConstrainBody,
          evalConstrainStep, Felt.sem]
      · simp only [lowerOp, lowerNegNoFresh, h, feltHandlers_feltIx, Felt.sem]
        constructor
        · exact negNoFresh_apply env h
        · tauto

theorem simple_computeSim (F : Type) [Field F] :
    SimpleComputeSim (feltHandlers F) (lowerOp (F := F) ) (feltHandlers F) := by
  intro n n' γ ctx ctx' d op env
  have hd : d = feltIx := fin_felt_eq d
  subst d
  cases op with
  | add d s1 s2 | sub d s1 s2 | mul d s1 s2 | div d s1 s2 | inv d s | const d c =>
      simp [lowerOp, feltHandlers, evalComputeBody, evalComputeStep, Felt.sem]
  | neg d s =>
      by_cases h : d = s
      · subst s
        simp [lowerOp, lowerNegNoFresh, feltHandlers, evalComputeBody, evalComputeStep, Felt.sem]
      · simp only [lowerOp, lowerNegNoFresh, h, feltHandlers_feltIx, Felt.sem]
        exact congrArg some (negNoFresh_apply env h)

/-- Body-level no-fresh constrain preservation for safe `neg` expansion. -/
theorem simple_constrainBody (F : Type) [Field F] {n n' : Nat} {γ : OpCtx}
    (ctx : SemCtx FeltSet n F) (ctx' : SemCtx FeltSet n' F)
    (stmts : List (Stmt FeltSet γ F))
    (env : LocalVar → F) :
    evalConstrainBody (feltHandlers F) ctx'
        (lowerBody (lowerOp (F := F)) stmts) env ↔
      evalConstrainBody (feltHandlers F) ctx stmts env :=
  @Dialect.simple_constrainBody F _ FeltSet FeltSet n n' γ
    (feltHandlers F) ctx (feltHandlers F) ctx'
    (lowerOp (F := F)) (simple_constrainSim F) stmts env

/-- Body-level no-fresh compute preservation for safe `neg` expansion. -/
theorem simple_computeBody (F : Type) [Field F] {n n' : Nat} {γ : OpCtx}
    (ctx : SemCtx FeltSet n F) (ctx' : SemCtx FeltSet n' F)
    (stmts : List (Stmt FeltSet γ F))
    (env : LocalVar → F) :
    evalComputeBody (feltHandlers F) ctx'
        (lowerBody (lowerOp (F := F)) stmts) env =
      evalComputeBody (feltHandlers F) ctx stmts env :=
  @Dialect.simple_computeBody F _ FeltSet FeltSet n n' γ
    (feltHandlers F) ctx (feltHandlers F) ctx'
    (lowerOp (F := F)) (simple_computeSim F) stmts env

/-! ## Fresh-temp neg lowering -/

def lowerNegFresh {γ : OpCtx} [Field F]
    (tmp d s : LocalVar) : List (Stmt FeltSet γ F) :=
  [.op feltIx (Felt.Op.const tmp 0), .op feltIx (Felt.Op.sub d tmp s)]

def lowerOpFresh [Field F] : FreshLowerOp FeltSet FeltSet F :=
  fun next d op => by
    have hd : d = feltIx := fin_felt_eq d
    subst d
    exact match op with
      | Felt.Op.neg d s => (lowerNegFresh next d s, next + 1)
      | other => ([.op feltIx other], next)

theorem lowerOpFresh_mono (F : Type) [Field F] :
    FreshLowerMono (lowerOpFresh (F := F)) := by
  intro γ next d op
  have hd : d = feltIx := fin_felt_eq d
  subst d
  cases op <;> simp [lowerOpFresh, lowerNegFresh]

private theorem negFresh_apply_below [Field F] {γ : OpCtx} (env : LocalVar → F)
    {tmp d s v : LocalVar} (hvtmp : v < tmp) (htmp_s : tmp ≠ s) :
    Felt.applyOp (Felt.Op.sub (γ := γ) (F := F) d tmp s)
        (Felt.applyOp (Felt.Op.const (γ := γ) (F := F) tmp 0) env) v =
      Felt.applyOp (Felt.Op.neg (γ := γ) (F := F) d s) env v := by
  have hv_ne_tmp : v ≠ tmp := by
    intro h
    rw [h] at hvtmp
    exact (Nat.lt_irrefl tmp) hvtmp
  by_cases hv : v = d
  · subst v
    have hstmp : s ≠ tmp := fun h => htmp_s h.symm
    simp [Felt.applyOp, Felt.evalVal, Felt.destVar, hstmp]
  · simp [Felt.applyOp, Felt.destVar, hv, hv_ne_tmp]

theorem fresh_constrainSim (F : Type) [Field F] :
    FreshConstrainSim (feltHandlers F) (lowerOpFresh (F := F)) (feltHandlers F) := by
  intro n n' γ ctx ctx' next d op env hfresh
  have hd : d = feltIx := fin_felt_eq d
  subst d
  cases op with
  | add d s1 s2 | sub d s1 s2 | mul d s1 s2 | div d s1 s2 | inv d s | const d c =>
      simp [lowerOpFresh, feltHandlers, evalConstrainEnv, evalConstrainBody,
        evalConstrainStep, Felt.sem]
  | neg d s =>
      have hdmem : d ∈ (Stmt.op feltIx (Felt.Op.neg d s) : Stmt FeltSet γ F).vars := by
        change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.neg d s)).toList ++
          Felt.reads (γ := γ) (F := F) (Felt.Op.neg d s)
        simp [Felt.dest, Felt.reads]
      have hsmem : s ∈ (Stmt.op feltIx (Felt.Op.neg d s) : Stmt FeltSet γ F).vars := by
        change s ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.neg d s)).toList ++
          Felt.reads (γ := γ) (F := F) (Felt.Op.neg d s)
        simp [Felt.dest, Felt.reads]
      have hdlt : d < next := hfresh d hdmem
      have hslt : s < next := hfresh s hsmem
      have htmp_d : next ≠ d := fun h => Nat.lt_irrefl next (h ▸ hdlt)
      have htmp_s : next ≠ s := fun h => Nat.lt_irrefl next (h ▸ hslt)
      simp only [lowerOpFresh, lowerNegFresh, feltHandlers_feltIx, Felt.sem]
      constructor
      · intro v hv
        exact negFresh_apply_below env hv htmp_s
      · tauto

theorem fresh_computeSim (F : Type) [Field F] :
    FreshComputeSim (feltHandlers F) (lowerOpFresh (F := F)) (feltHandlers F) := by
  intro n n' γ ctx ctx' next d op env hfresh
  have hd : d = feltIx := fin_felt_eq d
  subst d
  cases op with
  | add d s1 s2 | sub d s1 s2 | mul d s1 s2 | div d s1 s2 | inv d s | const d c =>
      simp only [lowerOpFresh, feltHandlers_feltIx, evalComputeBody_cons, evalComputeStep, Felt.sem]
      intro v hv
      rfl
  | neg d s =>
      have hdmem : d ∈ (Stmt.op feltIx (Felt.Op.neg d s) : Stmt FeltSet γ F).vars := by
        change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.neg d s)).toList ++
          Felt.reads (γ := γ) (F := F) (Felt.Op.neg d s)
        simp [Felt.dest, Felt.reads]
      have hsmem : s ∈ (Stmt.op feltIx (Felt.Op.neg d s) : Stmt FeltSet γ F).vars := by
        change s ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.neg d s)).toList ++
          Felt.reads (γ := γ) (F := F) (Felt.Op.neg d s)
        simp [Felt.dest, Felt.reads]
      have hdlt : d < next := hfresh d hdmem
      have hslt : s < next := hfresh s hsmem
      have htmp_d : next ≠ d := fun h => Nat.lt_irrefl next (h ▸ hdlt)
      have htmp_s : next ≠ s := fun h => Nat.lt_irrefl next (h ▸ hslt)
      simp only [lowerOpFresh, lowerNegFresh, feltHandlers_feltIx, evalComputeBody_cons,
        evalComputeStep, Felt.sem]
      intro v hv
      exact negFresh_apply_below env hv htmp_s

/-- First fresh local for module-level Felt lowering. -/
def startFresh {γ : OpCtx} {F : Type} (numParams : Nat) (body : List (Stmt FeltSet γ F)) :
    LocalVar :=
  max (maxVarBody body) numParams

theorem startFresh_above {γ : OpCtx} {F : Type}
    (numParams : Nat) (body : List (Stmt FeltSet γ F)) :
    bodyFreshAbove (startFresh numParams body) body :=
  bodyFreshAbove_mono (bodyFreshAbove_maxVarBody body) (Nat.le_max_left _ _)

theorem startFresh_init {γ : OpCtx} {F : Type}
    (numParams : Nat) (body : List (Stmt FeltSet γ F)) (v : LocalVar) :
    startFresh numParams body ≤ v → ¬ v < numParams := by
  intro hv hlt
  exact (Nat.not_lt_of_ge (Nat.le_trans (Nat.le_max_right _ _) hv)) hlt

private theorem capsLE_felt_true {γ : OpCtx} {F : Type} (k : Capability)
    (body : List (Stmt FeltSet γ F)) : capsLE k body = true := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | op d p =>
      have hd : d = feltIx := fin_felt_eq d
      subst d
      have hcap : (Stmt.op feltIx p : Stmt FeltSet γ F).cap ≤ k := by
        cases p <;> exact Capability.pure_le k
      change (decide ((Stmt.op feltIx p : Stmt FeltSet γ F).cap ≤ k) && capsLE k rest) = true
      rw [show decide ((Stmt.op feltIx p : Stmt FeltSet γ F).cap ≤ k) = true by simp [hcap]]
      exact ih

theorem fresh_lower_caps {γ : OpCtx} {F : Type} [Field F]
    (k : Capability) (numParams : Nat) (body : List (Stmt FeltSet γ F)) :
    capsLE k body = true →
      capsLE k
        (lowerBodyFresh (lowerOpFresh (F := F)) (startFresh numParams body) body).1 = true := by
  intro _
  exact capsLE_felt_true k _


private theorem init_or_eq_high_false (init : LocalVar → Bool) {next d : LocalVar}
    (hinit : ∀ v, next ≤ v → init v = false) (hdlt : d < next) :
    ∀ v, next ≤ v → (init v || v == d) = false := by
  intro v hv
  have hvd : v ≠ d := by
    intro h
    subst v
    exact Nat.not_lt_of_ge hv hdlt
  simp [hinit v hv, hvd]

private theorem init_or_eq_high_false_succ (init : LocalVar → Bool) {next d : LocalVar}
    (hinit : ∀ v, next ≤ v → init v = false) (hdlt : d < next) :
    ∀ v, next + 1 ≤ v → ((init v || v == next) || v == d) = false := by
  intro v hv
  have hnextv : next ≤ v := Nat.le_trans (Nat.le_succ next) hv
  have hvnext : v ≠ next := by
    intro h
    subst v
    exact Nat.not_succ_le_self next hv
  have hvd : v ≠ d := by
    intro h
    subst v
    exact Nat.not_lt_of_ge hnextv hdlt
  simp [hinit v hnextv, hvnext, hvd]

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem fresh_lower_ssa {γ : OpCtx} {F : Type} [Field F]
    (init : LocalVar → Bool) (next : LocalVar) (body : List (Stmt FeltSet γ F)) :
    (∀ v, next ≤ v → init v = false) →
    bodyFreshAbove next body →
    isSSA init body = true →
      isSSA init (lowerBodyFresh (lowerOpFresh (F := F)) next body).1 = true := by
  induction body generalizing init next with
  | nil =>
      intro _ _ hssa
      exact hssa
  | cons stmt rest ih =>
      intro hinit hfresh hssa
      cases stmt with
      | op ix op =>
        have hix : ix = feltIx := fin_felt_eq ix
        subst ix
        have hstmt : (Stmt.op feltIx op : Stmt FeltSet γ F).freshAbove next :=
          (bodyFreshAbove_cons.mp hfresh).1
        have hrest : bodyFreshAbove next rest :=
          (bodyFreshAbove_cons.mp hfresh).2
        cases op with
        | add d s1 s2 =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.add d s1 s2)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.add d s1 s2)
              simp [Felt.dest, Felt.reads]
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simpa [isSSA, Stmt.reads, Stmt.dest, FeltSet, Felt.reads, Felt.dest] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hih := ih (fun x => init x || x == d) next
              (init_or_eq_high_false init hinit hdlt) hrest htail
            have hih' : isSSA (fun x => init x || x == d)
                (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1 = true := by
              simpa using hih
            simp only [lowerBodyFresh_op, lowerOpFresh]
            change isSSA init (Stmt.op feltIx (Felt.Op.add d s1 s2) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hih']
            exact ⟨by simpa [Stmt.reads, FeltSet, feltIx, Felt.sig, Felt.reads] using
                (Bool.and_eq_true_iff.mp hssa).1,
              by simpa [Bool.not_eq_true'] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1⟩
        | sub d s1 s2 =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.sub d s1 s2)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.sub d s1 s2)
              simp [Felt.dest, Felt.reads]
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simpa [isSSA, Stmt.reads, Stmt.dest, FeltSet, Felt.reads, Felt.dest] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hih := ih (fun x => init x || x == d) next
              (init_or_eq_high_false init hinit hdlt) hrest htail
            have hih' : isSSA (fun x => init x || x == d)
                (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1 = true := by
              simpa using hih
            simp only [lowerBodyFresh_op, lowerOpFresh]
            change isSSA init (Stmt.op feltIx (Felt.Op.sub d s1 s2) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hih']
            exact ⟨by simpa [Stmt.reads, FeltSet, feltIx, Felt.sig, Felt.reads] using
                (Bool.and_eq_true_iff.mp hssa).1,
              by simpa [Bool.not_eq_true'] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1⟩
        | mul d s1 s2 =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.mul d s1 s2)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.mul d s1 s2)
              simp [Felt.dest, Felt.reads]
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simpa [isSSA, Stmt.reads, Stmt.dest, FeltSet, Felt.reads, Felt.dest] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hih := ih (fun x => init x || x == d) next
              (init_or_eq_high_false init hinit hdlt) hrest htail
            have hih' : isSSA (fun x => init x || x == d)
                (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1 = true := by
              simpa using hih
            simp only [lowerBodyFresh_op, lowerOpFresh]
            change isSSA init (Stmt.op feltIx (Felt.Op.mul d s1 s2) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hih']
            exact ⟨by simpa [Stmt.reads, FeltSet, feltIx, Felt.sig, Felt.reads] using
                (Bool.and_eq_true_iff.mp hssa).1,
              by simpa [Bool.not_eq_true'] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1⟩
        | div d s1 s2 =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.div d s1 s2)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.div d s1 s2)
              simp [Felt.dest, Felt.reads]
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simpa [isSSA, Stmt.reads, Stmt.dest, FeltSet, Felt.reads, Felt.dest] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hih := ih (fun x => init x || x == d) next
              (init_or_eq_high_false init hinit hdlt) hrest htail
            have hih' : isSSA (fun x => init x || x == d)
                (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1 = true := by
              simpa using hih
            simp only [lowerBodyFresh_op, lowerOpFresh]
            change isSSA init (Stmt.op feltIx (Felt.Op.div d s1 s2) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hih']
            exact ⟨by simpa [Stmt.reads, FeltSet, feltIx, Felt.sig, Felt.reads] using
                (Bool.and_eq_true_iff.mp hssa).1,
              by simpa [Bool.not_eq_true'] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1⟩
        | inv d s =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.inv d s)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.inv d s)
              simp [Felt.dest, Felt.reads]
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simpa [isSSA, Stmt.reads, Stmt.dest, FeltSet, Felt.reads, Felt.dest] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hih := ih (fun x => init x || x == d) next
              (init_or_eq_high_false init hinit hdlt) hrest htail
            have hih' : isSSA (fun x => init x || x == d)
                (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1 = true := by
              simpa using hih
            simp only [lowerBodyFresh_op, lowerOpFresh]
            change isSSA init (Stmt.op feltIx (Felt.Op.inv d s) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hih']
            exact ⟨by simpa [Stmt.reads, FeltSet, feltIx, Felt.sig, Felt.reads] using
                (Bool.and_eq_true_iff.mp hssa).1,
              by simpa [Bool.not_eq_true'] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1⟩
        | const d c =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.const d c)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.const d c)
              simp [Felt.dest, Felt.reads]
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simpa [isSSA, Stmt.reads, Stmt.dest, FeltSet, Felt.reads, Felt.dest] using
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hih := ih (fun x => init x || x == d) next
              (init_or_eq_high_false init hinit hdlt) hrest htail
            have hih' : isSSA (fun x => init x || x == d)
                (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1 = true := by
              simpa using hih
            simp only [lowerBodyFresh_op, lowerOpFresh]
            change isSSA init (Stmt.op feltIx (Felt.Op.const d c) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) next rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hih']
            exact by simpa [Bool.not_eq_true'] using
              (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1
        | neg d s =>
            have hdlt : d < next := by
              apply hstmt d
              change d ∈ (Felt.dest (γ := γ) (F := F) (Felt.Op.neg d s)).toList ++
                Felt.reads (γ := γ) (F := F) (Felt.Op.neg d s)
              simp [Felt.dest, Felt.reads]
            have hs_true : init s = true := by
              simp only [isSSA, Stmt.reads, Stmt.dest, Felt.reads, Felt.dest, List.all_cons,
                List.all_nil, Bool.and_true] at hssa
              exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).1).1
            have htail : isSSA (fun x => init x || x == d) rest = true := by
              simp only [isSSA, Stmt.reads, Stmt.dest, Felt.reads, Felt.dest, List.all_cons,
                List.all_nil, Bool.and_true] at hssa
              exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).2
            have hnext_false : init next = false := hinit next (Nat.le_refl next)
            have hrest_succ : bodyFreshAbove (next + 1) rest :=
              bodyFreshAbove_mono hrest (Nat.le_succ next)
            have hagree : bodyInitAgree (fun x => init x || x == d)
                (fun x => (init x || x == next) || x == d) rest := by
              intro t ht v hv
              have hvlt : v < next := hrest t ht v hv
              have hvne : v ≠ next := by
                intro h
                subst v
                exact Nat.lt_irrefl next hvlt
              have hvnextb : (v == next) = false := by simp [hvne]
              simp [hvnextb]
            have htail' : isSSA (fun x => (init x || x == next) || x == d) rest = true := by
              rw [← isSSA_congr_init rest hagree]
              exact htail
            have hih := ih (fun x => (init x || x == next) || x == d) (next + 1)
              (init_or_eq_high_false_succ init hinit hdlt) hrest_succ htail'
            simp only [lowerBodyFresh_op, lowerOpFresh,
              lowerNegFresh, feltHandlers_feltIx, Felt.sem]
            change isSSA init (Stmt.op feltIx (Felt.Op.const next 0) ::
              Stmt.op feltIx (Felt.Op.sub d next s) ::
              (lowerBodyFresh (lowerOpFresh (F := F)) (next + 1) rest).1) = true
            simp [isSSA, Stmt.reads, Stmt.dest, FeltSet, feltIx, Felt.sig, Felt.reads,
              Felt.dest, hnext_false, hs_true]
            constructor
            · constructor
              · simpa [Bool.not_eq_true'] using
                  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hssa).2).1
              · intro h
                subst d
                exact Nat.lt_irrefl next hdlt
            · simpa using hih

/-- Module-safe Felt pass erasing `neg` through a fresh temporary. -/
def modulePass (F : Type) [Field F] : DialectPass FeltSet FeltSet F where
  handlers  := feltHandlers F
  handlers' := feltHandlers F
  lowerOp   := lowerOpFresh (F := F)
  next_mono := lowerOpFresh_mono F
  constrain := fresh_constrainSim F
  compute   := fresh_computeSim F
  startFresh := startFresh
  startFresh_above := by
    intro γ numParams body
    exact startFresh_above numParams body
  startFresh_init := by
    intro γ numParams body v hv
    exact startFresh_init numParams body v hv
  lower_caps := by
    intro γ k numParams body hcaps
    exact fresh_lower_caps k numParams body hcaps
  lower_ssa := by
    intro γ init next body hinit hfresh hssa
    exact fresh_lower_ssa init next body hinit hfresh hssa

end Dialect.FeltPass
