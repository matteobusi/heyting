/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Core.Pass
import Heyting.Languages.StructIR
import Heyting.Languages.StructInlineIR

namespace StructIRToStructInlineIR

open StructIR

variable {F : Type} [Field F] {n : Nat}

abbrev ConstrainStmtInline (n : Nat) (F : Type) :=
  StructInlineIR.ConstrainStmt n F

abbrev Subst := Nat → Nat

def Subst.update (subst : Subst) (src dst : Nat) : Subst :=
  fun v => if v == src then dst else subst v

/-! ## Substitution boundedness -/

abbrev SubstBounded (s : Subst) (bound : Nat) : Prop := ∀ v, s v < bound

omit [Field F] in
theorem substBounded_update {s : Subst} {bound : Nat}
    (hs : SubstBounded s bound) (dest : Nat) :
    SubstBounded (Subst.update s dest bound) (bound + 1) := by
  intro v; simp only [Subst.update]
  split
  · exact Nat.lt_succ_of_le (Nat.le_refl bound)
  · exact Nat.lt_succ_of_lt (hs v)

/-! ## Environment agreement -/

/-- Agreement between source and inlined local environments under a substitution map. -/
abbrev EnvRel (subst : Subst) (envs envi : StructIR.LocalEnv F) : Prop :=
  ∀ v, envi (subst v) = envs v

/-- Agreement between source and inlined object environments under a substitution map. -/
abbrev ObjRel (subst : Subst) (objs obji : StructIR.ObjEnv) : Prop :=
  ∀ v, obji (subst v) = objs v

omit [Field F] in
theorem envRel_update_bounded {s : Subst} {envs envi : StructIR.LocalEnv F}
    (h : EnvRel s envs envi) {bound : Nat} (hs : SubstBounded s bound)
    (dest : Nat) (val : F) :
    EnvRel (Subst.update s dest bound)
      (envs.update dest val) (envi.update bound val) := by
  intro v
  simp only [Subst.update, StructIR.LocalEnv.update, beq_iff_eq]
  split
  · subst_vars; simp
  · rename_i hne; simp [Nat.ne_of_lt (hs v), h v]

omit [Field F] in
theorem objRel_update_bounded {s : Subst} {objs obji : StructIR.ObjEnv}
    (h : ObjRel s objs obji) {bound : Nat} (hs : SubstBounded s bound)
    (dest : Nat) (path : StructIR.InstancePath) :
    ObjRel (Subst.update s dest bound)
      (objs.update dest path) (obji.update bound path) := by
  intro v
  simp only [Subst.update, StructIR.ObjEnv.update, beq_iff_eq]
  split
  · subst_vars; simp
  · rename_i hne; simp [Nat.ne_of_lt (hs v), h v]

/-! ## Callee inlining (alpha-renames all dests) -/

def inlineBody (m : StructIR.Module n F) (i : Fin n)
    (valSubst : Subst) (objSubst : Subst) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    List (ConstrainStmtInline n F) × Nat :=
  match body with
  | [] => ([], next)
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      let out : ConstrainStmtInline n F := .feltAdd next (valSubst src1) (valSubst src2)
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) objSubst (next + 1) rest
      (out :: tail, next')
    | .feltSub dest src1 src2 =>
      let out : ConstrainStmtInline n F := .feltSub next (valSubst src1) (valSubst src2)
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) objSubst (next + 1) rest
      (out :: tail, next')
    | .feltMul dest src1 src2 =>
      let out : ConstrainStmtInline n F := .feltMul next (valSubst src1) (valSubst src2)
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) objSubst (next + 1) rest
      (out :: tail, next')
    | .feltDiv dest src1 src2 =>
      let out : ConstrainStmtInline n F := .feltDiv next (valSubst src1) (valSubst src2)
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) objSubst (next + 1) rest
      (out :: tail, next')
    | .feltNeg dest src =>
      let out : ConstrainStmtInline n F := .feltNeg next (valSubst src)
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) objSubst (next + 1) rest
      (out :: tail, next')
    | .feltConst dest c =>
      let out : ConstrainStmtInline n F := .feltConst next c
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) objSubst (next + 1) rest
      (out :: tail, next')
    | .readMember dest self member =>
      let out : ConstrainStmtInline n F := .readMember next (objSubst self) member.val
      let (tail, next') :=
        inlineBody m i (Subst.update valSubst dest next) (Subst.update objSubst dest next)
          (next + 1) rest
      (out :: tail, next')
    | .constrainEq src1 src2 =>
      let out : ConstrainStmtInline n F := .constrainEq (valSubst src1) (valSubst src2)
      let (tail, next') := inlineBody m i valSubst objSubst next rest
      (out :: tail, next')
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let zeroVar := next
      let zeroStmt : ConstrainStmtInline n F := .feltConst zeroVar (0 : F)
      let calleeValSubst : Subst := fun param =>
        match args[param]? with
        | some arg => valSubst arg
        | none => zeroVar
      let calleeObjSubst : Subst := fun param =>
        match args[param]? with
        | some arg => objSubst arg
        | none => zeroVar
      let calleeBody := (m.structs j).constrain.body
      let (inlinedCallee, nextAfterCall) :=
        inlineBody m j calleeValSubst calleeObjSubst (next + 1) calleeBody
      let (tail, next') := inlineBody m i valSubst objSubst nextAfterCall rest
      (zeroStmt :: inlinedCallee ++ tail, next')
  termination_by (i, body.length)

/-! ## Top-level expansion (preserves non-call dests) -/

def expandBody (m : StructIR.Module n F) (i : Fin n) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    List (ConstrainStmtInline n F) × Nat :=
  match body with
  | [] => ([], next)
  | stmt :: rest =>
    match stmt with
    | .feltAdd d s1 s2 =>
      let (t, n') := expandBody m i next rest
      (.feltAdd d s1 s2 :: t, n')
    | .feltSub d s1 s2 =>
      let (t, n') := expandBody m i next rest
      (.feltSub d s1 s2 :: t, n')
    | .feltMul d s1 s2 =>
      let (t, n') := expandBody m i next rest
      (.feltMul d s1 s2 :: t, n')
    | .feltDiv d s1 s2 =>
      let (t, n') := expandBody m i next rest
      (.feltDiv d s1 s2 :: t, n')
    | .feltNeg d s =>
      let (t, n') := expandBody m i next rest
      (.feltNeg d s :: t, n')
    | .feltConst d c =>
      let (t, n') := expandBody m i next rest
      (.feltConst d c :: t, n')
    | .readMember d s mem =>
      let (t, n') := expandBody m i next rest
      (.readMember d s mem.val :: t, n')
    | .constrainEq s1 s2 =>
      let (t, n') := expandBody m i next rest
      (.constrainEq s1 s2 :: t, n')
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let zv := next
      let cvS : Subst := fun p =>
        match args[p]? with | some a => a | none => zv
      let coS : Subst := fun p =>
        match args[p]? with | some a => a | none => zv
      let (ic, na) :=
        inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body
      let (t, n') := expandBody m i na rest
      (.feltConst zv (0 : F) :: ic ++ t, n')
  termination_by (i, body.length)

/-! ## Max variable in a body -/

omit [Field F] in
def maxVarStmt {i : Fin n} {nm : Nat} (stmt : StructIR.ConstrainStmt n i F nm) : Nat :=
  match stmt with
  | .feltAdd d s1 s2 | .feltSub d s1 s2
  | .feltMul d s1 s2 | .feltDiv d s1 s2 => max d (max s1 s2)
  | .feltNeg d s | .readMember d s _ => max d s
  | .feltConst d _ => d
  | .constrainEq s1 s2 => max s1 s2
  | .call _ args => args.foldl max 0

omit [Field F] in
def maxVarBody {i : Fin n} {nm : Nat}
    (body : List (StructIR.ConstrainStmt n i F nm)) : Nat :=
  body.foldl (fun acc s => max acc (maxVarStmt s)) 0

/-! ## Compilation -/

def compileStruct (m : StructIR.Module n F) (i : Fin n) : StructInlineIR.StructDef n F :=
  let next := maxVarBody (m.structs i).constrain.body + 1
  let body := (expandBody m i next (m.structs i).constrain.body).1
  { name := (m.structs i).name
    members := (m.structs i).members
    constrain := {
      numParams := (m.structs i).constrain.numParams
      body := body } }

def compile (m : StructIR.Module (n + 1) F) : StructInlineIR.Module (n + 1) F :=
  fun i => compileStruct m i

def witnessRel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (wi : StructIR.Witness F) : Prop :=
  let _ := m
  wi = ws

omit [Field F] in
theorem witnessRel_refl (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) : witnessRel m ws ws := by
  simp [witnessRel]

/-! ## Correctness: expandBody preserves evaluation -/

omit [Field F] in
/-- All variable positions in a statement are < bound. -/
def allVarsBelowStmt {i : Fin n} {nm : Nat}
    (stmt : StructIR.ConstrainStmt n i F nm) (bound : Nat) : Prop :=
  maxVarStmt stmt < bound

omit [Field F] in
/-- All variable positions in a body are < bound. -/
def allVarsBelow {i : Fin n} {nm : Nat}
    (body : List (StructIR.ConstrainStmt n i F nm)) (bound : Nat) : Prop :=
  ∀ s ∈ body, allVarsBelowStmt s bound

omit [Field F] in
private theorem foldl_max_le_init {α : Type*} (f : α → Nat) (l : List α) (init : Nat) :
    init ≤ l.foldl (fun acc x => max acc (f x)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

omit [Field F] in
private theorem foldl_max_mem {α : Type*} (f : α → Nat) {l : List α} {x : α}
    (hx : x ∈ l) (init : Nat) :
    f x ≤ l.foldl (fun acc s => max acc (f s)) init := by
  induction l generalizing init with
  | nil => exact absurd hx List.not_mem_nil
  | cons h t ih =>
    rcases List.mem_cons.mp hx with heq | hmem
    · subst heq; exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_le_init f t _)
    · exact ih hmem _

omit [Field F] in
theorem maxVarBody_bound {i : Fin n} {nm : Nat}
    (body : List (StructIR.ConstrainStmt n i F nm)) :
    allVarsBelow body (maxVarBody body + 1) := by
  intro s hs
  simp only [allVarsBelowStmt, maxVarBody]
  exact Nat.lt_succ_of_le (foldl_max_mem maxVarStmt hs 0)

/-- Object environment freshness: all positions ≥ next map to []. -/
def ObjFresh (objEnv : StructIR.ObjEnv) (next : Nat) : Prop :=
  ∀ v, v ≥ next → objEnv v = []

omit [Field F] in
/-- Object environment freshness is preserved by updates below the boundary. -/
theorem objFresh_update_below {objEnv : StructIR.ObjEnv} {next : Nat}
    (h : ObjFresh objEnv next) {d : Nat} (hd : d < next) (path : StructIR.InstancePath) :
    ObjFresh (objEnv.update d path) next := by
  intro v hv
  simp only [StructIR.ObjEnv.update, beq_iff_eq]
  split
  · next heq => subst heq; omega
  · exact h v hv

/-! ## Combined inlineBody correctness + frame (proved by k-bounded strong induction) -/

omit [Field F] in
private lemma localEnv_update_ne (env : StructIR.LocalEnv F) (k v : Nat) (val : F) (h : v ≠ k) :
    (env.update k val) v = env v := by
  simp only [StructIR.LocalEnv.update, beq_iff_eq, ite_eq_right_iff]
  exact fun hc => absurd hc h

omit [Field F] in
private lemma objEnv_update_ne (env : StructIR.ObjEnv) (k v : Nat)
    (path : StructIR.InstancePath) (h : v ≠ k) :
    (StructIR.ObjEnv.update env k path) v = env v := by
  simp only [StructIR.ObjEnv.update, beq_iff_eq, ite_eq_right_iff]
  exact fun hc => absurd hc h

omit [Field F] in
private lemma objFresh_succ {obji : StructIR.ObjEnv} {next : Nat}
    (h : ObjFresh obji next) : ObjFresh obji (next + 1) := by
  intro v hv
  exact h v (Nat.le_of_succ_le hv)

omit [Field F] in
private lemma objFresh_update_at {obji : StructIR.ObjEnv} {next : Nat}
    (h : ObjFresh obji next) (path : StructIR.InstancePath) :
    ObjFresh (StructIR.ObjEnv.update obji next path) (next + 1) := by
  intro v hv
  rw [objEnv_update_ne obji next v path (by omega : v ≠ next)]
  exact h v (Nat.le_of_succ_le hv)

/-- The next counter returned by inlineBody is ≥ the initial next. -/
private theorem inlineBody_next_ge (m : StructIR.Module n F) (i : Fin n)
    (valSubst objSubst : Subst) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    next ≤ (inlineBody m i valSubst objSubst next body).2 := by
  induction body generalizing valSubst objSubst next with
  | nil => simp [inlineBody]
  | cons stmt rest ih =>
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | feltSub dest src1 src2 =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | feltMul dest src1 src2 =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | feltDiv dest src1 src2 =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | feltNeg dest src =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | feltConst dest c =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | readMember dest self member =>
      simp only [inlineBody]
      exact Nat.le_trans (Nat.le_succ next) (ih _ _ _)
    | constrainEq src1 src2 =>
      simp only [inlineBody]
      exact ih _ _ _
    | call target args =>
      simp only [inlineBody]
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let cvS : Subst := fun p => match args[p]? with | some a => valSubst a | none => next
      let coS : Subst := fun p => match args[p]? with | some a => objSubst a | none => next
      have hna_ge : next + 1 ≤ (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).2 :=
        inlineBody_next_ge m j cvS coS (next + 1) (m.structs j).constrain.body
      exact Nat.le_trans (Nat.le_succ next)
        (Nat.le_trans hna_ge
          (ih _ _ _))
  termination_by (i, body.length)

/-- Upper-bound frame: running the inlined body does not touch positions ≥ returned next.
    This holds because inlineBody only allocates positions in [initial_next, returned_next). -/
private theorem inlineBody_frame_above (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (valSubst objSubst : Subst) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (envi : StructInlineIR.LocalEnv F) (obji : StructIR.ObjEnv)
    (v : Nat) (hv : (inlineBody m i valSubst objSubst next body).2 ≤ v) :
    (StructInlineIR.runState w envi obji (inlineBody m i valSubst objSubst next body).1).1 v =
      envi v ∧
    (StructInlineIR.runState w envi obji (inlineBody m i valSubst objSubst next body).1).2 v =
      obji v := by
  induction body generalizing valSubst objSubst next envi obji with
  | nil => simp [inlineBody, StructInlineIR.runState]
  | cons stmt rest ih =>
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next) objSubst (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next) objSubst (next + 1)
        (envi.update next (envi (valSubst src1) + envi (valSubst src2))) obji
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2⟩
      exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | feltSub dest src1 src2 =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next) objSubst (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next) objSubst (next + 1)
        (envi.update next (envi (valSubst src1) - envi (valSubst src2))) obji
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2⟩
      exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | feltMul dest src1 src2 =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next) objSubst (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next) objSubst (next + 1)
        (envi.update next (envi (valSubst src1) * envi (valSubst src2))) obji
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2⟩
      exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | feltDiv dest src1 src2 =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next) objSubst (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next) objSubst (next + 1)
        (envi.update next (envi (valSubst src1) * (envi (valSubst src2))⁻¹)) obji
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2⟩
      exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | feltNeg dest src =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next) objSubst (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next) objSubst (next + 1)
        (envi.update next (-(envi (valSubst src)))) obji
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2⟩
      exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | feltConst dest c =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next) objSubst (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next) objSubst (next + 1)
        (envi.update next c) obji
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2⟩
      exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | readMember dest self member =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      have hle : next + 1 ≤ v := Nat.le_trans
        (inlineBody_next_ge m i (Subst.update valSubst dest next)
          (Subst.update objSubst dest next) (next + 1) rest)
        (by simp only [inlineBody] at hv; exact hv)
      obtain ⟨h1, h2⟩ := ih (Subst.update valSubst dest next)
        (Subst.update objSubst dest next) (next + 1)
        (envi.update next (w (obji (objSubst self), member.val)))
        (StructIR.ObjEnv.update obji next (obji (objSubst self) ++ [member.val]))
        (by simp only [inlineBody] at hv; exact hv)
      refine ⟨h1.trans ?_, h2.trans ?_⟩
      · exact localEnv_update_ne envi next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
      · exact objEnv_update_ne obji next v _ (Nat.ne_of_gt (Nat.lt_of_succ_le hle))
    | constrainEq src1 src2 =>
      simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
      exact ih valSubst objSubst next envi obji (by simp only [inlineBody] at hv; exact hv)
    | call target args =>
      simp only [inlineBody]
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let cvS : Subst := fun p => match args[p]? with | some a => valSubst a | none => next
      let coS : Subst := fun p => match args[p]? with | some a => objSubst a | none => next
      -- The callee `inlinedCallee` runs, then the tail. We want v ≥ ret ≥ callee_next.
      -- First apply: runState on (inlinedCallee ++ tail).
      rw [List.cons_append, StructInlineIR.runState]
      simp only [StructInlineIR.stepState]
      rw [StructInlineIR.runState_append]
      -- Now: the state after inlinedCallee has a composite relation with obji.
      -- Use ih on the tail with initial next = nextAfterCall.
      have hna_ge : next + 1 ≤ (inlineBody m j cvS coS (next + 1)
          (m.structs j).constrain.body).2 :=
        inlineBody_next_ge m j cvS coS (next + 1) (m.structs j).constrain.body
      have hv_tail : (inlineBody m i valSubst objSubst
          (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).2 rest).2 ≤ v := by
        simp only [inlineBody] at hv
        exact hv
      -- The tail starts at nextAfterCall; its own returned_next ≤ v. Apply ih.
      obtain ⟨htail1, htail2⟩ := ih valSubst objSubst
        (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).2
        ((StructInlineIR.runState w (envi.update next 0) obji
          (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).1).1)
        ((StructInlineIR.runState w (envi.update next 0) obji
          (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).1).2)
        hv_tail
      -- Now need: after inlinedCallee, position v is unchanged from (envi.update next 0, obji).
      -- By recursion on the callee via inlineBody_frame_above.
      have hv_callee : (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).2 ≤ v :=
        Nat.le_trans (inlineBody_next_ge m i valSubst objSubst
          (inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body).2 rest) hv_tail
      obtain ⟨hic1, hic2⟩ := inlineBody_frame_above m w j cvS coS (next + 1)
        (m.structs j).constrain.body (envi.update next 0) obji v hv_callee
      refine ⟨htail1.trans (hic1.trans ?_), htail2.trans hic2⟩
      exact localEnv_update_ne envi next v 0 (Nat.ne_of_gt (by
        have : next + 1 ≤ v := Nat.le_trans hna_ge hv_callee
        exact Nat.lt_of_succ_le this))
  termination_by (i, body.length)

/-- Combined frame + correctness for inlineBody, by k-bounded strong induction on struct index. -/
private theorem inlineBody_props (m : StructIR.Module n F) (w : StructIR.Witness F)
    (k : Nat) (i : Fin n) (hi : i.val < k)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    -- Frame: running inlined body does not touch vars below `next`
    (∀ (valSubst objSubst : Subst) (next : Nat)
        (envi : StructInlineIR.LocalEnv F) (obji : StructIR.ObjEnv),
       SubstBounded valSubst next → SubstBounded objSubst next →
       ∀ v, v < next →
         (StructInlineIR.runState w envi obji (inlineBody m i valSubst objSubst next body).1).1 v =
           envi v ∧
         (StructInlineIR.runState w envi obji (inlineBody m i valSubst objSubst next body).1).2 v =
           obji v)
    ∧
    -- Correctness: source eval ↔ inlined eval under env relation
    (∀ (valSubst objSubst : Subst) (next : Nat)
        (envs envi : StructIR.LocalEnv F) (objs obji : StructIR.ObjEnv),
       EnvRel valSubst envs envi → ObjRel objSubst objs obji →
       SubstBounded valSubst next → SubstBounded objSubst next → ObjFresh obji next →
        (StructIR.evalConstrainBody m w i envs objs body ↔
         StructInlineIR.evalConstrainBody
           (fun _ => { name := "", members := [], constrain := { numParams := 0, body := [] } })
           w i envi obji
           (inlineBody m i valSubst objSubst next body).1)) := by
  induction k generalizing i body with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ k ihk =>
    -- Now i.val < k+1, so i.val ≤ k.
    -- Inner structural induction on body.
    induction body with
    | nil =>
      constructor
      · intro _ _ _ _ _ _ _ v _; simp [inlineBody, StructInlineIR.runState]
      · intro _ _ _ _
        simp [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
    | cons stmt rest ih_rest =>
      -- IH for rest (same i; `ih_rest` already has i fixed since we didn't generalize)
      have ⟨frame_rest, correct_rest⟩ := ih_rest
      constructor
      · -- Frame
        intro valSubst objSubst next envi obji hValBound hObjBound v hv
        cases stmt with
        | feltAdd dest src1 src2 =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next) objSubst (next + 1)
            (envi.update next (envi (valSubst src1) + envi (valSubst src2))) obji
            (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)),
                 h2⟩
        | feltSub dest src1 src2 =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next) objSubst (next + 1)
            (envi.update next (envi (valSubst src1) - envi (valSubst src2))) obji
            (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)), h2⟩
        | feltMul dest src1 src2 =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next) objSubst (next + 1)
            (envi.update next (envi (valSubst src1) * envi (valSubst src2))) obji
            (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)), h2⟩
        | feltDiv dest src1 src2 =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next) objSubst (next + 1)
            (envi.update next (envi (valSubst src1) * (envi (valSubst src2))⁻¹)) obji
            (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)), h2⟩
        | feltNeg dest src =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next) objSubst (next + 1)
            (envi.update next (-(envi (valSubst src)))) obji
            (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)), h2⟩
        | feltConst dest c =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next) objSubst (next + 1)
            (envi.update next c) obji
            (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)), h2⟩
        | readMember dest self member =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          obtain ⟨h1, h2⟩ := frame_rest (Subst.update valSubst dest next)
            (Subst.update objSubst dest next) (next + 1)
            (envi.update next (w (obji (objSubst self), member.val)))
            (StructIR.ObjEnv.update obji next (obji (objSubst self) ++ [member.val]))
            (substBounded_update hValBound dest) (substBounded_update hObjBound dest)
            v (Nat.lt_succ_of_lt hv)
          exact ⟨h1.trans (localEnv_update_ne envi next v _ (Nat.ne_of_lt hv)),
                 h2.trans (objEnv_update_ne obji next v _ (Nat.ne_of_lt hv))⟩
        | constrainEq src1 src2 =>
          simp only [inlineBody, StructInlineIR.runState, StructInlineIR.stepState]
          exact frame_rest valSubst objSubst next envi obji hValBound hObjBound v hv
        | call target args =>
          -- j = ⟨target.val, target.isLt.trans i.isLt⟩; j.val < i.val ≤ k
          simp only [inlineBody]
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let cvS : Subst := fun p => match args[p]? with | some a => valSubst a | none => next
          let coS : Subst := fun p => match args[p]? with | some a => objSubst a | none => next
          -- j.val < i.val < k+1, so j.val < k
          have hj : j.val < k := Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le target.isLt (Nat.lt_succ_iff.mp hi)) (Nat.le_refl k)
          have ⟨frame_callee, _⟩ := ihk j hj (m.structs j).constrain.body
          -- cvS, coS are bounded by next+1
          have hcvS : SubstBounded cvS (next + 1) := fun p => by
            simp only [cvS]; split
            · exact Nat.lt_succ_of_lt (hValBound _)
            · exact Nat.lt_succ_self _
          have hcoS : SubstBounded coS (next + 1) := fun p => by
            simp only [coS]; split
            · exact Nat.lt_succ_of_lt (hObjBound _)
            · exact Nat.lt_succ_self _
          -- after zeroStmt (feltConst next 0), envi becomes envi.update next 0
          -- v < next so v ≠ next: (envi.update next 0) v = envi v
          -- after inlinedCallee (frame: vars < next+1 preserved, in particular v < next):
          --   envAfter v = (envi.update next 0) v = envi v
          -- after tail rest (frame: vars < nextAfterCall ≥ next+1 > next):
          --   envFinal v = envAfter v = envi v
          -- Use evalConstrainBody_append to split inlinedCallee ++ tail
          let ic_pair := inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body
          let ic := ic_pair.1
          let na := ic_pair.2
          let tail_pair := inlineBody m i valSubst objSubst na rest
          let tail := tail_pair.1
          -- After zeroStmt: state is (envi.update next 0, obji)
          -- After ic: frame_callee at v, next+1
          have hv' : v < next + 1 := Nat.lt_succ_of_lt hv
          obtain ⟨hic1, hic2⟩ := frame_callee cvS coS (next + 1)
            (envi.update next 0) obji hcvS hcoS v hv'
          -- na ≥ next + 1 (inlineBody only increases next), so v < na
          -- We need frame for the tail at (na, v)
          -- For that we need na > v. We know na ≥ next+1 > v.
          -- However frame_rest is about rest with the original valSubst, objSubst
          -- The tail uses valSubst, objSubst, na
          -- We need SubstBounded valSubst na and SubstBounded objSubst na
          -- Since valSubst src < next < next+1 ≤ na, and objSubst src < next < na
          -- na ≥ next+1 follows from inlineBody_next_ge (to be established)
          -- For now, observe: after zeroStmt + ic, the env at v is envi v.
          -- For the tail with na: v < next+1 ≤ na (by monotonicity of inlineBody next)
          -- We use: hv_tail : v < na (follows from v < next < na)
          -- And: SubstBounded valSubst na (follows from valSubst bound < next < na)
          -- But we need to know na ≥ next+1. This holds since inlineBody increases next.
          -- Key: inlineBody_next monotone. Let's establish inline separately.
          -- For a simpler approach: we know na = ic_pair.2, and the callee processes a
          -- body starting at next+1, so na ≥ next+1 > next > v.
          -- We use: Nat.le_of_lt (Nat.lt_of_lt_of_le hv (Nat.le_of_lt (Nat.lt_succ_self next)))
          -- Actually just need v < na. We'll establish na ≥ next+1 by:
          -- inlineBody m j cvS coS (next+1) body: all new slots are ≥ next+1,
          -- and next' returned is the fresh slot after all allocations.
          -- The simplest: assume ic_pair.2 ≥ next+1 (will prove separately as inlineBody_next_ge)
          -- For now carry it via a sub-lemma inline:
          have hna_ge : next + 1 ≤ na := by
            exact inlineBody_next_ge m j cvS coS (next + 1) (m.structs j).constrain.body
          have hv_na : v < na := Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hv) hna_ge
          have hvalBound_na : SubstBounded valSubst na :=
            fun p => Nat.lt_of_lt_of_le (hValBound p) (Nat.le_trans (Nat.le_succ next) hna_ge)
          have hobjBound_na : SubstBounded objSubst na :=
            fun p => Nat.lt_of_lt_of_le (hObjBound p) (Nat.le_trans (Nat.le_succ next) hna_ge)
          -- Frame for tail: after running tail, v is unchanged
          obtain ⟨htail1, htail2⟩ := frame_rest valSubst objSubst na
            ((StructInlineIR.runState w (envi.update next 0) obji ic).1)
            ((StructInlineIR.runState w (envi.update next 0) obji ic).2)
            hvalBound_na hobjBound_na v hv_na
          -- Goal: (runState w envi obji (zeroStmt :: ic ++ tail)) v = (envi v, obji v)
          -- runState on zeroStmt first updates env to envi.update next 0,
          -- then runs ic to produce (envAfterIC, objAfterIC),
          -- then runs tail.
          -- Use runState_append to split (ic ++ tail).
          refine ⟨?_, ?_⟩
          · -- env component
            change (StructInlineIR.runState w envi obji
                   (StructInlineIR.ConstrainStmt.feltConst next 0 :: ic ++ tail)).1 v = envi v
            rw [List.cons_append, StructInlineIR.runState]
            simp only [StructInlineIR.stepState]
            rw [StructInlineIR.runState_append]
            exact htail1.trans
              (hic1.trans (localEnv_update_ne envi next v 0 (Nat.ne_of_lt hv)))
          · -- obj component
            change (StructInlineIR.runState w envi obji
                   (StructInlineIR.ConstrainStmt.feltConst next 0 :: ic ++ tail)).2 v = obji v
            rw [List.cons_append, StructInlineIR.runState]
            simp only [StructInlineIR.stepState]
            rw [StructInlineIR.runState_append]
            exact htail2.trans hic2
      · -- Correctness
        cases stmt with
          | feltAdd dest src1 src2 =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hval : envi (valSubst src1) + envi (valSubst src2) = envs src1 + envs src2 := by
               rw [hEnvRel, hEnvRel]
             rw [hval]
             constructor
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mp h⟩
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mpr h⟩
          | feltSub dest src1 src2 =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hval : envi (valSubst src1) - envi (valSubst src2) = envs src1 - envs src2 := by
               rw [hEnvRel, hEnvRel]
             rw [hval]
             constructor
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mp h⟩
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mpr h⟩
          | feltMul dest src1 src2 =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hval : envi (valSubst src1) * envi (valSubst src2) = envs src1 * envs src2 := by
               rw [hEnvRel, hEnvRel]
             rw [hval]
             constructor
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mp h⟩
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mpr h⟩
          | feltDiv dest src1 src2 =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hval : envi (valSubst src1) * (envi (valSubst src2))⁻¹
                       = envs src1 * (envs src2)⁻¹ := by
               rw [hEnvRel, hEnvRel]
             have hne_iff : envs src2 ≠ 0 ↔ envi (valSubst src2) ≠ 0 := by
               rw [hEnvRel]
             rw [hval]
             constructor
             · intro ⟨hne, h⟩
               exact ⟨hne_iff.mp hne,
                      (correct_rest _ _ (next + 1) _ _ _ _
                        (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                        (substBounded_update hValBound dest)
                        (fun v => Nat.lt_succ_of_lt (hObjBound v))
                        (objFresh_succ hObjFresh)).mp h⟩
             · intro ⟨hne, h⟩
               exact ⟨hne_iff.mpr hne,
                      (correct_rest _ _ (next + 1) _ _ _ _
                        (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                        (substBounded_update hValBound dest)
                        (fun v => Nat.lt_succ_of_lt (hObjBound v))
                        (objFresh_succ hObjFresh)).mpr h⟩
          | feltNeg dest src =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hval : -envi (valSubst src) = -envs src := by rw [hEnvRel]
             rw [hval]
             constructor
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mp h⟩
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest _) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mpr h⟩
          | feltConst dest c =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             constructor
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest c) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mp h⟩
             · intro ⟨_, h⟩; exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _
                 (envRel_update_bounded hEnvRel hValBound dest c) hObjRel
                 (substBounded_update hValBound dest) (fun v => Nat.lt_succ_of_lt (hObjBound v))
                 (objFresh_succ hObjFresh)).mpr h⟩
          | readMember dest self member =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hself : obji (objSubst self) = objs self := hObjRel self
             rw [hself]
             have hEnv' : EnvRel (valSubst.update dest next)
                          (envs.update dest (w (objs self, member.val)))
                          (StructInlineIR.LocalEnv.update envi next
                            (w (objs self, member.val))) :=
               envRel_update_bounded hEnvRel hValBound dest (w (objs self, member.val))
             have hObj' : ObjRel (objSubst.update dest next)
                          (objs.update dest (objs self ++ [member.val]))
                          (StructIR.ObjEnv.update obji next (objs self ++ [member.val])) :=
               objRel_update_bounded hObjRel hObjBound dest (objs self ++ [member.val])
             constructor
             · intro ⟨_, h⟩
               exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _ hEnv' hObj'
                 (substBounded_update hValBound dest)
                 (substBounded_update hObjBound dest)
                 (objFresh_update_at hObjFresh (objs self ++ [member.val]))).mp h⟩
             · intro ⟨_, h⟩
               exact ⟨trivial, (correct_rest _ _ (next + 1) _ _ _ _ hEnv' hObj'
                 (substBounded_update hValBound dest)
                 (substBounded_update hObjBound dest)
                 (objFresh_update_at hObjFresh (objs self ++ [member.val]))).mpr h⟩
          | constrainEq src1 src2 =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody, StructInlineIR.evalConstrainBody]
             have hs1 : envi (valSubst src1) = envs src1 := hEnvRel src1
             have hs2 : envi (valSubst src2) = envs src2 := hEnvRel src2
             rw [hs1, hs2]
             constructor
             · intro ⟨heq, h⟩
               exact ⟨heq,
                      (correct_rest _ _ next _ _ _ _ hEnvRel hObjRel hValBound hObjBound
                        hObjFresh).mp h⟩
             · intro ⟨heq, h⟩
               exact ⟨heq,
                      (correct_rest _ _ next _ _ _ _ hEnvRel hObjRel hValBound hObjBound
                        hObjFresh).mpr h⟩
          | call target args =>
             intro valSubst objSubst next envs envi objs obji
             simp only [EnvRel, ObjRel, SubstBounded]
             intro hEnvRel hObjRel hValBound hObjBound hObjFresh
             simp only [StructIR.evalConstrainBody, inlineBody]
             let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
             let cvS : Subst := fun p => match args[p]? with | some a => valSubst a | none => next
             let coS : Subst := fun p => match args[p]? with | some a => objSubst a | none => next
             have hj : j.val < k := Nat.lt_of_lt_of_le
               (Nat.lt_of_lt_of_le target.isLt (Nat.lt_succ_iff.mp hi)) (Nat.le_refl k)
             have ⟨frame_callee, correct_callee⟩ := ihk j hj (m.structs j).constrain.body
             have hcvS : SubstBounded cvS (next + 1) := fun p => by
               simp only [cvS]; split
               · exact Nat.lt_succ_of_lt (hValBound _)
               · exact Nat.lt_succ_self _
             have hcoS : SubstBounded coS (next + 1) := fun p => by
               simp only [coS]; split
               · exact Nat.lt_succ_of_lt (hObjBound _)
               · exact Nat.lt_succ_self _
             let calleeEnv : StructIR.LocalEnv F :=
               fun p => match args[p]? with | some a => envs a | none => 0
             let calleeObjEnv : StructIR.ObjEnv :=
               fun p => match args[p]? with | some a => objs a | none => []
             have hcalleeEnvRel : EnvRel cvS calleeEnv (envi.update next (0 : F)) := by
               intro p
               show (envi.update next 0) (cvS p) = calleeEnv p
               simp only [cvS, calleeEnv]
               cases h : args[p]? with
               | some a =>
                 simp only
                 rw [localEnv_update_ne envi next (valSubst a) 0
                       (Nat.ne_of_lt (hValBound a))]
                 exact hEnvRel a
               | none =>
                 simp only [StructIR.LocalEnv.update, beq_iff_eq, if_true]
             have hcalleeObjRel : ObjRel coS calleeObjEnv obji := by
               intro p
               show obji (coS p) = calleeObjEnv p
               simp only [coS, calleeObjEnv]
               cases h : args[p]? with
               | some a => simp only; exact hObjRel a
               | none => simp only; exact hObjFresh next (Nat.le_refl _)
             let ic_pair := inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body
             let ic := ic_pair.1
             let na := ic_pair.2
             let tail_pair := inlineBody m i valSubst objSubst na rest
             let tail := tail_pair.1
             have hna_ge : next + 1 ≤ na :=
               inlineBody_next_ge m j cvS coS (next + 1) (m.structs j).constrain.body
             have hvalBound_na : SubstBounded valSubst na :=
               fun p => Nat.lt_of_lt_of_le (hValBound p) (Nat.le_trans (Nat.le_succ next) hna_ge)
             have hobjBound_na : SubstBounded objSubst na :=
               fun p => Nat.lt_of_lt_of_le (hObjBound p) (Nat.le_trans (Nat.le_succ next) hna_ge)
             have hEnvAfter : EnvRel valSubst envs
                 (StructInlineIR.runState w (envi.update next 0) obji ic).1 := by
               intro p
               have hlt : valSubst p < next + 1 := Nat.lt_succ_of_lt (hValBound p)
               obtain ⟨hf, _⟩ := frame_callee cvS coS (next + 1) (envi.update next 0) obji
                 hcvS hcoS (valSubst p) hlt
               rw [hf, localEnv_update_ne envi next (valSubst p) 0 (Nat.ne_of_lt (hValBound p))]
               exact hEnvRel p
             have hObjAfter : ObjRel objSubst objs
                 (StructInlineIR.runState w (envi.update next 0) obji ic).2 := by
               intro p
               have hlt : objSubst p < next + 1 := Nat.lt_succ_of_lt (hObjBound p)
               obtain ⟨_, ho⟩ := frame_callee cvS coS (next + 1) (envi.update next 0) obji
                 hcvS hcoS (objSubst p) hlt
               rw [ho]
               exact hObjRel p
             have hcallee_iff_j :
                 (StructIR.evalConstrainBody m w j calleeEnv calleeObjEnv
                   (m.structs j).constrain.body ↔
                  StructInlineIR.evalConstrainBody
                    (fun _ => { name := "", members := [],
                                constrain := { numParams := 0, body := [] } })
                    w j (envi.update next 0) obji ic) :=
               correct_callee cvS coS (next + 1) calleeEnv (envi.update next 0)
                 calleeObjEnv obji hcalleeEnvRel hcalleeObjRel hcvS hcoS
                 (objFresh_succ hObjFresh)
             -- Bridge w j ↔ w i via evalConstrainBody_irrel
             have hcallee_iff :
                 (StructIR.evalConstrainBody m w j calleeEnv calleeObjEnv
                   (m.structs j).constrain.body ↔
                  StructInlineIR.evalConstrainBody
                    (fun _ => { name := "", members := [],
                                constrain := { numParams := 0, body := [] } })
                    w i (envi.update next 0) obji ic) := by
               rw [hcallee_iff_j]
               exact Iff.of_eq (StructInlineIR.evalConstrainBody_irrel _ _ w j i _ _ _)
             have hObjFreshAfter : ObjFresh
                 (StructInlineIR.runState w (envi.update next 0) obji ic).2 na := by
               -- ic allocates positions in [next+1, na); positions ≥ na are untouched
               -- (by inlineBody_frame_above), so equal obji at that position,
               -- which is [] by objFresh_succ hObjFresh (since na ≥ next+1).
               intro p hp
               obtain ⟨_, h2⟩ := inlineBody_frame_above m w j cvS coS (next + 1)
                 (m.structs j).constrain.body (envi.update next 0) obji p hp
               rw [h2]
               exact hObjFresh p (Nat.le_trans (Nat.le_of_succ_le hna_ge) hp)
             have htail_iff : (StructIR.evalConstrainBody m w i envs objs rest ↔
                 StructInlineIR.evalConstrainBody
                   (fun _ => { name := "", members := [],
                               constrain := { numParams := 0, body := [] } })
                   w i (StructInlineIR.runState w (envi.update next 0) obji ic).1
                   (StructInlineIR.runState w (envi.update next 0) obji ic).2 tail) :=
               correct_rest valSubst objSubst na envs
                 (StructInlineIR.runState w (envi.update next 0) obji ic).1
                 objs (StructInlineIR.runState w (envi.update next 0) obji ic).2
                 hEnvAfter hObjAfter hvalBound_na hobjBound_na hObjFreshAfter
             -- Goal: source has eval (callee) ∧ eval rest
             -- Target has eval (zeroStmt :: ic ++ tail) which reduces to:
             --   (True) ∧ eval (ic ++ tail) on (envi.update next 0, obji)
             -- = (True) ∧ eval ic ∧ eval tail (after runState ic)
             change _ ↔ True ∧ StructInlineIR.evalConstrainBody
               (fun _ => { name := "", members := [],
                           constrain := { numParams := 0, body := [] } })
               w i (StructInlineIR.LocalEnv.update envi next 0) obji (ic ++ tail)
             rw [StructInlineIR.evalConstrainBody_append]
             constructor
             · intro ⟨hcallee, hrest⟩
               exact ⟨True.intro, hcallee_iff.mp hcallee, htail_iff.mp hrest⟩
             · intro ⟨_, hic_eval, htail_eval⟩
               exact ⟨hcallee_iff.mpr hic_eval, htail_iff.mpr htail_eval⟩

/-- After running inlined stmts, vars below `next` in env/objEnv are unchanged. -/
theorem inlineBody_frame (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (valSubst objSubst : Subst) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (envi : StructInlineIR.LocalEnv F) (obji : StructIR.ObjEnv)
    (hValBound : SubstBounded valSubst next)
    (hObjBound : SubstBounded objSubst next)
    (v : Nat) (hv : v < next) :
    (StructInlineIR.runState w envi obji (inlineBody m i valSubst objSubst next body).1).1 v =
      envi v ∧
    (StructInlineIR.runState w envi obji (inlineBody m i valSubst objSubst next body).1).2 v =
      obji v :=
  ((inlineBody_props m w (i.val + 1) i (Nat.lt_succ_self _) body).1
    valSubst objSubst next envi obji hValBound hObjBound v hv)

/-- inlineBody is correct: source eval ↔ inlined eval under substituted env. -/
theorem inlineBody_correct (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (valSubst objSubst : Subst) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (envs envi : StructIR.LocalEnv F) (objs obji : StructIR.ObjEnv)
    (hEnv : EnvRel valSubst envs envi) (hObj : ObjRel objSubst objs obji)
    (hValBound : SubstBounded valSubst next) (hObjBound : SubstBounded objSubst next)
    (hObjFresh : ObjFresh obji next) :
    StructIR.evalConstrainBody m w i envs objs body ↔
    StructInlineIR.evalConstrainBody
      (fun _ => { name := "", members := [], constrain := { numParams := 0, body := [] } })
      w i envi obji
      (inlineBody m i valSubst objSubst next body).1 := by
  have h := (inlineBody_props m w (i.val + 1) i (Nat.lt_succ_self _) body).2
  simp only [EnvRel, ObjRel, SubstBounded] at h
  exact h valSubst objSubst next envs envi objs obji hEnv hObj hValBound hObjBound hObjFresh

/-- Source `evalConstrainBody` depends on `env` and `objEnv` only at positions < bound,
    provided the body only references variables < bound.

    Used in the `call` case of `expandBody_correct`: the `ic` block of the expanded
    target mutates the outer env/objEnv only at positions ≥ next+1, so the tail `rest`
    (which lives below `next`) evaluates the same way on the original state and on the
    post-ic state. -/
theorem StructIR.evalConstrainBody_agree (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (env1 env2 : StructIR.LocalEnv F) (objEnv1 objEnv2 : StructIR.ObjEnv)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (bound : Nat) (hBound : allVarsBelow body bound)
    (hEnv : ∀ v, v < bound → env1 v = env2 v)
    (hObj : ∀ v, v < bound → objEnv1 v = objEnv2 v) :
    StructIR.evalConstrainBody m w i env1 objEnv1 body ↔
    StructIR.evalConstrainBody m w i env2 objEnv2 body := by
  induction body generalizing env1 env2 objEnv1 objEnv2 with
  | nil => simp [StructIR.evalConstrainBody]
  | cons stmt rest ih =>
    have hBoundRest : allVarsBelow rest bound :=
      fun s hs => hBound s (List.mem_cons_of_mem _ hs)
    have hStmt := hBound stmt List.mem_cons_self
    cases stmt with
    | feltAdd dest src1 src2 =>
      have : max dest (max src1 src2) < bound := hStmt
      have hd : dest < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) this
      have hs1 : src1 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) this
      have hs2 : src2 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) this
      simp only [StructIR.evalConstrainBody]
      rw [hEnv src1 hs1, hEnv src2 hs2]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ hObj)
      intro v hv
      simp only [StructIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hEnv v hv
    | feltSub dest src1 src2 =>
      have : max dest (max src1 src2) < bound := hStmt
      have hd : dest < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) this
      have hs1 : src1 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) this
      have hs2 : src2 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) this
      simp only [StructIR.evalConstrainBody]
      rw [hEnv src1 hs1, hEnv src2 hs2]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ hObj)
      intro v hv
      simp only [StructIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hEnv v hv
    | feltMul dest src1 src2 =>
      have : max dest (max src1 src2) < bound := hStmt
      have hd : dest < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) this
      have hs1 : src1 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) this
      have hs2 : src2 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) this
      simp only [StructIR.evalConstrainBody]
      rw [hEnv src1 hs1, hEnv src2 hs2]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ hObj)
      intro v hv
      simp only [StructIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hEnv v hv
    | feltDiv dest src1 src2 =>
      have : max dest (max src1 src2) < bound := hStmt
      have hd : dest < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) this
      have hs1 : src1 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) this
      have hs2 : src2 < bound := Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) this
      simp only [StructIR.evalConstrainBody]
      rw [hEnv src1 hs1, hEnv src2 hs2]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ hObj)
      intro v hv
      simp only [StructIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hEnv v hv
    | feltNeg dest src =>
      have hd : dest < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hStmt
      have hs : src < bound := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hStmt
      simp only [StructIR.evalConstrainBody]
      rw [hEnv src hs]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ hObj)
      intro v hv
      simp only [StructIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hEnv v hv
    | feltConst dest c =>
      have hd : dest < bound := hStmt
      simp only [StructIR.evalConstrainBody]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ hObj)
      intro v hv
      simp only [StructIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hEnv v hv
    | readMember dest self member =>
      have hd : dest < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hStmt
      have hs : self < bound := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hStmt
      simp only [StructIR.evalConstrainBody]
      rw [hObj self hs]
      refine and_congr_right' (ih _ _ _ _ hBoundRest ?_ ?_)
      · intro v hv
        simp only [StructIR.LocalEnv.update, beq_iff_eq]
        split
        · rfl
        · exact hEnv v hv
      · intro v hv
        simp only [StructIR.ObjEnv.update, beq_iff_eq]
        split
        · rfl
        · exact hObj v hv
    | constrainEq src1 src2 =>
      have hs1 : src1 < bound := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hStmt
      have hs2 : src2 < bound := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hStmt
      simp only [StructIR.evalConstrainBody]
      rw [hEnv src1 hs1, hEnv src2 hs2]
      exact and_congr_right' (ih _ _ _ _ hBoundRest hEnv hObj)
    | call target args =>
      -- Callee env is built from args, all of which are < bound; so callee state is identical
      -- on both sides, making the callee evaluation literally equal.
      have hargs : ∀ a ∈ args, a < bound := by
        intro a ha
        have : args.foldl max 0 < bound := hStmt
        exact Nat.lt_of_le_of_lt (foldl_max_mem id ha 0) this
      -- callee envs: pointwise equal on args-sourced positions.
      have hcEnv_pt : ∀ (p : Nat),
          (match args[p]? with
           | some arg => env1 arg
           | none     => (0 : F)) =
          (match args[p]? with
           | some arg => env2 arg
           | none     => (0 : F)) := by
        intro p
        cases h : args[p]? with
        | some a =>
          have ha : a ∈ args := by
            rw [List.getElem?_eq_some_iff] at h
            obtain ⟨_, _, rfl⟩ := h
            exact List.getElem_mem ..
          simp [hEnv a (hargs a ha)]
        | none => rfl
      have hcObj_pt : ∀ (p : Nat),
          (match args[p]? with
           | some arg => objEnv1 arg
           | none     => ([] : StructIR.InstancePath)) =
          (match args[p]? with
           | some arg => objEnv2 arg
           | none     => ([] : StructIR.InstancePath)) := by
        intro p
        cases h : args[p]? with
        | some a =>
          have ha : a ∈ args := by
            rw [List.getElem?_eq_some_iff] at h
            obtain ⟨_, _, rfl⟩ := h
            exact List.getElem_mem ..
          simp [hObj a (hargs a ha)]
        | none => rfl
      have hcEnv : (fun (param : Nat) =>
          match args[param]? with
          | some arg => env1 arg
          | none     => (0 : F)) =
          (fun (param : Nat) =>
          match args[param]? with
          | some arg => env2 arg
          | none     => 0) := funext hcEnv_pt
      have hcObj : (fun (param : Nat) =>
          match args[param]? with
          | some arg => objEnv1 arg
          | none     => ([] : StructIR.InstancePath)) =
          (fun (param : Nat) =>
          match args[param]? with
          | some arg => objEnv2 arg
          | none     => []) := funext hcObj_pt
      simp only [StructIR.evalConstrainBody]
      refine and_congr ?_ (ih _ _ _ _ hBoundRest hEnv hObj)
      -- The callee environments are pointwise equal → the calleeEnv functions are equal →
      -- the two `evalConstrainBody` calls are literally the same.
      have : evalConstrainBody m w ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          (fun param => match args[param]? with | some arg => env1 arg | none => 0)
          (fun param => match args[param]? with | some arg => objEnv1 arg | none => [])
          (m.structs _).constrain.body =
        evalConstrainBody m w ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          (fun param => match args[param]? with | some arg => env2 arg | none => 0)
          (fun param => match args[param]? with | some arg => objEnv2 arg | none => [])
          (m.structs _).constrain.body := by
        rw [hcEnv, hcObj]
      exact Iff.of_eq this

/-- expandBody_correct: for non-call stmts, source and target eval are identical.
    For call stmts, we rely on inlineBody_correct + frame isolation. -/
theorem expandBody_correct (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (env : StructIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (mi : StructInlineIR.Module n F) (ii : Fin n) (next : Nat)
    (body : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (hBound : allVarsBelow body next)
    (hFresh : ObjFresh objEnv next) :
    StructIR.evalConstrainBody m w i env objEnv body ↔
    StructInlineIR.evalConstrainBody mi w ii env objEnv (expandBody m i next body).1 := by
  induction body generalizing env objEnv next with
  | nil =>
    simp [StructIR.evalConstrainBody, StructInlineIR.evalConstrainBody, expandBody]
  | cons stmt rest ih =>
    have hBoundRest : allVarsBelow rest next :=
      fun s hs => hBound s (List.mem_cons_of_mem _ hs)
    have hStmt := hBound stmt List.mem_cons_self
    cases stmt with
    | feltAdd d s1 s2 =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | feltSub d s1 s2 =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | feltMul d s1 s2 =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | feltDiv d s1 s2 =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | feltNeg d s =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | feltConst d c =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | readMember d s mem =>
      have hd : d < next := by
        have h := hBound (ConstrainStmt.readMember d s mem) List.mem_cons_self
        simp only [allVarsBelowStmt, maxVarStmt] at h
        exact Nat.lt_of_le_of_lt (Nat.le_max_left d s) h
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest (objFresh_update_below hFresh hd _))
    | constrainEq s1 s2 =>
      simp only [StructIR.evalConstrainBody, expandBody, StructInlineIR.evalConstrainBody]
      exact and_congr_right' (ih _ _ _ hBoundRest hFresh)
    | call target args =>
      -- Source: callProp ∧ eval_source(rest) on (env, objEnv)
      -- Target: eval_target(feltConst next 0 :: ic ++ t) on (env, objEnv)
      --       = True ∧ eval_target(ic ++ t) on (env.update next 0, objEnv)
      --       = True ∧ eval_target(ic) on (env.update next 0, objEnv)
      --              ∧ eval_target(t) on (post-ic.env, post-ic.objEnv)    -- by append
      -- Match (1) callee ↔ ic via inlineBody_correct,
      --       (2) rest ↔ t via IH on na with post-ic state, bridged by agreement.
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let zv := next
      let cvS : Subst := fun p =>
        match args[p]? with | some a => a | none => zv
      let coS : Subst := fun p =>
        match args[p]? with | some a => a | none => zv
      -- Bound args by `next`.
      have hargs : ∀ a ∈ args, a < next := by
        intro a ha
        have hsf : args.foldl max 0 < next := hStmt
        exact Nat.lt_of_le_of_lt (foldl_max_mem id ha 0) hsf
      -- cvS, coS are bounded by next + 1.
      have hcvS : SubstBounded cvS (next + 1) := fun p => by
        simp only [cvS]
        cases h : args[p]? with
        | some a =>
          have : a ∈ args := by
            rw [List.getElem?_eq_some_iff] at h
            obtain ⟨_, _, rfl⟩ := h
            exact List.getElem_mem ..
          exact Nat.lt_succ_of_lt (hargs a this)
        | none => exact Nat.lt_succ_self _
      have hcoS : SubstBounded coS (next + 1) := fun p => by
        simp only [coS]
        cases h : args[p]? with
        | some a =>
          have : a ∈ args := by
            rw [List.getElem?_eq_some_iff] at h
            obtain ⟨_, _, rfl⟩ := h
            exact List.getElem_mem ..
          exact Nat.lt_succ_of_lt (hargs a this)
        | none => exact Nat.lt_succ_self _
      -- Source-side callee state.
      let calleeEnv : StructIR.LocalEnv F :=
        fun p => match args[p]? with | some a => env a | none => 0
      let calleeObjEnv : StructIR.ObjEnv :=
        fun p => match args[p]? with | some a => objEnv a | none => []
      -- The starting target env after the zero-stmt: env.update next 0.
      let envi0 : StructIR.LocalEnv F := env.update next 0
      -- EnvRel / ObjRel between source callee state and target starting state.
      have hEnvRel : EnvRel cvS calleeEnv envi0 := by
        intro p
        simp only [cvS, calleeEnv, envi0]
        cases h : args[p]? with
        | some a =>
          simp only
          have : a < next := hargs a (by
            rw [List.getElem?_eq_some_iff] at h
            obtain ⟨_, _, rfl⟩ := h
            exact List.getElem_mem ..)
          exact localEnv_update_ne env next a 0 (Nat.ne_of_lt this)
        | none =>
          simp only [zv, StructIR.LocalEnv.update, beq_iff_eq, if_true]
      have hObjRel : ObjRel coS calleeObjEnv objEnv := by
        intro p
        simp only [coS, calleeObjEnv]
        cases h : args[p]? with
        | some a => simp only
        | none =>
          simp only [zv]
          exact hFresh next (Nat.le_refl _)
      -- inlineBody output + next.
      let ic_pair := inlineBody m j cvS coS (next + 1) (m.structs j).constrain.body
      let ic := ic_pair.1
      let na := ic_pair.2
      let tail_pair := expandBody m i na rest
      let t := tail_pair.1
      have hna_ge : next + 1 ≤ na :=
        inlineBody_next_ge m j cvS coS (next + 1) (m.structs j).constrain.body
      -- Frame: after running ic, positions < next+1 unchanged from envi0/objEnv.
      have hframe := fun v hv =>
        inlineBody_frame m w j cvS coS (next + 1) (m.structs j).constrain.body
          envi0 objEnv hcvS hcoS v hv
      -- inlineBody correctness: callee eval ↔ ic eval, bridged via evalConstrainBody_irrel.
      have hcall_iff_j :
          StructIR.evalConstrainBody m w j calleeEnv calleeObjEnv
            (m.structs j).constrain.body ↔
          StructInlineIR.evalConstrainBody
            (fun _ => { name := "", members := [], constrain := { numParams := 0, body := [] } })
            w j envi0 objEnv ic :=
        inlineBody_correct m w j cvS coS (next + 1) (m.structs j).constrain.body
          calleeEnv envi0 calleeObjEnv objEnv hEnvRel hObjRel hcvS hcoS (objFresh_succ hFresh)
      have hcall_iff :
          StructIR.evalConstrainBody m w j calleeEnv calleeObjEnv
            (m.structs j).constrain.body ↔
          StructInlineIR.evalConstrainBody mi w ii envi0 objEnv ic := by
        rw [hcall_iff_j]
        exact Iff.of_eq (StructInlineIR.evalConstrainBody_irrel _ _ w j ii _ _ _)
      -- ObjFresh after running ic: positions ≥ na in post-ic.objEnv are [].
      have hObjFreshAfter :
          ObjFresh (StructInlineIR.runState w envi0 objEnv ic).2 na := by
        intro v hv
        obtain ⟨_, h2⟩ := inlineBody_frame_above m w j cvS coS (next + 1)
          (m.structs j).constrain.body envi0 objEnv v hv
        rw [h2]
        exact hFresh v (Nat.le_trans (Nat.le_of_succ_le hna_ge) hv)
      -- allVarsBelow rest na (since na ≥ next+1 > max used in rest).
      have hBoundRest_na : allVarsBelow rest na := fun s hs => by
        have := hBoundRest s hs
        exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.le_succ next) hna_ge)
      -- At positions < next, post-ic state agrees with original.
      have hEnv_post_eq : ∀ v, v < next →
          (StructInlineIR.runState w envi0 objEnv ic).1 v = env v := by
        intro v hv
        obtain ⟨h1, _⟩ := hframe v (Nat.lt_succ_of_lt hv)
        rw [h1]
        exact localEnv_update_ne env next v 0 (Nat.ne_of_lt hv)
      have hObj_post_eq : ∀ v, v < next →
          (StructInlineIR.runState w envi0 objEnv ic).2 v = objEnv v := by
        intro v hv
        obtain ⟨_, h2⟩ := hframe v (Nat.lt_succ_of_lt hv)
        exact h2
      -- IH at post-ic state and next := na.
      have htail_iff := ih (StructInlineIR.runState w envi0 objEnv ic).1
        (StructInlineIR.runState w envi0 objEnv ic).2 na hBoundRest_na hObjFreshAfter
      -- Agreement bridge: source eval of rest at (env, objEnv) ↔ at post-ic state.
      have hrest_agree := StructIR.evalConstrainBody_agree m w i
        env (StructInlineIR.runState w envi0 objEnv ic).1
        objEnv (StructInlineIR.runState w envi0 objEnv ic).2
        rest next hBoundRest
        (fun v hv => (hEnv_post_eq v hv).symm)
        (fun v hv => (hObj_post_eq v hv).symm)
      -- Unfold source and target eval.
      simp only [StructIR.evalConstrainBody, expandBody]
      change (_ ∧ _) ↔ StructInlineIR.evalConstrainBody mi w ii env objEnv
        (StructInlineIR.ConstrainStmt.feltConst next 0 :: ic ++ t)
      rw [show (StructInlineIR.ConstrainStmt.feltConst next 0 :: ic ++ t) =
            (StructInlineIR.ConstrainStmt.feltConst (F := F) next 0 :: (ic ++ t)) from rfl]
      simp only [StructInlineIR.evalConstrainBody]
      rw [StructInlineIR.evalConstrainBody_append]
      -- Goal:
      --   callProp ∧ eval_source(rest) on (env, objEnv)
      -- ↔ True ∧ eval_target(ic) on (envi0, objEnv)
      --        ∧ eval_target(t) on (post-ic)
      constructor
      · intro ⟨hcall, hrest⟩
        refine ⟨trivial, hcall_iff.mp hcall, htail_iff.mp (hrest_agree.mp hrest)⟩
      · intro ⟨_, hic, htail⟩
        refine ⟨hcall_iff.mpr hic, hrest_agree.mpr (htail_iff.mpr htail)⟩

/-! ## Preservation and reflection -/

theorem preservation (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (h : StructIR.satisfies ws m) :
    StructInlineIR.satisfies ws (compile m) := by
  simp only [StructIR.satisfies, StructInlineIR.satisfies, compile, compileStruct] at *
  exact (expandBody_correct _ _ _ _ _ _ _ _ _ (maxVarBody_bound _)
    (fun v _ => by simp [StructIR.ObjEnv.update, beq_iff_eq])).mp h

theorem reflection (m : StructIR.Module (n + 1) F)
    (wi : StructInlineIR.Witness F)
    (h : StructInlineIR.satisfies wi (compile m)) :
    StructIR.satisfies wi m := by
  simp only [StructIR.satisfies, StructInlineIR.satisfies, compile, compileStruct] at *
  exact (expandBody_correct _ _ _ _ _ _ _ _ _ (maxVarBody_bound _)
    (fun v _ => by simp [StructIR.ObjEnv.update, beq_iff_eq])).mpr h

instance CorrectPass (n : Nat) (F : Type) [Field F] :
    PresReflPass (StructIR.Language n F) (StructInlineIR.Language n F) where
  compile := compile
  witnessRel := witnessRel
  preservation := by
    intro ws p hs
    exact ⟨ws, witnessRel_refl p ws, preservation p ws hs⟩
  reflection := by
    intro wi p hs
    exact ⟨wi, witnessRel_refl p wi, reflection p wi hs⟩

instance Pass (n : Nat) (F : Type) [Field F] :
    Pass (StructIR.Language n F) (StructInlineIR.Language n F) where
  compile := compile
  witnessRel := witnessRel

end StructIRToStructInlineIR
