/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Languages.StructIR

/-!
# StructIR Freshening Support

Freshening, renaming, and environment-agreement lemmas for `StructIR`
constrain bodies.

Freshening, renaming, and environment-agreement support extracted from older
substitution-semantics development, kept because active executable compiler and
reflection proofs depend on it.
-/

namespace StructIRFreshen

open StructIR

variable {F : Type} [Field F] {n : Nat}

omit [Field F] in
/-- Maximum local variable mentioned by single constrain statement. -/
def maxVarStmt {i : Fin n} {nm : Nat} (stmt : StructIR.ConstrainStmt n i F nm) : Nat :=
  match stmt with
  | .feltAdd d s1 s2 | .feltSub d s1 s2
  | .feltMul d s1 s2 | .feltDiv d s1 s2 => max d (max s1 s2)
  | .feltNeg d s | .readMember d s _ => max d s
  | .feltConst d _ => d
  | .constrainEq s1 s2 => max s1 s2
  | .call _ args => args.foldl max 0

omit [Field F] in
/-- Maximum local variable mentioned anywhere in constrain body. -/
def maxVarBody {i : Fin n} {nm : Nat}
    (body : List (StructIR.ConstrainStmt n i F nm)) : Nat :=
  body.foldl (fun acc s => max acc (maxVarStmt s)) 0

/-- Rename all locals in constrain statement by map `ρ`. -/
def renameStmt {i : Fin n} {nm : Nat} (ρ : Nat → Nat)
    (stmt : StructIR.ConstrainStmt n i F nm) : StructIR.ConstrainStmt n i F nm :=
  match stmt with
  | .feltAdd d s1 s2 => .feltAdd (ρ d) (ρ s1) (ρ s2)
  | .feltSub d s1 s2 => .feltSub (ρ d) (ρ s1) (ρ s2)
  | .feltMul d s1 s2 => .feltMul (ρ d) (ρ s1) (ρ s2)
  | .feltDiv d s1 s2 => .feltDiv (ρ d) (ρ s1) (ρ s2)
  | .feltNeg d s => .feltNeg (ρ d) (ρ s)
  | .feltConst d c => .feltConst (ρ d) c
  | .readMember d s member => .readMember (ρ d) (ρ s) member
  | .constrainEq s1 s2 => .constrainEq (ρ s1) (ρ s2)
  | .call target args => .call target (args.map ρ)

/-- Rename all locals in constrain body by map `ρ`. -/
def renameBody {i : Fin n} {nm : Nat} (ρ : Nat → Nat)
    (body : List (StructIR.ConstrainStmt n i F nm)) : List (StructIR.ConstrainStmt n i F nm) :=
  body.map (renameStmt ρ)

omit [Field F] in
/-- Freshen constrain body into block starting at `nextFresh`. -/
def freshenBody {i : Fin n} {nm : Nat} (nextFresh : Nat)
    (body : List (StructIR.ConstrainStmt n i F nm)) :
    List (StructIR.ConstrainStmt n i F nm) × Nat :=
  let ρ : Nat → Nat := fun v => nextFresh + v
  let blockSize := maxVarBody body + 1
  (renameBody ρ body, nextFresh + blockSize)

/-- Variable-renaming map used by freshening. -/
def freshMap (nextFresh : Nat) : Nat → Nat := fun v => nextFresh + v

/-- Every freshened variable index is at least `nextFresh`. -/
theorem freshMap_ge (nextFresh v : Nat) : nextFresh ≤ freshMap nextFresh v := by
  simp [freshMap]

/-- Freshening by left-addition is injective. -/
theorem freshMap_injective (nextFresh : Nat) : Function.Injective (freshMap nextFresh) := by
  intro a b h
  exact Nat.add_left_cancel h

omit [Field F] in
/-- Freshening never decreases freshness counter. -/
theorem freshenBody_next_ge {i : Fin n} {nm : Nat}
    (nextFresh : Nat) (body : List (StructIR.ConstrainStmt n i F nm)) :
    nextFresh ≤ (freshenBody nextFresh body).2 := by
  simp [freshenBody]

omit [Field F] in
/-- Freshening always strictly advances freshness counter. -/
theorem freshenBody_next_gt {i : Fin n} {nm : Nat}
    (nextFresh : Nat) (body : List (StructIR.ConstrainStmt n i F nm)) :
    nextFresh < (freshenBody nextFresh body).2 := by
  simp [freshenBody]

/-- Variables below `nextFresh` cannot equal freshened variables. -/
theorem fresh_old_disjoint (nextFresh x v : Nat) (hx : x < nextFresh) :
    x ≠ freshMap nextFresh v := by
  intro h
  have : nextFresh ≤ x := by simpa [h] using freshMap_ge nextFresh v
  omega

/-- Reindexing a call-argument lookup commutes with post-composition by `ρ`. -/
lemma get_map_lemma (ρ : ℕ → ℕ) (args : List ℕ) (env : ℕ → F) (n : ℕ) :
    (match Option.map ρ (args[n]?) with | some a => env a | none => 0) =
    (match args[n]? with | some a => (env ∘ ρ) a | none => 0) := by
  induction args generalizing n with
  | nil => simp
  | cons a args ih => cases n with | zero => simp | succ n => simp [ih n]

/-- Object-environment version of `get_map_lemma`. -/
lemma get_map_lemma_obj (ρ : ℕ → ℕ) (args : List ℕ) (env : ℕ → List ℕ) (n : ℕ) :
    (match Option.map ρ (args[n]?) with | some a => env a | none => []) =
    (match args[n]? with | some a => (env ∘ ρ) a | none => []) := by
  induction args generalizing n with
  | nil => simp
  | cons a args ih => cases n with | zero => simp | succ n => simp [ih n]

set_option linter.unusedSectionVars false in
/-- Post-composing updated local environment with injective renaming. -/
lemma env_update_rename_comm (env : LocalEnv F) (dest : LocalVar) (val : F)
    (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ) :
    (env.update (ρ dest) val) ∘ ρ = LocalEnv.update (env ∘ ρ) dest val := by
  funext x
  simp only [Function.comp_apply, LocalEnv.update]
  by_cases hx : x = dest
  · subst x
    simp
  · have hne : ρ x ≠ ρ dest := by intro hEq; exact hx (hρ_inj hEq)
    simp [hx, hne]

/-- Object-environment version of `env_update_rename_comm`. -/
lemma objEnv_update_rename_comm (objEnv : ObjEnv) (dest : LocalVar) (path : InstancePath)
    (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ) :
    (objEnv.update (ρ dest) path) ∘ ρ = ObjEnv.update (objEnv ∘ ρ) dest path := by
  funext x
  simp only [Function.comp_apply, ObjEnv.update]
  by_cases hx : x = dest
  · subst x
    simp
  · have hne : ρ x ≠ ρ dest := by intro hEq; exact hx (hρ_inj hEq)
    simp [hx, hne]

set_option linter.flexible false in
/-- Renaming a constrain body by injective `ρ` commutes with evaluation. -/
lemma evalConstrainBody_rename (m : Module n F) (w : Witness F) (i : Fin n)
    (env : LocalEnv F) (objEnv : ObjEnv) (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ)
    (body : List (ConstrainStmt n i F (m.structs i).members.length)) :
    evalConstrainBody m w i env objEnv (renameBody ρ body) ↔
    evalConstrainBody m w i (env ∘ ρ) (objEnv ∘ ρ) body := by
  induction body generalizing env objEnv with
  | nil => simp [evalConstrainBody, renameBody]
  | cons stmt body ih =>
    rename_i ih
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) + env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) + env (ρ src2))) objEnv)
    | feltSub dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) - env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) - env (ρ src2))) objEnv)
    | feltMul dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) * env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) * env (ρ src2))) objEnv)
    | feltDiv dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      intro hnz
      simpa [env_update_rename_comm env dest (env (ρ src1) * (env (ρ src2))⁻¹) ρ hρ_inj]
        using
        (ih (env.update (ρ dest) (env (ρ src1) * (env (ρ src2))⁻¹)) objEnv)
    | feltNeg dest src =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (-(env (ρ src))) ρ hρ_inj] using
        (ih (env.update (ρ dest) (-(env (ρ src)))) objEnv)
    | feltConst dest c =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest c ρ hρ_inj] using
        (ih (env.update (ρ dest) c) objEnv)
    | readMember dest self member =>
      let path := objEnv (ρ self)
      let val := w (path, member.val)
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest val ρ hρ_inj,
        objEnv_update_rename_comm objEnv dest (path ++ [member.val]) ρ hρ_inj,
        Function.comp_apply] using
        (ih (env.update (ρ dest) val) (objEnv.update (ρ dest) (path ++ [member.val])))
    | constrainEq src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      intro h_eq
      simpa [renameBody] using (ih env objEnv)
    | call target args =>
      simp [evalConstrainBody, renameBody, renameStmt]
      have h_callee_env_eq :
          (fun param : Nat => match Option.map ρ args[param]? with | some a => env a | none => 0) =
          (fun param : Nat => match args[param]? with | some a => (env ∘ ρ) a | none => 0) := by
        apply funext
        intro n
        apply get_map_lemma ρ args env n
      have h_callee_objEnv_eq :
          (fun param : Nat =>
            match Option.map ρ args[param]? with
            | some a => objEnv a
            | none => []) =
          (fun param : Nat =>
            match args[param]? with
            | some a => (objEnv ∘ ρ) a
            | none => []) := by
        apply funext
        intro n
        apply get_map_lemma_obj ρ args objEnv n
      constructor
      · rintro ⟨hcall, h⟩
        refine ⟨h_callee_objEnv_eq ▸ h_callee_env_eq ▸ hcall, (ih env objEnv).mp h⟩
      · rintro ⟨hcall, h⟩
        refine ⟨h_callee_objEnv_eq.symm ▸ h_callee_env_eq.symm ▸ hcall,
          (ih env objEnv).mpr h⟩

private lemma list_all_true_of_mem {α : Type}
    (xs : List α) (p : α → Bool) (x : α)
    (hall : xs.all p = true) (hx : x ∈ xs) : p x = true := by
  induction xs generalizing x with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.all, Bool.and_eq_true] at hall
    rcases hall with ⟨hy, hys⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hy
    · exact ih _ hys hx

/-- General environment-agreement lemma for SSA constrain bodies. -/
private lemma evalConstrainBody_env_agree_on_init_aux
    (m : Module n F) (w : StructIR.Witness F) (i : Fin n) :
    ∀ (body : List (ConstrainStmt n i F (m.structs i).members.length))
      (init : LocalVar → Bool)
      (env1 env2 : LocalEnv F) (objEnv : ObjEnv),
      StructIR.isSSA init body = true →
      (∀ v, init v = true → env1 v = env2 v) →
      (evalConstrainBody m w i env1 objEnv body ↔
        evalConstrainBody m w i env2 objEnv body) := by
  intro body
  induction body with
  | nil =>
    intro init env1 env2 objEnv _ _
    simp [evalConstrainBody]
  | cons stmt rest ih =>
    intro init env1 env2 objEnv hSSA hAgree
    simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
    obtain ⟨hReads, hSSA'⟩ := hSSA
    have hReadsAgree : ∀ v ∈ stmt.reads, env1 v = env2 v := by
      intro v hv
      exact hAgree v (list_all_true_of_mem _ _ _ hReads hv)
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 + env2 src2)) v =
          (env2.update dest (env2 src1 + env2 src2)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      exact ih _ _ _ _ hSSA'' hext
    | feltSub dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 - env2 src2)) v =
          (env2.update dest (env2 src1 - env2 src2)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      exact ih _ _ _ _ hSSA'' hext
    | feltMul dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 * env2 src2)) v =
          (env2.update dest (env2 src1 * env2 src2)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      exact ih _ _ _ _ hSSA'' hext
    | feltDiv dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 * (env2 src2)⁻¹)) v =
          (env2.update dest (env2 src1 * (env2 src2)⁻¹)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      constructor
      · rintro ⟨hnz, hrest⟩
        exact ⟨hnz, (ih _ _ _ _ hSSA'' hext).mp hrest⟩
      · rintro ⟨hnz, hrest⟩
        exact ⟨hnz, (ih _ _ _ _ hSSA'' hext).mpr hrest⟩
    | feltNeg dest src =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs : env1 src = env2 src := hReadsAgree src rfl
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (-(env2 src))) v =
          (env2.update dest (-(env2 src))) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      exact ih _ _ _ _ hSSA'' hext
    | feltConst dest c =>
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      have hext : ∀ v, (fun x => init x || x == dest) v = true →
          (env1.update dest c) v = (env2.update dest c) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      simp only [evalConstrainBody, true_and]
      exact ih _ _ _ _ hSSA'' hext
    | readMember dest self member =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hself : env1 self = env2 self := hReadsAgree self rfl
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      have hext : ∀ v, (fun x => init x || x == dest) v = true →
          (env1.update dest (w (objEnv self, member.val))) v =
          (env2.update dest (w (objEnv self, member.val))) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq
            simp
          · simp only [beq_iff_eq, heq, if_false]
            exact hAgree _ hv
        · subst hv
          simp
      simp only [evalConstrainBody, true_and]
      exact ih _ _ _ _ hSSA'' hext
    | constrainEq src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest] at hSSA'
      simp only [evalConstrainBody, hs1, hs2]
      constructor
      · rintro ⟨heq, hrest⟩
        exact ⟨heq, (ih _ _ _ _ hSSA' hAgree).mp hrest⟩
      · rintro ⟨heq, hrest⟩
        exact ⟨heq, (ih _ _ _ _ hSSA' hAgree).mpr hrest⟩
    | call target args =>
      have hargs : ∀ a ∈ args, env1 a = env2 a := by
        intro a ha
        exact hReadsAgree a (by simpa [ConstrainStmt.reads] using ha)
      have hCalleeEnv :
          (fun param : Nat =>
            match args[param]? with | some arg => env1 arg | none => (0 : F)) =
          (fun param : Nat =>
            match args[param]? with | some arg => env2 arg | none => (0 : F)) := by
        funext param
        cases h : args[param]? with
        | none => rfl
        | some arg =>
          have : arg ∈ args := List.mem_of_getElem? h
          exact hargs arg this
      simp only [ConstrainStmt.dest] at hSSA'
      simp only [evalConstrainBody]
      constructor
      · rintro ⟨hcall, hrest⟩
        refine ⟨?_, (ih _ _ _ _ hSSA' hAgree).mp hrest⟩
        exact hCalleeEnv ▸ hcall
      · rintro ⟨hcall, hrest⟩
        refine ⟨?_, (ih _ _ _ _ hSSA' hAgree).mpr hrest⟩
        exact hCalleeEnv.symm ▸ hcall

/-- If two envs agree on parameter variables, SSA evaluation is identical. -/
lemma evalConstrainBody_env_agree_on_init
    (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (env1 env2 : LocalEnv F) (objEnv : ObjEnv)
    (body : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA (fun v => v < (m.structs i).constrain.numParams) body = true)
    (hAgree : ∀ v,
      (fun v => v < (m.structs i).constrain.numParams) v = true → env1 v = env2 v) :
    evalConstrainBody m w i env1 objEnv body ↔ evalConstrainBody m w i env2 objEnv body := by
  refine evalConstrainBody_env_agree_on_init_aux m w i body _ env1 env2 objEnv hSSA ?_
  intro v hv
  exact hAgree v (by simpa using hv)

end StructIRFreshen
