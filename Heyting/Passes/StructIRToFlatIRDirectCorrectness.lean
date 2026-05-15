import Heyting.Core.Pass
import Heyting.Core.VarIdEncoding
import Heyting.Languages.FlatIR
import Heyting.Languages.FlatIRSubst
import Heyting.Languages.StructIR
import Heyting.Languages.StructIRSubst
import Heyting.Passes.StructIRToFlatIRDirect
import Heyting.Passes.StructIRToFlatIRDirectSim

open StructIR
open FlatIR

namespace StructIRToFlatIRDirect

variable {F : Type} [Field F] {n : Nat}

private lemma get_map_lemma (ρ : ℕ → ℕ) (args : List ℕ) (env : ℕ → F) (n : ℕ) :
    (match Option.map ρ (args[n]?) with | some a => env a | none => 0) =
    (match args[n]? with | some a => (env ∘ ρ) a | none => 0) := by
  induction args generalizing n with
  | nil => simp
  | cons a args ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih n]

private lemma get_map_lemma_obj (ρ : ℕ → ℕ) (args : List ℕ) (env : ℕ → List ℕ) (n : ℕ) :
    (match Option.map ρ (args[n]?) with | some a => env a | none => []) =
    (match args[n]? with | some a => (env ∘ ρ) a | none => []) := by
  induction args generalizing n with
  | nil => simp
  | cons a args ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih n]

/-- The natural FlatIR witness derived from a StructIR witness via `decode`. -/
noncomputable def wt' (w : StructIR.Witness F) : FlatIR.Witness F :=
  fun v => w (VarIdEncoding.decode v)

/-- FlatIR.satisfies decomposes on cons. -/
lemma satisfies_cons (w : FlatIR.Witness F) (i : FlatIR.Instr F) (p : FlatIR.Program F) :
    FlatIR.satisfies w (i :: p) ↔ FlatIR.satisfiesInstr w i ∧ FlatIR.satisfies w p := by
  constructor
  · intro h
    refine ⟨h i (by simp), ?_⟩
    intro j hj; exact h j (by simp [hj])
  · intro ⟨hi, hp⟩ j hj
    rcases List.mem_cons.mp hj with rfl | hjp
    · exact hi
    · exact hp j hjp

/-- FlatIR.satisfies decomposes on append. -/
lemma satisfies_append (w : FlatIR.Witness F) (p1 p2 : FlatIR.Program F) :
    FlatIR.satisfies w (p1 ++ p2) ↔ FlatIR.satisfies w p1 ∧ FlatIR.satisfies w p2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj; exact h j (by simp [hj])
    · intro j hj; exact h j (by simp [hj])
  · intro ⟨h1, h2⟩ j hj
    rcases List.mem_append.mp hj with hj1 | hj2
    · exact h1 j hj1
    · exact h2 j hj2

/-- LocalEnv.update is identity when value matches existing entry. -/
lemma localEnv_update_self (env : LocalEnv F) (x : Nat) (v : F) (h : env x = v) :
    env.update x v = env := by
  funext k
  simp only [LocalEnv.update]
  by_cases hk : k = x
  · subst hk
    simp only [beq_self_eq_true, if_true, h]
  · have : (k == x) = false := by simp [hk]
    rw [this]; simp

/-- When env update at ρ(dest) is post-composed with ρ, it equals composition with
    update at dest.  Requires ρ injective. -/
lemma env_update_rename_comm (env : LocalEnv F) (dest : LocalVar) (val : F)
    (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ) :
    (env.update (ρ dest) val) ∘ ρ = LocalEnv.update (env ∘ ρ) dest val := by
  funext x
  simp only [Function.comp_apply, LocalEnv.update]
  by_cases hx : x = dest
  · subst x; simp
  · have hne : ρ x ≠ ρ dest := by
      intro hEq
      exact hx (hρ_inj hEq)
    simp [hx, hne]

/-- Same for ObjEnv updates. -/
lemma objEnv_update_rename_comm (objEnv : ObjEnv) (dest : LocalVar) (path : InstancePath)
    (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ) :
    (objEnv.update (ρ dest) path) ∘ ρ = ObjEnv.update (objEnv ∘ ρ) dest path := by
  funext x
  simp only [Function.comp_apply, ObjEnv.update]
  by_cases hx : x = dest
  · subst x; simp
  · have hne : ρ x ≠ ρ dest := by
      intro hEq
      exact hx (hρ_inj hEq)
    simp [hx, hne]

/-- Renaming all variables in a body by an injective ρ commutes with evaluation,
    provided the env and objEnv are also adjusted by ρ on the right (original-index)
    side.  That is:

    `eval(env, objEnv)[renameBody ρ body] ↔ eval(env ∘ ρ, objEnv ∘ ρ)[body]`. -/
lemma evalConstrainBody_rename (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (env : LocalEnv F) (objEnv : ObjEnv) (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ)
    (body : List (ConstrainStmt n i F (m.structs i).members.length)) :
    evalConstrainBody m w i env objEnv (StructIRSubst.renameBody ρ body) ↔
    evalConstrainBody m w i (env ∘ ρ) (objEnv ∘ ρ) body := by
  induction body generalizing env objEnv with
  | nil =>
    simp [evalConstrainBody, StructIRSubst.renameBody]
  | cons stmt body ih =>
    rename_i ih
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) + env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) + env (ρ src2))) objEnv)
    | feltSub dest src1 src2 =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) - env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) - env (ρ src2))) objEnv)
    | feltMul dest src1 src2 =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) * env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) * env (ρ src2))) objEnv)
    | feltDiv dest src1 src2 =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      intro hnz
      simpa [env_update_rename_comm env dest (env (ρ src1) * (env (ρ src2))⁻¹) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) * (env (ρ src2))⁻¹)) objEnv)
    | feltNeg dest src =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      simpa [env_update_rename_comm env dest (-(env (ρ src))) ρ hρ_inj] using
        (ih (env.update (ρ dest) (-(env (ρ src)))) objEnv)
    | feltConst dest c =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      simpa [env_update_rename_comm env dest c ρ hρ_inj] using
        (ih (env.update (ρ dest) c) objEnv)
    | readMember dest self member =>
      let path := objEnv (ρ self)
      let val := w (path, member.val)
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      simpa [
          env_update_rename_comm env dest val ρ hρ_inj,
          objEnv_update_rename_comm objEnv dest (path ++ [member.val]) ρ hρ_inj,
          Function.comp_apply
        ] using
        (ih (env.update (ρ dest) val) (objEnv.update (ρ dest) (path ++ [member.val])))
    | constrainEq src1 src2 =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      intro h_eq
      simpa [StructIRSubst.renameBody] using (ih env objEnv)
    | call target args =>
      simp [evalConstrainBody, StructIRSubst.renameBody, StructIRSubst.renameStmt]
      have h_callee_env_eq :
        (fun param : Nat => match Option.map ρ args[param]? with | some a => env a | none => 0) =
        (fun param : Nat => match args[param]? with | some a => (env ∘ ρ) a | none => 0) := by
        apply funext; intro n; apply get_map_lemma ρ args env n
      have h_callee_objEnv_eq :
        (fun param : Nat => match Option.map ρ args[param]? with | some a => objEnv a | none => []) =
        (fun param : Nat => match args[param]? with | some a => (objEnv ∘ ρ) a | none => []) := by
        apply funext; intro n; apply get_map_lemma_obj ρ args objEnv n
      constructor
      · rintro ⟨hcall, h⟩
        refine ⟨h_callee_objEnv_eq ▸ h_callee_env_eq ▸ hcall, (ih env objEnv).mp h⟩
      · rintro ⟨hcall, h⟩
        refine ⟨h_callee_objEnv_eq.symm ▸ h_callee_env_eq.symm ▸ hcall, (ih env objEnv).mpr h⟩

/-- If two local-variable environments agree on all parameter variables (those
    below `numParams`), and the body is in SSA form, then evaluation with
    either env yields the same result.

    The `hSSA` condition is the `isSSA` Bool predicate returning `true`.  The
    `hAgree` condition takes a Bool-level `init v = true` (matching the `isSSA`
    convention) and must return equality of the two envs at `v`. -/
lemma evalConstrainBody_env_agree_on_init (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (env1 env2 : LocalEnv F) (objEnv : ObjEnv)
    (body : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA (fun v => v < (m.structs i).constrain.numParams) body = true)
    (hAgree : ∀ v, (fun v => v < (m.structs i).constrain.numParams) v = true → env1 v = env2 v) :
    evalConstrainBody m w i env1 objEnv body ↔ evalConstrainBody m w i env2 objEnv body := by
  sorry

/-- Extract per-param equality from `compileParamBindings` satisfaction (inner loop). -/
private lemma compileParamBindings_go_env_agree (args : List Nat) (nextFresh : Nat)
    (wt : FlatIR.Witness F) (idx remaining : Nat)
    (hParam : FlatIR.satisfies wt
      (compileParamBindings.go (F := F) args (StructIRSubst.freshMap nextFresh) idx remaining))
    (param : Nat) (hlt : param < remaining) :
    wt (StructIRSubst.freshMap nextFresh (idx + param)) =
    match args[idx + param]? with | some arg => wt arg | none => 0 := by
  induction remaining generalizing idx param with
  | zero => omega
  | succ k ih =>
    simp only [compileParamBindings.go] at hParam
    rw [satisfies_append] at hParam
    obtain ⟨hHead, hRest⟩ := hParam
    cases param with
    | zero =>
      simp only [Nat.add_zero]
      split at hHead
      · rename_i arg h
        simp only [satisfies_cons] at hHead
        obtain ⟨hI, _⟩ := hHead
        simp only [FlatIR.satisfiesInstr] at hI
        simp [h, hI]
      · rename_i h
        simp only [satisfies_cons] at hHead
        obtain ⟨hI, _⟩ := hHead
        simp only [FlatIR.satisfiesInstr] at hI
        simp [h, hI]
    | succ p =>
      have hlt' : p < k := Nat.lt_of_succ_lt_succ hlt
      have := ih (idx + 1) hRest p hlt'
      simp only [Nat.add_assoc, Nat.add_comm 1 p] at this ⊢
      exact this

/-- From `compileParamBindings` satisfaction, extract per-param equality. -/
private lemma compileParamBindings_env_agree (numParams : Nat) (args : List Nat) (nextFresh : Nat)
    (wt : FlatIR.Witness F)
    (hParam : FlatIR.satisfies wt
      (compileParamBindings numParams args (StructIRSubst.freshMap nextFresh)))
    (param : Nat) (hlt : param < numParams) :
    wt (StructIRSubst.freshMap nextFresh param) =
    match args[param]? with | some arg => wt arg | none => 0 := by
  unfold compileParamBindings at hParam
  have := compileParamBindings_go_env_agree args nextFresh wt 0 numParams hParam param hlt
  simpa using this

/-- Helper: body reflection for a fixed i, given IH for all j < i. -/
private theorem body_reflection_wt_aux (m : Module n F) (w : StructIR.Witness F)
    (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams) (m.structs j).constrain.body = true)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      FlatIR.satisfies (wt' w) (compileConstrainBody m j objEnv nextFresh stmts).1 →
      evalConstrainBody m w j (wt' w) objEnv stmts)
    (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSat : FlatIR.satisfies (wt' w) (compileConstrainBody m i objEnv nextFresh stmts).1) :
    evalConstrainBody m w i (wt' w) objEnv stmts := by
  induction stmts generalizing objEnv nextFresh with
  | nil => simp [evalConstrainBody]
  | cons stmt rest ih =>
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp only [evalConstrainBody, true_and]
      rw [localEnv_update_self _ _ _ hI]
      exact ih _ _ hRest
    | feltSub dest src1 src2 =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp only [evalConstrainBody, true_and]
      rw [localEnv_update_self _ _ _ hI]
      exact ih _ _ hRest
    | feltMul dest src1 src2 =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp only [evalConstrainBody, true_and]
      rw [localEnv_update_self _ _ _ hI]
      exact ih _ _ hRest
    | feltDiv dest src1 src2 =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      obtain ⟨hnz, hdest⟩ := hI
      simp only [evalConstrainBody]
      refine ⟨hnz, ?_⟩
      rw [localEnv_update_self _ _ _ hdest]
      exact ih _ _ hRest
    | feltNeg dest src =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp only [evalConstrainBody, true_and]
      rw [localEnv_update_self _ _ _ hI]
      exact ih _ _ hRest
    | feltConst dest c =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp only [evalConstrainBody, true_and]
      rw [localEnv_update_self _ _ _ hI]
      exact ih _ _ hRest
    | readMember dest self member =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp only [evalConstrainBody, true_and]
      have hwval : w (objEnv self, member.val) = wt' w dest := by
        rw [hI]
        simp [wt', encodeWitnessVar, VarIdEncoding.decode_encode]
      rw [localEnv_update_self _ _ _ hwval.symm]
      exact ih _ _ hRest
    | constrainEq src1 src2 =>
      simp only [compileConstrainBody] at hSat
      rw [satisfies_cons] at hSat
      obtain ⟨hI, hRest⟩ := hSat
      simp only [FlatIR.satisfiesInstr] at hI
      simp [evalConstrainBody, hI]
      exact ih _ _ hRest
    | call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      have hj : j.val < i.val := target.isLt
      let calleeBody := (m.structs j).constrain.body
      let ρ' : Nat → Nat := StructIRSubst.freshMap nextFresh
      let freshenResult := StructIRSubst.freshenBody nextFresh calleeBody
      let freshBody := freshenResult.1
      let nextFresh' := freshenResult.2
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with
        | some arg => objEnv arg
        | none => []
      let adjustedObjEnv : ObjEnv := fun v =>
        if h : nextFresh ≤ v then calleeObjEnv (v - nextFresh) else []
      let paramBinds :=
        compileParamBindings (F := F) (m.structs j).constrain.numParams args ρ'
      let compileResult := compileConstrainBody m j adjustedObjEnv nextFresh' freshBody
      let calleeInstrs := compileResult.1
      let nextFresh'' := compileResult.2.2
      let tailResult := compileConstrainBody m i objEnv nextFresh'' rest
      let tailProg := tailResult.1
      simp only [compileConstrainBody] at hSat
      rw [satisfies_append] at hSat
      obtain ⟨hParamCallee, hTail⟩ := hSat
      rw [satisfies_append] at hParamCallee
      obtain ⟨hParam, hCallee⟩ := hParamCallee
      have hCalleeAdj : FlatIR.satisfies (wt' w)
          (compileConstrainBody m j adjustedObjEnv nextFresh' freshBody).1 := by
        simpa [calleeInstrs, compileResult] using hCallee
      have hCalleeEval : evalConstrainBody m w j (wt' w) adjustedObjEnv freshBody :=
        ih_i j hj adjustedObjEnv nextFresh' freshBody hCalleeAdj
      have hTailProg : FlatIR.satisfies (wt' w)
          (compileConstrainBody m i objEnv nextFresh'' rest).1 := by
        simpa [tailProg, tailResult] using hTail
      have hRestEval : evalConstrainBody m w i (wt' w) objEnv rest :=
        ih objEnv nextFresh'' hTailProg
      simp only [evalConstrainBody]
      refine ⟨?_, hRestEval⟩
      have hFreshEq : freshBody = StructIRSubst.renameBody ρ' calleeBody := by
        unfold freshBody freshenResult ρ'
        rfl
      have hCalleeEval' : evalConstrainBody m w j (wt' w) adjustedObjEnv
          (StructIRSubst.renameBody ρ' calleeBody) := by
        simpa [hFreshEq] using hCalleeEval
      have hRename := (evalConstrainBody_rename m w j (wt' w) adjustedObjEnv ρ'
        (StructIRSubst.freshMap_injective nextFresh) calleeBody).mp hCalleeEval'
      have hObjEnvEq : adjustedObjEnv ∘ ρ' = calleeObjEnv := by
        funext param
        simp [adjustedObjEnv, ρ', StructIRSubst.freshMap, Function.comp]
      rw [hObjEnvEq] at hRename
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => wt' w arg | none => 0
      apply (evalConstrainBody_env_agree_on_init m w j ((wt' w) ∘ ρ') calleeEnv calleeObjEnv
        calleeBody (hSSA j) ?_).mp hRename
      intro v hv
      simp only [Function.comp, calleeEnv, ρ']
      have hEq := compileParamBindings_env_agree (m.structs j).constrain.numParams args nextFresh
        (wt' w) hParam v (by simpa using hv)
      simp [StructIRSubst.freshMap] at hEq ⊢
      split <;> simp_all

theorem body_reflection_wt (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams) (m.structs j).constrain.body = true)
    (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSat : FlatIR.satisfies (wt' w)
      (compileConstrainBody m i objEnv nextFresh stmts).1) :
    evalConstrainBody m w i (wt' w) objEnv stmts := by
  revert i objEnv nextFresh stmts hSat
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      FlatIR.satisfies (wt' w) (compileConstrainBody m i objEnv nextFresh stmts).1 →
      evalConstrainBody m w i (wt' w) objEnv stmts)
  · intro k ih_k i hi objEnv nextFresh stmts hSat
    apply body_reflection_wt_aux m w i hSSA
    · intro j hj
      exact ih_k j.val (hi ▸ hj) j rfl
    · exact hSat
  · rfl

/--
Bridge: `checkedSuccess` at the StructIR level implies `satisfies`.
This assumes the StructIRSubst <-> StructIR bridge is complete.
-/
theorem checkedSuccess_implies_satisfies [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module (n + 1) F) :
    StructIRSubst.checkedSuccess w m → StructIR.satisfies w m := by
  intro ⟨trace, h⟩
  exact StructIRSubst.satisfies_of_checkedSuccess w m ⟨trace, h⟩

/--
Top-level reflection: FlatIR satisfies compiled program → StructIR satisfies source.

Strategy: Convert FlatIR.satisfies to FlatIRSubst.checkedSuccess via the bridge,
then use atom-level correspondence to get StructIRSubst.checkedSuccess, and finally
convert back to StructIR.satisfies via the StructIR bridge.
-/
instance CorrectReflectingPass :
    ReflectingPass (StructIRSubst.Language n F) (FlatIRSubst.Language F) where
  toPass := CorrectPass (F := F) (n := n)
  reflection := by
    sorry

end StructIRToFlatIRDirect
