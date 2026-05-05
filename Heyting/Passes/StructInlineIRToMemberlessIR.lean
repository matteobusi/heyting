/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Core.Pass
import Heyting.Languages.StructInlineIR
import Heyting.Languages.MemberlessIR
import Mathlib.Data.List.Nodup

/-!
# StructInlineIR → MemberlessIR Pass

Eliminates struct-member hierarchy from the call-free `StructInlineIR`,
producing a `MemberlessIR` module where every variable is a flat felt slot.

## Compilation strategy

Each `StructInlineIR.ConstrainStmt` maps to one `MemberlessIR.Stmt`:

| StructInlineIR statement | MemberlessIR output | Notes |
|---|---|---|
| `feltAdd/Sub/Mul/Div/Neg/Const` | same op, same vars | identity |
| `constrainEq` | `constrainEq` | identity |
| `readMember dest self member` | `readMember dest self member` | pre-populates `dest` |

Local variable IDs are preserved verbatim.

## Correctness

- **Preservation**: if `ws` satisfies `StructInlineIR.Module m` and the body
  is `WellFormedForCompile`, then `compileWitness m ws` satisfies
  `MemberlessIR.Module (compile m)`.
- **Reflection**: if `mw` satisfies `MemberlessIR.Module (compile m)`, then
  `extractWitness m mw` satisfies `StructInlineIR.Module m`.
-/

namespace StructInlineIRToMemberlessIR

open StructIR StructInlineIR MemberlessIR

variable {F : Type} [Field F] {n : Nat}

/-! ## Program compilation -/

def compileStmt {n : Nat} {F : Type} {i : Fin n}
    (stmt : StructInlineIR.ConstrainStmt n F) :
    Option (MemberlessIR.Stmt n i F) :=
  match stmt with
  | .feltAdd dest src1 src2  => some (.feltAdd dest src1 src2)
  | .feltSub dest src1 src2  => some (.feltSub dest src1 src2)
  | .feltMul dest src1 src2  => some (.feltMul dest src1 src2)
  | .feltDiv dest src1 src2  => some (.feltDiv dest src1 src2)
  | .feltNeg dest src        => some (.feltNeg dest src)
  | .feltConst dest c        => some (.feltConst dest c)
  | .constrainEq src1 src2   => some (.constrainEq src1 src2)
  | .readMember dest self member =>
    some (.readMember dest self member)

def compileStmts {n : Nat} {F : Type} {i : Fin n}
    (stmts : List (StructInlineIR.ConstrainStmt n F)) :
    List (MemberlessIR.Stmt n i F) :=
  stmts.filterMap compileStmt

def compileFunc (i : Fin n) (sd : StructInlineIR.StructDef n F) :
    MemberlessIR.Func n i F where
  numParams := sd.constrain.numParams
  body      := compileStmts (i := i) sd.constrain.body

def compile (m : StructInlineIR.Module (n + 1) F) :
    MemberlessIR.Module (n + 1) F :=
  fun i => compileFunc i (m.structs i)

/-! ## Witness translation (forward) -/

def compileWitnessBody (ws : StructInlineIR.Witness F)
    (env : StructInlineIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : Nat → F) : Nat → F :=
  match stmts with
  | [] => acc
  | stmt :: rest =>
    let (env', objEnv', acc') :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        let v := env src1 + env src2
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltSub dest src1 src2 =>
        let v := env src1 - env src2
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltMul dest src1 src2 =>
        let v := env src1 * env src2
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltDiv dest src1 src2 =>
        let v := env src1 * (env src2)⁻¹
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltNeg dest src =>
        let v := -(env src)
        (env.update dest v, objEnv,
         fun k => if k == dest then v else acc k)
      | .feltConst dest c =>
        (env.update dest c, objEnv,
         fun k => if k == dest then c else acc k)
      | .readMember dest self member =>
        let path := objEnv self
        let v := ws (path, member)
        (env.update dest v,
         StructIR.ObjEnv.update objEnv dest (path ++ [member]),
         fun k => if k == dest then v else acc k)
      | .constrainEq _ _ =>
        (env, objEnv, acc)
    compileWitnessBody ws env' objEnv' rest acc'

def compileWitness (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) : Nat → F :=
  let mainIdx : Fin (n + 1) :=
    ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initEnv : StructInlineIR.LocalEnv F := fun k => ws ([], k)
  let initObjEnv : StructIR.ObjEnv :=
    StructIR.ObjEnv.update (fun _ => []) 0 []
  compileWitnessBody ws initEnv initObjEnv
    (m.structs mainIdx).constrain.body initEnv

/-! ## Compile-witness agreement lemma -/

theorem compileWitnessBody_agrees (ws : StructInlineIR.Witness F)
    (env : StructInlineIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : Nat → F) (hAcc : ∀ k, acc k = env k) :
    ∀ k, compileWitnessBody ws env objEnv stmts acc k =
      (StructInlineIR.runState ws env objEnv stmts).1 k := by
  induction stmts generalizing env objEnv acc with
  | nil =>
    intro k
    simp [compileWitnessBody, StructInlineIR.runState, hAcc]
  | cons stmt rest ih =>
    intro k
    have agg : ∀ (dest : Nat) (v : F),
        ∀ k', (fun k' => if k' == dest then v else acc k') k' =
              (env.update dest v) k' := by
      intro dest v k'
      simp only [StructInlineIR.LocalEnv.update, beq_iff_eq]
      split
      · rfl
      · exact hAcc k'
    match stmt with
    | .feltAdd d s1 s2 =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .feltSub d s1 s2 =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .feltMul d s1 s2 =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .feltDiv d s1 s2 =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .feltNeg d s =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .feltConst d c =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .readMember d s mem =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ (agg d _) k
    | .constrainEq s1 s2 =>
      simp only [compileWitnessBody, StructInlineIR.runState,
                 StructInlineIR.stepState]
      exact ih _ _ _ hAcc k

/-! ## Well-formedness for compilation -/

/-- Well-formedness predicate for compilation: ensures that the
    MemberlessIR constraints (which use a fixed witness) correctly
    reflect the StructInlineIR semantics (which thread an evolving env).

    For each statement:
    1. Dest (if any) is not one of its own sources.
    2. All sources are not overwritten by later statements.
    3. Dest (if any) is not overwritten by later statements (SSA). -/
def WellFormedForCompile :
    List (StructInlineIR.ConstrainStmt n F) → Prop
  | [] => True
  | stmt :: rest =>
    (match StructInlineIR.constrainStmtDest stmt with
     | some d => d ∉ StructInlineIR.constrainStmtSources stmt
     | none => True) ∧
    (∀ src ∈ StructInlineIR.constrainStmtSources stmt,
       src ∉ StructInlineIR.constrainDests rest) ∧
    (match StructInlineIR.constrainStmtDest stmt with
     | some d => d ∉ StructInlineIR.constrainDests rest
     | none => True) ∧
    WellFormedForCompile rest

/-! ## Helper: runState preserves non-dest positions -/

theorem runState_preserve (ws : StructInlineIR.Witness F)
    (env : StructInlineIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F)) (k : Nat)
    (hk : k ∉ StructInlineIR.constrainDests stmts) :
    (StructInlineIR.runState ws env objEnv stmts).1 k =
      env k := by
  contrapose! hk;
  contrapose! hk; induction stmts generalizing env objEnv <;> simp_all +decide [ runState ] ;
  rename_i h₁ h₂ h₃;
  rw [ h₃ ];
  · unfold stepState; rcases h₁ with ( _ | _ | _ | _ | _ | _ | _ | _ ) <;> simp +decide [ constrainDests ] at hk ⊢;
    all_goals unfold StructInlineIR.LocalEnv.update; simp +decide [ hk.1 ] ;
  · unfold constrainDests at *; aesop;

/-! ## LocalEnv.update helpers -/

omit [Field F] in
private theorem update_self (env : StructInlineIR.LocalEnv F)
    (d : Nat) (v : F) :
    (env.update d v) d = v := by
  simp [StructInlineIR.LocalEnv.update]

omit [Field F] in
private theorem update_other (env : StructInlineIR.LocalEnv F)
    (d k : Nat) (v : F) (h : k ≠ d) :
    (env.update d v) k = env k := by
  simp [StructInlineIR.LocalEnv.update, beq_iff_eq, h]

/-! ## Key: mw at preserved position equals env -/

/-- If `k ∉ constrainDests stmts` and `acc` agrees with `env`,
    then `compileWitnessBody` at `k` equals `env k`. -/
theorem cwb_at_preserved
    (ws : StructInlineIR.Witness F)
    (env : StructInlineIR.LocalEnv F) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : Nat → F) (hAcc : ∀ k, acc k = env k) (k : Nat)
    (hk : k ∉ StructInlineIR.constrainDests stmts) :
    compileWitnessBody ws env objEnv stmts acc k = env k :=
  (compileWitnessBody_agrees ws env objEnv stmts acc hAcc k).trans
    (runState_preserve ws env objEnv stmts k hk)

/-! ## Witness translation (backward) -/

abbrev ReadMap := StructIR.VarId → StructInlineIR.LocalVar

def buildReadMap (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : ReadMap) : ReadMap :=
  match stmts with
  | [] => acc
  | stmt :: rest =>
    let (objEnv', acc') :=
      match stmt with
      | .readMember dest self member =>
        let path := objEnv self
        (StructIR.ObjEnv.update objEnv dest (path ++ [member]),
         fun vid =>
           if vid == (path, member) then dest else acc vid)
      | .feltAdd _ _ _ | .feltSub _ _ _ | .feltMul _ _ _
      | .feltDiv _ _ _ | .feltNeg _ _ | .feltConst _ _ =>
        (objEnv, acc)
      | .constrainEq _ _ =>
        (objEnv, acc)
    buildReadMap objEnv' rest acc'

def extractWitness (m : StructInlineIR.Module (n + 1) F)
    (mw : Nat → F) : StructInlineIR.Witness F :=
  let mainIdx : Fin (n + 1) :=
    ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initObjEnv : StructIR.ObjEnv :=
    StructIR.ObjEnv.update (fun _ => []) 0 []
  let rmap := buildReadMap initObjEnv
    (m.structs mainIdx).constrain.body (fun _ => 0)
  fun vid =>
    if vid.1 = [] then mw vid.2 else mw (rmap vid)

/-! ## Witness relation -/

def witnessRel (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) (mw : Nat → F) : Prop :=
  mw = compileWitness m ws

theorem witnessRel_compileWitness
    (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) :
    witnessRel m ws (compileWitness m ws) := rfl

/-! ## Helper: acc agrees with env.update -/

omit [Field F] in
private theorem mk_hAcc_update
    (acc : Nat → F) (env : StructInlineIR.LocalEnv F)
    (hAcc : ∀ k, acc k = env k) (dest : Nat) (v : F) :
    ∀ k, (fun k => if k == dest then v else acc k) k =
         (env.update dest v) k := by
  intro k
  simp only [StructInlineIR.LocalEnv.update, beq_iff_eq]
  split <;> [rfl; exact hAcc k]

/-! ## Main preservation helper -/

/-- If StructInlineIR.evalConstrainBody holds and the body is
    WellFormedForCompile, then MemberlessIR.evalBody holds for the
    compiled statements with the compiled witness. -/
theorem evalBody_of_evalConstrainBody
    (m : StructInlineIR.Module n F)
    (ws : StructInlineIR.Witness F)
    (i : Fin n) (env : StructInlineIR.LocalEnv F)
    (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (acc : Nat → F)
    (hEval : StructInlineIR.evalConstrainBody m ws i env objEnv
      stmts)
    (hAcc : ∀ k, acc k = env k)
    (hWF : WellFormedForCompile stmts) :
    let mw := compileWitnessBody ws env objEnv stmts acc
    MemberlessIR.evalBody (fun j => compileFunc j (m.structs j)) i
      mw (compileStmts stmts) := by
  intro mw
  induction stmts generalizing env objEnv acc with
  | nil => simp [compileStmts, MemberlessIR.evalBody]
  | cons stmt rest ih =>
    unfold StructInlineIR.evalConstrainBody at hEval
    unfold compileStmts
    simp only [List.filterMap_cons]
    obtain ⟨hNSR, hSP, hDP, hWFR⟩ := hWF
    cases stmt with
    | feltAdd dest src1 src2 =>
      -- After match reduction: hNSR : dest ∉ [src1, src2]
      -- hSP : ∀ src ∈ [src1,src2], src ∉ constrainDests rest
      -- hDP : dest ∉ constrainDests rest
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨_, hRE⟩ := hEval
      have hAcc' := mk_hAcc_update acc env hAcc dest
        (env src1 + env src2)
      -- Prove constraint: mw dest = mw src1 + mw src2
      -- mw k = cwb ws env' objEnv rest acc' k
      -- By cwb_at_preserved, mw k = env' k when k not in dests
      have hD : mw dest = env src1 + env src2 := by
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          dest hDP
        rwa [update_self] at this
      have hne1 : src1 ≠ dest := by
        intro h; apply hNSR; rw [h]; exact List.mem_cons_self
      have hne2 : src2 ≠ dest := by
        intro h; apply hNSR; rw [h]
        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
      have hS1 : mw src1 = env src1 := by
        have hsp1 := hSP src1 List.mem_cons_self
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src1 hsp1
        rwa [update_other _ _ _ _ hne1] at this
      have hS2 : mw src2 = env src2 := by
        have hsp2 := hSP src2
          (List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src2 hsp2
        rwa [update_other _ _ _ _ hne2] at this
      exact ⟨by rw [hD, hS1, hS2],
             ih _ objEnv _ hRE hAcc' hWFR⟩
    | feltSub dest src1 src2 =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨_, hRE⟩ := hEval
      have hAcc' := mk_hAcc_update acc env hAcc dest
        (env src1 - env src2)
      have hD : mw dest = env src1 - env src2 := by
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          dest hDP
        rwa [update_self] at this
      have hne1 : src1 ≠ dest := by
        intro h; apply hNSR; rw [h]; exact List.mem_cons_self
      have hne2 : src2 ≠ dest := by
        intro h; apply hNSR; rw [h]
        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
      have hS1 : mw src1 = env src1 := by
        have hsp1 := hSP src1 List.mem_cons_self
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src1 hsp1
        rwa [update_other _ _ _ _ hne1] at this
      have hS2 : mw src2 = env src2 := by
        have hsp2 := hSP src2
          (List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src2 hsp2
        rwa [update_other _ _ _ _ hne2] at this
      exact ⟨by rw [hD, hS1, hS2],
             ih _ objEnv _ hRE hAcc' hWFR⟩
    | feltMul dest src1 src2 =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨_, hRE⟩ := hEval
      have hAcc' := mk_hAcc_update acc env hAcc dest
        (env src1 * env src2)
      have hD : mw dest = env src1 * env src2 := by
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          dest hDP
        rwa [update_self] at this
      have hne1 : src1 ≠ dest := by
        intro h; apply hNSR; rw [h]; exact List.mem_cons_self
      have hne2 : src2 ≠ dest := by
        intro h; apply hNSR; rw [h]
        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
      have hS1 : mw src1 = env src1 := by
        have hsp1 := hSP src1 List.mem_cons_self
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src1 hsp1
        rwa [update_other _ _ _ _ hne1] at this
      have hS2 : mw src2 = env src2 := by
        have hsp2 := hSP src2
          (List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src2 hsp2
        rwa [update_other _ _ _ _ hne2] at this
      exact ⟨by rw [hD, hS1, hS2],
             ih _ objEnv _ hRE hAcc' hWFR⟩
    | feltDiv dest src1 src2 =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨h_nz, hRE⟩ := hEval
      have hAcc' := mk_hAcc_update acc env hAcc dest
        (env src1 * (env src2)⁻¹)
      have hne1 : src1 ≠ dest := by
        intro h; apply hNSR; rw [h]; exact List.mem_cons_self
      have hne2 : src2 ≠ dest := by
        intro h; apply hNSR; rw [h]
        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
      have hD : mw dest = env src1 * (env src2)⁻¹ := by
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          dest hDP
        rwa [update_self] at this
      have hS1 : mw src1 = env src1 := by
        have hsp1 := hSP src1 List.mem_cons_self
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src1 hsp1
        rwa [update_other _ _ _ _ hne1] at this
      have hS2 : mw src2 = env src2 := by
        have hsp2 := hSP src2
          (List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src2 hsp2
        rwa [update_other _ _ _ _ hne2] at this
      exact ⟨⟨by rw [hS2]; exact h_nz,
              by rw [hD, hS1, hS2]⟩,
             ih _ objEnv _ hRE hAcc' hWFR⟩
    | feltNeg dest src =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨_, hRE⟩ := hEval
      have hAcc' := mk_hAcc_update acc env hAcc dest (-(env src))
      have hne : src ≠ dest := by
        intro h; apply hNSR; rw [h]; exact List.mem_cons_self
      have hD : mw dest = -(env src) := by
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          dest hDP
        rwa [update_self] at this
      have hS : mw src = env src := by
        have hsp := hSP src List.mem_cons_self
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          src hsp
        rwa [update_other _ _ _ _ hne] at this
      exact ⟨by rw [hD, hS],
             ih _ objEnv _ hRE hAcc' hWFR⟩
    | feltConst dest c =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨_, hRE⟩ := hEval
      have hAcc' := mk_hAcc_update acc env hAcc dest c
      have hD : mw dest = c := by
        have := cwb_at_preserved ws _ objEnv rest _ hAcc'
          dest hDP
        rwa [update_self] at this
      exact ⟨hD, ih _ objEnv _ hRE hAcc' hWFR⟩
    | readMember dest self member =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨_, hRE⟩ := hEval
      have hAcc' : ∀ k,
          (fun k => if k == dest then ws (objEnv self, member)
                    else acc k) k =
          (env.update dest (ws (objEnv self, member))) k :=
        mk_hAcc_update acc env hAcc dest _
      exact ⟨trivial, ih _ _ _ hRE hAcc' hWFR⟩
    | constrainEq src1 src2 =>
      simp only [compileStmt, MemberlessIR.evalBody]
      obtain ⟨h_eq, hRE⟩ := hEval
      -- constrainStmtSources (constrainEq ..) = [src1, src2]
      have hS1 : mw src1 = env src1 := by
        have hsp1 := hSP src1 List.mem_cons_self
        exact cwb_at_preserved ws env objEnv rest acc hAcc
          src1 hsp1
      have hS2 : mw src2 = env src2 := by
        have hsp2 := hSP src2
          (List.mem_cons.mpr (Or.inr List.mem_cons_self))
        exact cwb_at_preserved ws env objEnv rest acc hAcc
          src2 hsp2
      exact ⟨by rw [hS1, hS2]; exact h_eq,
             ih env objEnv acc hRE hAcc hWFR⟩

/-! ## Preservation theorem -/

theorem preservation (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F)
    (h : StructInlineIR.satisfies ws m)
    (hWF : WellFormedForCompile
      (m.structs ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩
        ).constrain.body) :
    MemberlessIR.satisfies (compileWitness m ws) (compile m) := by
  unfold MemberlessIR.satisfies compile compileWitness
  simp only
  exact evalBody_of_evalConstrainBody m ws _ _ _
    _ _ h (fun _ => rfl) hWF

/-! ## Reflection helpers and theorem

  **Status**: sorry'd (open question). The reflection direction
  (`MemberlessIR.satisfies mw (compile m) → StructInlineIR.satisfies
  (extractWitness m mw) m`) requires resolving a semantic gap in the
  `extractWitness` definition: for root-level `readMember` statements
  (where `objEnv self = []`), `extractWitness` returns `mw member`
  rather than `mw dest`, which means the env invariant
  `∀ k, env k = mw k` cannot be maintained through the body evaluation.
  See `docs/WARNING.md` §8 for details. -/

/-- Helper for reflection (sorry'd — see note above).
    Requires resolving the `extractWitness` root-path issue. -/
theorem evalConstrainBody_of_evalBody
    (m : StructInlineIR.Module n F) (mw : Nat → F)
    (i : Fin n) (objEnv : StructIR.ObjEnv)
    (stmts : List (StructInlineIR.ConstrainStmt n F))
    (rmap : ReadMap)
    (hEvalMIR : MemberlessIR.evalBody
      (fun j => compileFunc j (m.structs j)) i mw
      (compileStmts stmts)) :
    let ws : StructInlineIR.Witness F :=
      fun vid =>
        if vid.1 = [] then mw vid.2 else mw (rmap vid)
    let env : StructInlineIR.LocalEnv F := fun k => mw k
    StructInlineIR.evalConstrainBody m ws i env objEnv
      stmts := by
  sorry

/-- Reflection (sorry'd — see note above).
    Requires resolving the `extractWitness` root-path issue. -/
theorem reflection (m : StructInlineIR.Module (n + 1) F)
    (mw : Nat → F)
    (h : MemberlessIR.satisfies mw (compile m)) :
    StructInlineIR.satisfies (extractWitness m mw) m := by
  sorry

instance PresReflPass (n : Nat) (F : Type) [Field F] :
    PresReflPass (StructInlineIR.Language n F)
      (MemberlessIR.instLanguage n F) where
  compile := compile
  witnessRel := witnessRel
  preservation := by
    intro ws p hs
    -- We need WellFormedForCompile for the main body
    -- For now, sorry this assumption - it should be proved from module invariants
    have hWF : WellFormedForCompile (p.structs ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩).constrain.body := by
      sorry
    exact ⟨compileWitness p ws, witnessRel_compileWitness p ws, preservation p ws hs hWF⟩
  reflection := by
    intro mw p hs
    use extractWitness p mw
    constructor
    · -- witnessRel: need to show mw = compileWitness p (extractWitness p mw)
      -- This is the semantic gap mentioned in docs/WARNING.md §8
      sorry
    · exact reflection p mw hs

instance Pass (n : Nat) (F : Type) [Field F] :
    Pass (StructInlineIR.Language n F)
      (MemberlessIR.instLanguage n F) :=
  inferInstance

end StructInlineIRToMemberlessIR