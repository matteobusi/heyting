import Heyting.Core.VarIdEncoding
import Heyting.Core.Pass
import Heyting.Languages.FlatIR
import Heyting.Languages.StructIRFreshen
import Heyting.Languages.StructIR

/-!
# StructIR -> FlatIR

Compiler from StructIR constrain bodies to FlatIR instruction lists, together
with reflection proof for executable lowering.

Design points:
- lowers arithmetic and equality directly,
- lowers `readMember` using concrete `(path, member)` encoding,
- inlines calls recursively,
- uses deterministic freshening strategy from `StructIRFreshen`.
-/
namespace StructIRToFlatIR

open StructIR

variable {F : Type} [Field F] {n : Nat}

/-- Encode a concrete witness coordinate `(path, member)` as a FlatIR variable id. -/
def encodeWitnessVar (path : StructIR.InstancePath) (member : Nat) : FlatIR.VarId :=
  VarIdEncoding.encode (path, member)

/-- Compile call parameter bindings after freshening (`ρ idx = nextFresh + idx`). -/
def compileParamBindings (numParams : Nat) (args : List Nat) (ρ : Nat → Nat) :
    List (FlatIR.Instr F) :=
  let rec go (idx remaining : Nat) : List (FlatIR.Instr F) :=
    match remaining with
    | 0 => []
    | k + 1 =>
      let head :=
        match args[idx]? with
        | some arg => [FlatIR.Instr.assertEq (ρ idx) arg]
        | none => [FlatIR.Instr.assignConst (ρ idx) (0 : F)]
      head ++ go (idx + 1) k
  go 0 numParams

/--
Compile a StructIR constrain body to FlatIR, threading object environment and
freshness state.
-/
def compileConstrainBody (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    List (FlatIR.Instr F) × StructIR.ObjEnv × Nat :=
  match stmts with
  | [] => ([], objEnv, nextFresh)
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltSub dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignSub dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltMul dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignMul dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltDiv dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignDiv dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltNeg dest src =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignNeg dest src :: tail, objEnv', nextFresh')
    | .feltConst dest c =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignConst dest c :: tail, objEnv', nextFresh')
    | .readMember dest self member =>
      let path := objEnv self
      let witnessVar := encodeWitnessVar path member.val
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnvStep nextFresh rest
      (FlatIR.Instr.assertEq dest witnessVar :: tail, objEnv', nextFresh')
    | .constrainEq src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assertEq src1 src2 :: tail, objEnv', nextFresh')
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let ρ : Nat → Nat := StructIRFreshen.freshMap nextFresh
      let (freshBody, nextFresh') := StructIRFreshen.freshenBody nextFresh calleeBody
      let paramBinds := compileParamBindings (F := F) (m.structs j).constrain.numParams args ρ
      let calleeObjEnv : StructIR.ObjEnv := fun param =>
        match args[param]? with
        | some arg => objEnv arg
        | none => []
      -- Adjust objEnv for ρ-renaming: ρ(k) = nextFresh + k should map to
      -- calleeObjEnv(k) (the path of the k-th arg).  For k ≥ nextFresh + numParams
      -- (non-param freshened vars) the result is [] which is overwritten by
      -- subsequent readMember updates inside the callee.
      let adjustedObjEnv : StructIR.ObjEnv := fun v =>
        if nextFresh ≤ v then
          calleeObjEnv (v - nextFresh)
        else
          []
      let (calleeInstrs, _, nextFresh'') :=
        compileConstrainBody m j adjustedObjEnv nextFresh' freshBody
      let (tail, objEnvTail, nextFreshTail) :=
        compileConstrainBody m i objEnv nextFresh'' rest
      (paramBinds ++ calleeInstrs ++ tail, objEnvTail, nextFreshTail)
  termination_by (i, stmts.length)
  decreasing_by
    all_goals
      first
      | apply Prod.Lex.left
        exact target.isLt
      | apply Prod.Lex.right
        simp

theorem compileConstrainBody_feltAdd_eq
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody m i objEnv nextFresh (.feltAdd dest src1 src2 :: rest) =
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

theorem compileConstrainBody_constrainEq_eq
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody m i objEnv nextFresh (.constrainEq src1 src2 :: rest) =
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assertEq src1 src2 :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

theorem compileConstrainBody_readMember_eq
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody m i objEnv nextFresh (.readMember dest self member :: rest) =
      let path := objEnv self
      let witnessVar := encodeWitnessVar path member.val
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnvStep nextFresh rest
      (FlatIR.Instr.assertEq dest witnessVar :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

/-- Compile a full StructIR module directly to a FlatIR program. -/
def compileProgram (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initObjEnv : StructIR.ObjEnv := StructIR.ObjEnv.update (fun _ => []) 0 []
  let initNextFresh := StructIRFreshen.maxVarBody (m.structs mainIdx).constrain.body + 1
  let (instrs, _, _) :=
    compileConstrainBody m mainIdx initObjEnv initNextFresh (m.structs mainIdx).constrain.body
  instrs

instance CorrectPass (F : Type) [Field F] (n : Nat) :
    Pass (StructIR.Language n F) (FlatIR.Language F) where
  compile := compileProgram (F := F)
  witnessRel _ ws wt :=
    -- Uniform bijection: FlatIR var v corresponds to StructIR position decode v.
    -- This aligns with the decode-seeded satisfies semantics.
    ∀ v, wt v = ws (VarIdEncoding.decode v)

/-- The natural FlatIR witness derived from a StructIR witness via `decode`. -/
def wt' (w : StructIR.Witness F) : FlatIR.Witness F :=
  fun v => w (VarIdEncoding.decode v)

/-- FlatIR.satisfies decomposes on cons. -/
lemma satisfies_cons (w : FlatIR.Witness F) (i : FlatIR.Instr F) (p : FlatIR.Program F) :
    FlatIR.satisfies w (i :: p) ↔ FlatIR.satisfiesInstr w i ∧ FlatIR.satisfies w p := by
  constructor
  · intro h
    refine ⟨h i (by simp), ?_⟩
    intro j hj
    exact h j (by simp [hj])
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
    · intro j hj
      exact h j (by simp [hj])
    · intro j hj
      exact h j (by simp [hj])
  · intro ⟨h1, h2⟩ j hj
    rcases List.mem_append.mp hj with hj1 | hj2
    · exact h1 j hj1
    · exact h2 j hj2

omit [Field F] in
/-- LocalEnv.update is identity when value matches existing entry. -/
lemma localEnv_update_self (env : LocalEnv F) (x : Nat) (v : F) (h : env x = v) :
    env.update x v = env := by
  funext k
  simp only [LocalEnv.update]
  by_cases hk : k = x
  · subst hk
    simp only [beq_self_eq_true, if_true, h]
  · have : (k == x) = false := by simp [hk]
    rw [this]
    simp

/-- If two local envs agree on parameters, SSA evaluation agrees. -/
lemma evalConstrainBody_env_agree_on_init (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (env1 env2 : LocalEnv F) (objEnv : ObjEnv)
    (body : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA (fun v => v < (m.structs i).constrain.numParams) body = true)
    (hAgree : ∀ v, (fun v => v < (m.structs i).constrain.numParams) v = true → env1 v = env2 v) :
    evalConstrainBody m w i env1 objEnv body ↔ evalConstrainBody m w i env2 objEnv body :=
  StructIRFreshen.evalConstrainBody_env_agree_on_init m w i env1 env2 objEnv body hSSA hAgree

/-- Extract per-param equality from `compileParamBindings` satisfaction (inner loop). -/
private lemma compileParamBindings_go_env_agree (args : List Nat) (nextFresh : Nat)
    (wt : FlatIR.Witness F) (idx remaining : Nat)
    (hParam : FlatIR.satisfies wt
      (compileParamBindings.go (F := F) args (StructIRFreshen.freshMap nextFresh) idx remaining))
    (param : Nat) (hlt : param < remaining) :
    wt (StructIRFreshen.freshMap nextFresh (idx + param)) =
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
        simp [hI]
      · rename_i h
        simp only [satisfies_cons] at hHead
        obtain ⟨hI, _⟩ := hHead
        simp only [FlatIR.satisfiesInstr] at hI
        simp [hI]
    | succ p =>
      have hlt' : p < k := Nat.lt_of_succ_lt_succ hlt
      have := ih (idx + 1) hRest p hlt'
      simp only [Nat.add_assoc, Nat.add_comm 1 p] at this ⊢
      exact this

/-- From `compileParamBindings` satisfaction, extract per-param equality. -/
private lemma compileParamBindings_env_agree (numParams : Nat) (args : List Nat) (nextFresh : Nat)
    (wt : FlatIR.Witness F)
    (hParam : FlatIR.satisfies wt
      (compileParamBindings numParams args (StructIRFreshen.freshMap nextFresh)))
    (param : Nat) (hlt : param < numParams) :
    wt (StructIRFreshen.freshMap nextFresh param) =
    match args[param]? with | some arg => wt arg | none => 0 := by
  unfold compileParamBindings at hParam
  have := compileParamBindings_go_env_agree args nextFresh wt 0 numParams hParam param hlt
  simpa using this

/-- Helper: body reflection for fixed `i`, given IH for all `j < i`. -/
private theorem body_reflection_wt_aux (m : Module n F) (w : StructIR.Witness F)
    (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
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
      simp only [evalConstrainBody, hI, true_and]
      exact ih _ _ hRest
    | call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      have hj : j.val < i.val := target.isLt
      let calleeBody := (m.structs j).constrain.body
      let ρ' : Nat → Nat := StructIRFreshen.freshMap nextFresh
      let freshenResult := StructIRFreshen.freshenBody nextFresh calleeBody
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
      have hFreshEq : freshBody = StructIRFreshen.renameBody ρ' calleeBody := by
        unfold freshBody freshenResult ρ'
        rfl
      have hCalleeEval' : evalConstrainBody m w j (wt' w) adjustedObjEnv
          (StructIRFreshen.renameBody ρ' calleeBody) := by
        simpa [hFreshEq] using hCalleeEval
      have hRename := (StructIRFreshen.evalConstrainBody_rename m w j (wt' w) adjustedObjEnv ρ'
        (StructIRFreshen.freshMap_injective nextFresh) calleeBody).mp hCalleeEval'
      have hObjEnvEq : adjustedObjEnv ∘ ρ' = calleeObjEnv := by
        funext param
        simp [adjustedObjEnv, ρ', StructIRFreshen.freshMap, Function.comp]
      rw [hObjEnvEq] at hRename
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => wt' w arg | none => 0
      apply (evalConstrainBody_env_agree_on_init m w j ((wt' w) ∘ ρ') calleeEnv calleeObjEnv
        calleeBody (hSSA j) ?_).mp hRename
      intro v hv
      simp only [Function.comp, calleeEnv, ρ']
      have hEq := compileParamBindings_env_agree (m.structs j).constrain.numParams args nextFresh
        (wt' w) hParam v (by simpa using hv)
      simp [StructIRFreshen.freshMap] at hEq ⊢
      split <;> simp_all

theorem body_reflection_wt (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
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

/-- Top-level reflection: FlatIR satisfies compiled program → StructIR satisfies source. -/
instance CorrectReflectingPass :
    ReflectingPass (StructIR.Language n F) (FlatIR.Language F) where
  toPass := CorrectPass (F := F) (n := n)
  reflection := by
    intro wt m hSat
    refine ⟨fun pos => wt (VarIdEncoding.encode pos), ?_, ?_⟩
    · intro v
      simp [VarIdEncoding.encode_decode]
    · set ws : StructIR.Witness F := fun pos => wt (VarIdEncoding.encode pos) with hws_def
      have hwt_eq : wt' ws = wt := by
        funext v
        simp [wt', ws, VarIdEncoding.encode_decode]
      change StructIR.satisfies (n := n) ws m
      unfold StructIR.satisfies
      simp only
      have henv_eq : (fun k : Nat =>
            let p := Nat.unpair k
            ws (Equiv.listNatEquivNat.symm p.1, p.2)) = wt' ws := by
        funext k
        rfl
      rw [henv_eq, hwt_eq]
      have hSat' : FlatIR.satisfies wt
          (compileConstrainBody m
            ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
            (StructIR.ObjEnv.update (fun _ => []) 0 [])
            (StructIRFreshen.maxVarBody (m.structs
              ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).constrain.body + 1)
            (m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).constrain.body).1 := by
        change FlatIR.satisfies wt (compileProgram m)
        exact hSat
      have hres := body_reflection_wt (F := F) (n := n + 1) m ws
        ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
        m.all_ssa
        (StructIR.ObjEnv.update (fun _ => []) 0 [])
        (StructIRFreshen.maxVarBody (m.structs
          ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).constrain.body + 1)
        (m.structs ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩).constrain.body
        (by rw [hwt_eq]; exact hSat')
      rw [hwt_eq] at hres
      exact hres

end StructIRToFlatIR
