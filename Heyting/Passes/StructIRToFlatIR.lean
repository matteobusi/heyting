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

/-- Encode a StructIR witness position into the shifted FlatIR witness-slot range. -/
def encodeWitnessPos (witnessBase : Nat) (pos : StructIR.VarId) : FlatIR.VarId :=
  witnessBase + VarIdEncoding.encode pos

/-- Encode concrete witness coordinate `(path, member)` as shifted FlatIR slot. -/
def encodeWitnessVar (witnessBase : Nat) (path : StructIR.InstancePath)
    (member : Nat) : FlatIR.VarId :=
  encodeWitnessPos witnessBase (path, member)

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
def compileConstrainBody (witnessBase : Nat) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    List (FlatIR.Instr F) × StructIR.ObjEnv × Nat :=
  match stmts with
  | [] => ([], objEnv, nextFresh)
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltSub dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignSub dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltMul dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignMul dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltDiv dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignDiv dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltNeg dest src =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignNeg dest src :: tail, objEnv', nextFresh')
    | .feltConst dest c =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignConst dest c :: tail, objEnv', nextFresh')
    | .readMember dest self member =>
      let path := objEnv self
      let witnessVar := encodeWitnessVar witnessBase path member.val
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      let (tail, objEnv', nextFresh') :=
        compileConstrainBody witnessBase m i objEnvStep nextFresh rest
      (FlatIR.Instr.assertEq dest witnessVar :: tail, objEnv', nextFresh')
    | .constrainEq src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
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
      let reservedNextFresh := max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
      let (calleeInstrs, _, nextFresh'') :=
        compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody
      let (tail, objEnvTail, nextFreshTail) :=
        compileConstrainBody witnessBase m i objEnv nextFresh'' rest
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
    (witnessBase : Nat)
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody witnessBase m i objEnv nextFresh (.feltAdd dest src1 src2 :: rest) =
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

theorem compileConstrainBody_constrainEq_eq
    (witnessBase : Nat)
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody witnessBase m i objEnv nextFresh (.constrainEq src1 src2 :: rest) =
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assertEq src1 src2 :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

theorem compileConstrainBody_readMember_eq
    (witnessBase : Nat)
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody witnessBase m i objEnv nextFresh (.readMember dest self member :: rest) =
      let path := objEnv self
      let witnessVar := encodeWitnessVar witnessBase path member.val
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      let (tail, objEnv', nextFresh') :=
        compileConstrainBody witnessBase m i objEnvStep nextFresh rest
      (FlatIR.Instr.assertEq dest witnessVar :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

/-- Final freshness counter reached by fully inlining a constrain body. -/
def localCeilConstrainBody (m : StructIR.Module n F)
    (i : Fin n) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) : Nat :=
  match stmts with
  | [] => nextFresh
  | stmt :: rest =>
    match stmt with
    | .call target _ =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let (freshBody, nextFresh') := StructIRFreshen.freshenBody nextFresh calleeBody
      let reservedNextFresh := max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
      let nextFresh'' := localCeilConstrainBody m j reservedNextFresh freshBody
      localCeilConstrainBody m i nextFresh'' rest
    | _ =>
      localCeilConstrainBody m i nextFresh rest
termination_by (i, stmts.length)
decreasing_by
  all_goals
    first
      | apply Prod.Lex.left
        exact target.isLt
      | apply Prod.Lex.right
        simp

lemma localCeilConstrainBody_noncall_cons {i : Fin n}
    (m : StructIR.Module n F) (nextFresh : Nat)
    (stmt : StructIR.ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (hNoCall : ∀ target args, stmt ≠ .call target args) :
    localCeilConstrainBody m i nextFresh (stmt :: rest) =
      localCeilConstrainBody m i nextFresh rest := by
  cases stmt <;> simp [localCeilConstrainBody]
  · exfalso; exact hNoCall _ _ rfl

lemma localCeilConstrainBody_noncall_tail_le {i : Fin n}
    (m : StructIR.Module n F) (nextFresh witnessBase : Nat)
    (stmt : StructIR.ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (hNoCall : ∀ target args, stmt ≠ .call target args)
    (hCeil : localCeilConstrainBody m i nextFresh (stmt :: rest) ≤ witnessBase) :
    localCeilConstrainBody m i nextFresh rest ≤ witnessBase := by
  rw [localCeilConstrainBody_noncall_cons m nextFresh stmt rest hNoCall] at hCeil
  exact hCeil

/-- Module-wide upper bound on local-variable identifiers across all structs.
    Used to reserve `[0, witBase)` for FlatIR locals so that encoded witness
    coordinates (`VarIdEncoding.encode (path, member)`) live above all locals
    and never collide with any source-level register, including freshened ones
    introduced by call inlining. -/
def localBoundOfModule (m : StructIR.Module (n + 1) F) : Nat :=
  Nat.succ <|
    (List.finRange (n + 1)).foldl
      (fun acc i => max acc (StructIRFreshen.maxVarBody (m.structs i).constrain.body)) 0

/-- Witness-slot base for compiled program `m`: all locals are below it, all
    witness coordinates are shifted above it. -/
def witnessBase (m : StructIR.Module (n + 1) F) : Nat :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let numParams := (m.structs mainIdx).constrain.numParams
  let localBase := localBoundOfModule m
  let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
  let renamedBody := StructIRFreshen.renameBody ρ mainBody
  let initNextFresh :=
    max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
  localCeilConstrainBody m mainIdx initNextFresh renamedBody

/-- Encode the canonical param-witness coordinate `paramCoord numMembers p` as
    a FlatIR variable id in the shifted witness-slot range. -/
def encodeParamVar (witnessBase numMembers p : Nat) : FlatIR.VarId :=
  encodeWitnessPos witnessBase (StructIR.paramCoord numMembers p)

/-- Bind each main param `p < numParams` (after renaming to `ρ p`) to its
    canonical param-witness coordinate `encodeParamVar numMembers p`.

    Emitted as a list of `assertEq (ρ p) (encode (paramCoord numMembers p))`
    instructions, one per param. -/
def compileMainParamBindings (witnessBase numMembers numParams : Nat) (ρ : Nat → Nat) :
    List (FlatIR.Instr F) :=
  let rec go (idx remaining : Nat) : List (FlatIR.Instr F) :=
    match remaining with
    | 0 => []
    | k + 1 =>
      FlatIR.Instr.assertEq (ρ idx) (encodeParamVar witnessBase numMembers idx) :: go (idx + 1) k
  go 0 numParams

/-- Compile a full StructIR module directly to a FlatIR program.

    All local variables are allocated below `witnessBase m`. Every witness
    coordinate is shifted to `witnessBase m + encode (path, member)`, so local
    registers and witness slots are formally disjoint.

    The program is prefixed by `compileMainParamBindings`, which asserts that
    each renamed main param `ρ p` equals the canonical witness coord
    `encode ([], p)`. -/
def compileProgram (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let numParams := (m.structs mainIdx).constrain.numParams
  let localBase := localBoundOfModule m
  let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
  let renamedBody := StructIRFreshen.renameBody ρ mainBody
  -- Renaming shifts `%self` (local 0) to `ρ 0 = witBase`. Initialize the
  -- object environment so that the renamed `%self` still represents the root
  -- (empty) path. All other locals start at `[]` by default.
  let initObjEnv : StructIR.ObjEnv := StructIR.ObjEnv.update (fun _ => []) (ρ 0) []
  -- Fresh-name supply for inlining starts above all renamed main locals,
  -- including params used only by `compileMainParamBindings`.
  let initNextFresh :=
    max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
  let wBase := witnessBase m
  let numMembers := (m.structs mainIdx).members.length
  let mainParamBinds : List (FlatIR.Instr F) :=
    compileMainParamBindings (F := F) wBase numMembers numParams ρ
  let (instrs, _, _) :=
    compileConstrainBody wBase m mainIdx initObjEnv initNextFresh renamedBody
  mainParamBinds ++ instrs

instance CorrectPass (F : Type) [Field F] (n : Nat) :
    Pass (StructIR.Language n F) (FlatIR.Language F) where
  compile := compileProgram (F := F)
  witnessRel m ws wt :=
    ∀ pos, wt (encodeWitnessPos (witnessBase m) pos) = ws pos

/-- Seed only shifted witness slots from a StructIR witness; all locals default to `0`. -/
def witnessSlotLift (witnessBase : Nat) (w : StructIR.Witness F) : FlatIR.Witness F :=
  fun v =>
    if witnessBase ≤ v then
      w (VarIdEncoding.decode (v - witnessBase))
    else
      0

/-- Seed renamed main-param locals from canonical param witness coordinates. -/
def seedMainParamLocalsWitness (localBase numParams numMembers : Nat)
    (ws : StructIR.Witness F) (wt : FlatIR.Witness F) : FlatIR.Witness F :=
  fun v =>
    if localBase ≤ v ∧ v - localBase < numParams then
      ws (StructIR.paramCoord numMembers (v - localBase))
    else
      wt v

/-- Local environment for renamed main body: only renamed params are seeded. -/
def seedMainParamLocalsEnv (localBase numParams numMembers : Nat)
    (ws : StructIR.Witness F) : LocalEnv F :=
  fun v =>
    if localBase ≤ v ∧ v - localBase < numParams then
      ws (StructIR.paramCoord numMembers (v - localBase))
    else
      0

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

/-- Bridge source call semantics to the shifted environments induced by inlining.

    The right side is exactly the callee evaluation shape produced by
    `evalConstrainBody` for a source `call`. The left side is the environment
    shape expected by the callee IH after freshening/inlining setup. -/
theorem evalConstrainBody_call_freshened_iff
    (m : Module n F) (ws : StructIR.Witness F) (i : Fin n)
    (freshBase : Nat) (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (target : Fin i) (args : List Nat) :
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let calleeBody := (m.structs j).constrain.body
    let calleeEnv : LocalEnv F := fun param =>
      match args[param]? with
      | some arg => env (StructIRFreshen.freshMap freshBase arg)
      | none => 0
    let calleeObjEnv : ObjEnv := fun param =>
      match args[param]? with
      | some arg => objEnv (StructIRFreshen.freshMap freshBase arg)
      | none => []
    let adjustedObjEnv : ObjEnv := fun v =>
      if runFresh ≤ v then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => objEnv arg
        | none => []
      else []
    let adjustedEnv : LocalEnv F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < (m.structs j).constrain.numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => env arg
        | none => 0
      else 0
    evalConstrainBody m ws j (fun x => adjustedEnv (StructIRFreshen.freshMap runFresh x))
      (fun x => adjustedObjEnv (StructIRFreshen.freshMap runFresh x)) calleeBody ↔
      evalConstrainBody m ws j calleeEnv calleeObjEnv calleeBody := by
  intro j calleeBody calleeEnv calleeObjEnv adjustedObjEnv adjustedEnv
  have hObjEq : (adjustedObjEnv ∘ StructIRFreshen.freshMap runFresh) = calleeObjEnv := by
    funext param
    cases h : args[param]? with
    | none =>
        simp [Function.comp_apply, adjustedObjEnv, calleeObjEnv, StructIRFreshen.freshMap,
          h, Nat.add_sub_cancel_left]
    | some arg =>
        simp [Function.comp_apply, adjustedObjEnv, calleeObjEnv, StructIRFreshen.freshMap,
          h, Nat.add_sub_cancel_left]
  have hEnvAgree :
      ∀ v,
        (fun v => v < (m.structs j).constrain.numParams) v = true →
          (adjustedEnv ∘ StructIRFreshen.freshMap runFresh) v = calleeEnv v := by
    intro v hv
    have hv' : v < (m.structs j).constrain.numParams := by
      simpa using hv
    have hcond : runFresh ≤ StructIRFreshen.freshMap runFresh v ∧
        StructIRFreshen.freshMap runFresh v - runFresh < (m.structs j).constrain.numParams := by
      constructor
      · simp [StructIRFreshen.freshMap]
      · simpa [StructIRFreshen.freshMap] using hv'
    cases h : args[v]? with
    | none =>
        have hcond' : runFresh ≤ runFresh + v ∧ runFresh + v - runFresh < (m.structs j).constrain.numParams := by
          simpa [StructIRFreshen.freshMap, Nat.add_sub_cancel_left] using hcond
        simpa [Function.comp_apply, adjustedEnv, calleeEnv, StructIRFreshen.freshMap, h, hcond',
          Nat.add_sub_cancel_left]
    | some arg =>
        have hcond' : runFresh ≤ runFresh + v ∧ runFresh + v - runFresh < (m.structs j).constrain.numParams := by
          simpa [StructIRFreshen.freshMap, Nat.add_sub_cancel_left] using hcond
        have hnot : ¬ (m.structs j).constrain.numParams ≤ v := Nat.not_le_of_lt hv'
        simpa [Function.comp_apply, adjustedEnv, calleeEnv, StructIRFreshen.freshMap, h, hcond',
          Nat.add_sub_cancel_left, hnot]
  calc
    evalConstrainBody m ws j (fun x => adjustedEnv (StructIRFreshen.freshMap runFresh x))
        (fun x => adjustedObjEnv (StructIRFreshen.freshMap runFresh x)) calleeBody
      ↔ evalConstrainBody m ws j calleeEnv (adjustedObjEnv ∘ StructIRFreshen.freshMap runFresh)
          calleeBody :=
            evalConstrainBody_env_agree_on_init m ws j
              (adjustedEnv ∘ StructIRFreshen.freshMap runFresh) calleeEnv
              (adjustedObjEnv ∘ StructIRFreshen.freshMap runFresh) calleeBody (m.all_ssa j) hEnvAgree
    _ ↔ evalConstrainBody m ws j calleeEnv calleeObjEnv calleeBody := by
          simpa [hObjEq]

/-- Extract per-param equality from `compileParamBindings` satisfaction (inner loop). -/
lemma compileParamBindings_go_env_agree (args : List Nat) (nextFresh : Nat)
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
lemma compileParamBindings_env_agree (numParams : Nat) (args : List Nat) (nextFresh : Nat)
    (wt : FlatIR.Witness F)
    (hParam : FlatIR.satisfies wt
      (compileParamBindings numParams args (StructIRFreshen.freshMap nextFresh)))
    (param : Nat) (hlt : param < numParams) :
    wt (StructIRFreshen.freshMap nextFresh param) =
    match args[param]? with | some arg => wt arg | none => 0 := by
  unfold compileParamBindings at hParam
  have := compileParamBindings_go_env_agree args nextFresh wt 0 numParams hParam param hlt
  simpa using this

/-! ### Forward direction for parameter bindings -/

/-- Forward direction of `compileParamBindings_go_env_agree`. -/
lemma compileParamBindings_go_satisfies_of_agree
    (args : List Nat) (nextFresh : Nat) (wt : FlatIR.Witness F)
    (idx remaining : Nat)
    (hagree : ∀ param, param < remaining →
      wt (StructIRFreshen.freshMap nextFresh (idx + param)) =
        match args[idx + param]? with | some arg => wt arg | none => 0) :
    FlatIR.satisfies wt
      (compileParamBindings.go (F := F) args
        (StructIRFreshen.freshMap nextFresh) idx remaining) := by
  induction remaining generalizing idx with
  | zero => intro instr hmem; simp [compileParamBindings.go] at hmem
  | succ k ih =>
    have h0 := hagree 0 (Nat.succ_pos _)
    simp only [Nat.add_zero] at h0
    have ih' : FlatIR.satisfies wt
        (compileParamBindings.go (F := F) args (StructIRFreshen.freshMap nextFresh)
          (idx + 1) k) := by
      apply ih
      intro p hp
      have hp' : p + 1 < k + 1 := Nat.succ_lt_succ hp
      have := hagree (p + 1) hp'
      have heq : idx + 1 + p = idx + (p + 1) := by omega
      simp only [heq]
      exact this
    intro instr hmem
    simp only [compileParamBindings.go] at hmem
    rcases List.mem_append.mp hmem with hHead | hRest
    · cases hcase : args[idx]? with
      | some arg =>
        rw [hcase] at hHead
        simp only [List.mem_singleton] at hHead
        subst hHead
        simp only [FlatIR.satisfiesInstr]
        simpa [hcase] using h0
      | none =>
        rw [hcase] at hHead
        simp only [List.mem_singleton] at hHead
        subst hHead
        simp only [FlatIR.satisfiesInstr]
        simpa [hcase] using h0
    · exact ih' instr hRest

/-- Forward direction: given per-param equality, `compileParamBindings` is satisfied. -/
lemma compileParamBindings_satisfies_of_agree
    (numParams : Nat) (args : List Nat) (nextFresh : Nat) (wt : FlatIR.Witness F)
    (hagree : ∀ param, param < numParams →
      wt (StructIRFreshen.freshMap nextFresh param) =
        match args[param]? with | some arg => wt arg | none => 0) :
    FlatIR.satisfies wt
      (compileParamBindings (F := F) numParams args (StructIRFreshen.freshMap nextFresh)) := by
  unfold compileParamBindings
  exact compileParamBindings_go_satisfies_of_agree (F := F)
    args nextFresh wt 0 numParams (by intro p hp; simpa using hagree p hp)

/-- Helper: body reflection for fixed `i`, given IH for all `j < i`. -/
 private theorem body_reflection_wt_aux (witnessBase : Nat) (m : Module n F)
    (w : StructIR.Witness F) (wt : FlatIR.Witness F)
    (hwt : ∀ pos, wt (encodeWitnessPos witnessBase pos) = w pos)
    (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      FlatIR.satisfies wt (compileConstrainBody witnessBase m j objEnv nextFresh stmts).1 →
      evalConstrainBody m w j wt objEnv stmts)
    (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSat : FlatIR.satisfies wt (compileConstrainBody witnessBase m i objEnv nextFresh stmts).1) :
    evalConstrainBody m w i wt objEnv stmts := by
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
      have hwval : w (objEnv self, member.val) = wt dest := by
        rw [hI]
        simpa [encodeWitnessVar, encodeWitnessPos] using (hwt (objEnv self, member.val)).symm
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
      let reservedNextFresh := max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
      let paramBinds :=
        compileParamBindings (F := F) (m.structs j).constrain.numParams args ρ'
      let compileResult :=
        compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody
      let calleeInstrs := compileResult.1
      let nextFresh'' := compileResult.2.2
      let tailResult := compileConstrainBody witnessBase m i objEnv nextFresh'' rest
      let tailProg := tailResult.1
      simp only [compileConstrainBody] at hSat
      rw [satisfies_append] at hSat
      obtain ⟨hParamCallee, hTail⟩ := hSat
      rw [satisfies_append] at hParamCallee
      obtain ⟨hParam, hCallee⟩ := hParamCallee
      have hCalleeAdj : FlatIR.satisfies wt
          (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1 := by
        simpa [calleeInstrs, compileResult] using hCallee
      have hCalleeEval : evalConstrainBody m w j wt adjustedObjEnv freshBody :=
        ih_i j hj adjustedObjEnv reservedNextFresh freshBody hCalleeAdj
      have hTailProg : FlatIR.satisfies wt
          (compileConstrainBody witnessBase m i objEnv nextFresh'' rest).1 := by
        simpa [tailProg, tailResult] using hTail
      have hRestEval : evalConstrainBody m w i wt objEnv rest :=
        ih objEnv nextFresh'' hTailProg
      simp only [evalConstrainBody]
      refine ⟨?_, hRestEval⟩
      have hFreshEq : freshBody = StructIRFreshen.renameBody ρ' calleeBody := by
        unfold freshBody freshenResult ρ'
        rfl
      have hCalleeEval' : evalConstrainBody m w j wt adjustedObjEnv
          (StructIRFreshen.renameBody ρ' calleeBody) := by
        simpa [hFreshEq] using hCalleeEval
      have hRename := (StructIRFreshen.evalConstrainBody_rename m w j wt adjustedObjEnv ρ'
        (StructIRFreshen.freshMap_injective nextFresh) calleeBody).mp hCalleeEval'
      have hObjEnvEq : adjustedObjEnv ∘ ρ' = calleeObjEnv := by
        funext param
        simp [adjustedObjEnv, ρ', StructIRFreshen.freshMap, Function.comp]
      rw [hObjEnvEq] at hRename
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => wt arg | none => 0
      apply (evalConstrainBody_env_agree_on_init m w j (wt ∘ ρ') calleeEnv calleeObjEnv
        calleeBody (hSSA j) ?_).mp hRename
      intro v hv
      simp only [Function.comp, calleeEnv, ρ']
      have hEq := compileParamBindings_env_agree (m.structs j).constrain.numParams args nextFresh
        wt hParam v (by simpa using hv)
      simp [StructIRFreshen.freshMap] at hEq ⊢
      split <;> simp_all

theorem body_reflection_wt (witnessBase : Nat) (m : Module n F)
    (w : StructIR.Witness F) (wt : FlatIR.Witness F)
    (hwt : ∀ pos, wt (encodeWitnessPos witnessBase pos) = w pos) (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
    (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSat : FlatIR.satisfies wt
      (compileConstrainBody witnessBase m i objEnv nextFresh stmts).1) :
    evalConstrainBody m w i wt objEnv stmts := by
  revert i objEnv nextFresh stmts hSat
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      FlatIR.satisfies wt (compileConstrainBody witnessBase m i objEnv nextFresh stmts).1 →
      evalConstrainBody m w i wt objEnv stmts)
  · intro k ih_k i hi objEnv nextFresh stmts hSat
    apply body_reflection_wt_aux witnessBase m w wt hwt i hSSA
    · intro j hj
      exact ih_k j.val (hi ▸ hj) j rfl
    · exact hSat
  · rfl

/-- Extract per-param equality from `compileMainParamBindings.go` satisfaction. -/
lemma compileMainParamBindings_go_env_agree (witnessBase numMembers : Nat) (ρ : Nat → Nat)
    (wt : FlatIR.Witness F) (idx remaining : Nat)
    (hParam : FlatIR.satisfies wt
      (compileMainParamBindings.go (F := F) witnessBase numMembers ρ idx remaining))
    (param : Nat) (hlt : param < remaining) :
    wt (ρ (idx + param)) = wt (encodeParamVar witnessBase numMembers (idx + param)) := by
  induction remaining generalizing idx param with
  | zero => omega
  | succ k ih =>
    simp only [compileMainParamBindings.go] at hParam
    rw [satisfies_cons] at hParam
    obtain ⟨hHead, hRest⟩ := hParam
    cases param with
    | zero =>
      simp only [Nat.add_zero]
      simpa [FlatIR.satisfiesInstr] using hHead
    | succ p =>
      have hlt' : p < k := Nat.lt_of_succ_lt_succ hlt
      have := ih (idx + 1) hRest p hlt'
      simpa [Nat.add_assoc, Nat.add_comm 1 p] using this

/-- From `compileMainParamBindings` satisfaction, extract per-param equality
    relating each renamed param `ρ p` to its canonical param-witness coord. -/
lemma compileMainParamBindings_env_agree
    (witnessBase numMembers numParams : Nat) (ρ : Nat → Nat) (wt : FlatIR.Witness F)
    (hParam : FlatIR.satisfies wt
      (compileMainParamBindings (F := F) witnessBase numMembers numParams ρ))
    (param : Nat) (hlt : param < numParams) :
    wt (ρ param) = wt (encodeParamVar witnessBase numMembers param) := by
  unfold compileMainParamBindings at hParam
  have := compileMainParamBindings_go_env_agree (F := F) witnessBase numMembers ρ wt 0 numParams
    hParam param hlt
  simpa using this

/-! ### Forward direction for main-param bindings -/

/-- Forward direction of `compileMainParamBindings_go_env_agree`. -/
lemma compileMainParamBindings_go_satisfies_of_agree
    (witnessBase numMembers : Nat) (ρ : Nat → Nat) (wt : FlatIR.Witness F)
    (idx remaining : Nat)
    (hagree : ∀ param, param < remaining →
      wt (ρ (idx + param)) = wt (encodeParamVar witnessBase numMembers (idx + param))) :
    FlatIR.satisfies wt
      (compileMainParamBindings.go (F := F) witnessBase numMembers ρ idx remaining) := by
  induction remaining generalizing idx with
  | zero => intro instr hmem; simp [compileMainParamBindings.go] at hmem
  | succ k ih =>
    have h0 := hagree 0 (Nat.succ_pos _)
    simp only [Nat.add_zero] at h0
    have ih' : FlatIR.satisfies wt
        (compileMainParamBindings.go (F := F) witnessBase numMembers ρ (idx + 1) k) := by
      apply ih
      intro p hp
      have hp' : p + 1 < k + 1 := Nat.succ_lt_succ hp
      have := hagree (p + 1) hp'
      have heq : idx + 1 + p = idx + (p + 1) := by omega
      simp only [heq]
      exact this
    intro instr hmem
    simp only [compileMainParamBindings.go] at hmem
    rcases List.mem_cons.mp hmem with hHead | hRest
    · subst hHead
      simp only [FlatIR.satisfiesInstr]
      exact h0
    · exact ih' instr hRest

/-- Forward direction: if `wt` agrees on shifted param slots with renamed-param locals,
    `compileMainParamBindings` is satisfied. -/
lemma compileMainParamBindings_satisfies_of_agree
    (witnessBase numMembers numParams : Nat) (ρ : Nat → Nat) (wt : FlatIR.Witness F)
    (hagree : ∀ param, param < numParams →
      wt (ρ param) = wt (encodeParamVar witnessBase numMembers param)) :
    FlatIR.satisfies wt
      (compileMainParamBindings (F := F) witnessBase numMembers numParams ρ) := by
  unfold compileMainParamBindings
  exact compileMainParamBindings_go_satisfies_of_agree (F := F)
    witnessBase numMembers ρ wt 0 numParams
    (by intro p hp; simpa using hagree p hp)

/-- Object-environment agreement restricted to local `0` (`%self`).

    If two object environments `obj1`, `obj2` agree on `0` and the body only
    reads the object channel through `%self` (enforced by `objectSafe` with
    `init = fun v => v < numParams` and `numParams ≥ 1`), then evaluating the
    body under either yields the same proposition.

    Used to bridge `initObjEnv ∘ ρ` (which sends `ρ 0 ↦ []` and everything
    else to `[]` since `(fun _ => []) ∘ ρ = fun _ => []`) and the canonical
    `ObjEnv.update (fun _ => []) 0 []`. Both functions are equal pointwise
    (every input maps to `[]` initially), so we only need the trivial
    congruence — promoted to a named lemma for readability. -/
lemma evalConstrainBody_obj_funext (m : Module n F) (w : StructIR.Witness F)
    (i : Fin n) (env : LocalEnv F) (obj1 obj2 : ObjEnv)
    (body : List (ConstrainStmt n i F (m.structs i).members.length))
    (hobj : obj1 = obj2) :
    evalConstrainBody m w i env obj1 body ↔
      evalConstrainBody m w i env obj2 body := by
  subst hobj
  rfl

/-- Compilation never decreases freshness counter. -/
theorem compileConstrainBody_next_ge_aux (witnessBase : Nat) (m : Module n F)
    (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      nextFresh ≤ (compileConstrainBody witnessBase m j objEnv nextFresh stmts).2.2)
    (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    nextFresh ≤ (compileConstrainBody witnessBase m i objEnv nextFresh stmts).2.2 := by
  induction stmts generalizing objEnv nextFresh with
  | nil => simp [compileConstrainBody]
  | cons stmt rest ih =>
    cases stmt with
    | feltAdd dest src1 src2 => simpa [compileConstrainBody] using ih objEnv nextFresh
    | feltSub dest src1 src2 => simpa [compileConstrainBody] using ih objEnv nextFresh
    | feltMul dest src1 src2 => simpa [compileConstrainBody] using ih objEnv nextFresh
    | feltDiv dest src1 src2 => simpa [compileConstrainBody] using ih objEnv nextFresh
    | feltNeg dest src => simpa [compileConstrainBody] using ih objEnv nextFresh
    | feltConst dest c => simpa [compileConstrainBody] using ih objEnv nextFresh
    | readMember dest self member =>
      let path := objEnv self
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      simpa [compileConstrainBody, path, objEnvStep] using ih objEnvStep nextFresh
    | constrainEq src1 src2 => simpa [compileConstrainBody] using ih objEnv nextFresh
    | call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let ρ : Nat → Nat := StructIRFreshen.freshMap nextFresh
      let freshenResult := StructIRFreshen.freshenBody nextFresh calleeBody
      let freshBody := freshenResult.1
      let nextFresh' := freshenResult.2
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with
        | some arg => objEnv arg
        | none => []
      let adjustedObjEnv : ObjEnv := fun v =>
        if nextFresh ≤ v then calleeObjEnv (v - nextFresh) else []
      let reservedNextFresh := max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
      let hReserved : nextFresh ≤ reservedNextFresh := by
        exact
          le_trans (StructIRFreshen.freshenBody_next_ge nextFresh calleeBody)
            (Nat.le_max_left _ _)
      let hCallee : reservedNextFresh ≤
          (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2 :=
        ih_i j target.isLt adjustedObjEnv reservedNextFresh freshBody
      let hTail :
          (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2 ≤
          (compileConstrainBody witnessBase m i objEnv
            (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
            rest).2.2 :=
        ih objEnv _
      exact le_trans hReserved (le_trans hCallee (by simpa [compileConstrainBody, ρ, freshenResult,
        freshBody, nextFresh', calleeObjEnv, adjustedObjEnv, reservedNextFresh] using hTail))

/-- `compileConstrainBody` and `localCeilConstrainBody` compute same final freshness. -/
theorem compileConstrainBody_localCeil_eq_aux (witnessBase : Nat) (m : Module n F)
    (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      (compileConstrainBody witnessBase m j objEnv nextFresh stmts).2.2 =
        localCeilConstrainBody m j nextFresh stmts)
    (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    (compileConstrainBody witnessBase m i objEnv nextFresh stmts).2.2 =
      localCeilConstrainBody m i nextFresh stmts := by
  induction stmts generalizing objEnv nextFresh with
  | nil => simp [compileConstrainBody, localCeilConstrainBody]
  | cons stmt rest ih =>
      cases stmt with
      | feltAdd dest src1 src2 => simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltSub dest src1 src2 => simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltMul dest src1 src2 => simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltDiv dest src1 src2 => simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltNeg dest src => simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltConst dest c => simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | readMember dest self member =>
          let path := objEnv self
          let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
          simpa [compileConstrainBody, localCeilConstrainBody, path, objEnvStep] using
            ih objEnvStep nextFresh
      | constrainEq src1 src2 =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | call target args =>
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let calleeBody := (m.structs j).constrain.body
          let freshenResult := StructIRFreshen.freshenBody nextFresh calleeBody
          let freshBody := freshenResult.1
          let nextFresh' := freshenResult.2
          let calleeObjEnv : ObjEnv := fun param =>
            match args[param]? with
            | some arg => objEnv arg
            | none => []
          let adjustedObjEnv : ObjEnv := fun v =>
            if nextFresh ≤ v then calleeObjEnv (v - nextFresh) else []
          let reservedNextFresh := max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
          have hCallee :
              (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2 =
                localCeilConstrainBody m j reservedNextFresh freshBody :=
            ih_i j target.isLt adjustedObjEnv reservedNextFresh freshBody
          have hTail :
              (compileConstrainBody witnessBase m i objEnv
                (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
                rest).2.2 =
              localCeilConstrainBody m i
                (localCeilConstrainBody m j reservedNextFresh freshBody) rest := by
            simpa [hCallee] using
              ih objEnv (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
          simpa [compileConstrainBody, localCeilConstrainBody, calleeBody, freshenResult, freshBody,
            nextFresh', calleeObjEnv, adjustedObjEnv, reservedNextFresh] using hTail

/-- Compilation never decreases freshness counter. -/
theorem compileConstrainBody_next_ge (witnessBase : Nat) (m : Module n F)
    (i : Fin n) (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    nextFresh ≤ (compileConstrainBody witnessBase m i objEnv nextFresh stmts).2.2 := by
  revert i objEnv nextFresh stmts
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      nextFresh ≤ (compileConstrainBody witnessBase m i objEnv nextFresh stmts).2.2)
  · intro k ih_k i hi objEnv nextFresh stmts
    apply compileConstrainBody_next_ge_aux witnessBase m i
    intro j hj
    exact ih_k j.val (hi ▸ hj) j rfl
  · rfl

/-- `compileConstrainBody` returns exact final local ceiling. -/
theorem compileConstrainBody_localCeil_eq (witnessBase : Nat) (m : Module n F)
    (i : Fin n) (objEnv : ObjEnv) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    (compileConstrainBody witnessBase m i objEnv nextFresh stmts).2.2 =
      localCeilConstrainBody m i nextFresh stmts := by
  revert i objEnv nextFresh stmts
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (objEnv : ObjEnv) (nextFresh : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      (compileConstrainBody witnessBase m i objEnv nextFresh stmts).2.2 =
        localCeilConstrainBody m i nextFresh stmts)
  · intro k ih_k i hi objEnv nextFresh stmts
    apply compileConstrainBody_localCeil_eq_aux witnessBase m i
    intro j hj
    exact ih_k j.val (hi ▸ hj) j rfl
  · rfl

omit [Field F] in
/-- Folding `max` from seeded accumulator factors out initial seed. -/
lemma foldl_max_seed {α : Type} (f : α → Nat) (seed : Nat) (xs : List α) :
    xs.foldl (fun acc s => max acc (f s)) seed =
      max seed (xs.foldl (fun acc s => max acc (f s)) 0) := by
  induction xs generalizing seed with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (max seed (f x)), ih (max 0 (f x))]
      simp [max_assoc]

omit [Field F] in
/-- `maxVarBody` unfolds over cons. -/
lemma maxVarBody_cons {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm)) :
    StructIRFreshen.maxVarBody (stmt :: rest) =
      max (StructIRFreshen.maxVarStmt stmt) (StructIRFreshen.maxVarBody rest) := by
  unfold StructIRFreshen.maxVarBody
  simp only [List.foldl_cons]
  simpa using foldl_max_seed (f := StructIRFreshen.maxVarStmt)
    (StructIRFreshen.maxVarStmt stmt) rest

/-- Final local ceiling always stays above starting freshness. -/
theorem localCeilConstrainBody_next_ge (m : Module n F)
    (i : Fin n) (nextFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    nextFresh ≤ localCeilConstrainBody m i nextFresh stmts := by
  simpa [compileConstrainBody_localCeil_eq (witnessBase := 0) (m := m) (i := i)
    (objEnv := fun _ => []) (nextFresh := nextFresh) (stmts := stmts)] using
    compileConstrainBody_next_ge (witnessBase := 0) (m := m) i (fun _ => []) nextFresh stmts

/-- Seeded shifted witness slots decode back to their original coordinates. -/
lemma witnessSlotLift_encodeWitnessPos (witnessBase : Nat) (w : StructIR.Witness F)
    (pos : StructIR.VarId) :
    witnessSlotLift witnessBase w (encodeWitnessPos witnessBase pos) = w pos := by
  simp [witnessSlotLift, encodeWitnessPos, VarIdEncoding.decode_encode]

/-! ## Forward materializer for `StructIR -> FlatIR` preservation

`materializeConstrainBody` mirrors `compileConstrainBody` one-to-one, writing
into a FlatIR witness `wt` so that each emitted instruction is satisfied. It
threads the same `(env, objEnv, nextFresh)` triple as `evalConstrainBody`, and
its writes go only to FlatIR locals `< witnessBase m`. Shifted witness slots
seeded from a `StructIR.Witness ws` are therefore left intact.

Used in `CorrectPreservingPass` below to construct the FlatIR witness from a
source-satisfying `ws`. -/

/-- One step of the materializer: update a FlatIR witness from a single source
    statement, mirroring the FlatIR instructions emitted by
    `compileConstrainBody` for that statement. The new state matches
    `(env', objEnv', nextFresh')` from `evalConstrainBody`. -/
def materializeConstrainBody (witnessBase : Nat)
    (m : StructIR.Module n F)
    (i : Fin n) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    FlatIR.Witness F :=
  match stmts with
  | [] => wt
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      let val := env src1 + env src2
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnv nextFresh rest
    | .feltSub dest src1 src2 =>
      let val := env src1 - env src2
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnv nextFresh rest
    | .feltMul dest src1 src2 =>
      let val := env src1 * env src2
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnv nextFresh rest
    | .feltDiv dest src1 src2 =>
      let val := env src1 * (env src2)⁻¹
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnv nextFresh rest
    | .feltNeg dest src =>
      let val := -(env src)
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnv nextFresh rest
    | .feltConst dest c =>
      let val := c
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnv nextFresh rest
    | .readMember dest self member =>
      -- `readMember` lowers to `assertEq dest witnessVar`. The witness slot is
      -- already seeded with `ws (path, member.val)`, so we just write `dest`.
      let path := objEnv self
      let val := wt (encodeWitnessVar witnessBase path member.val)
      let wt' : FlatIR.Witness F := fun v => if v = dest then val else wt v
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      materializeConstrainBody witnessBase m i wt' (env.update dest val)
        objEnvStep nextFresh rest
    | .constrainEq _ _ =>
      -- `constrainEq` lowers to `assertEq src1 src2`. No write needed; both
      -- sides are already assigned and the source semantics provides
      -- `env src1 = env src2`, which equals `wt src1 = wt src2` under the
      -- agreement invariant.
      materializeConstrainBody witnessBase m i wt env objEnv nextFresh rest
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let (freshBody, nextFresh') := StructIRFreshen.freshenBody nextFresh calleeBody
      let calleeObjEnv : StructIR.ObjEnv := fun param =>
        match args[param]? with
        | some arg => objEnv arg
        | none => []
      let adjustedObjEnv : StructIR.ObjEnv := fun v =>
        if nextFresh ≤ v then calleeObjEnv (v - nextFresh) else []
      -- Pre-bind the freshened parameter slots `ρ p` from the caller args.
      let wtParams : FlatIR.Witness F := fun v =>
        if nextFresh ≤ v ∧ v - nextFresh < (m.structs j).constrain.numParams then
          match args[v - nextFresh]? with
          | some arg => wt arg
          | none => 0
        else
          wt v
      -- Compute the callee's local environment from the freshened-arg view of
      -- the caller's environment.
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with
        | some arg => env arg
        | none => 0
      let adjustedEnv : LocalEnv F := fun v =>
        if nextFresh ≤ v ∧ v - nextFresh < (m.structs j).constrain.numParams then
          calleeEnv (v - nextFresh)
        else
          0
      let reservedNextFresh := max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
      let wtAfterCallee :=
        materializeConstrainBody witnessBase m j wtParams adjustedEnv
          adjustedObjEnv reservedNextFresh freshBody
      let nextFresh'' :=
        (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
      materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh'' rest
termination_by (i, stmts.length)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.left; exact target.isLt
    | apply Prod.Lex.right; simp

theorem materializeConstrainBody_feltAdd_rename_eq (witnessBase : Nat)
    (m : StructIR.Module n F) (i : Fin n) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : StructIR.ObjEnv) (runFresh freshBase : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
        (.feltAdd dest src1 src2 :: rest)) =
      let val :=
        env (StructIRFreshen.freshMap freshBase src1) +
          env (StructIRFreshen.freshMap freshBase src2)
      let wt' : FlatIR.Witness F :=
        fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v
      materializeConstrainBody witnessBase m i wt'
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        objEnv runFresh (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) := by
  simp [materializeConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt]

theorem materializeConstrainBody_constrainEq_rename_eq (witnessBase : Nat)
    (m : StructIR.Module n F) (i : Fin n) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : StructIR.ObjEnv) (runFresh freshBase src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
        (.constrainEq src1 src2 :: rest)) =
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) := by
  simp [materializeConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt]

theorem materializeConstrainBody_readMember_rename_eq (witnessBase : Nat)
    (m : StructIR.Module n F) (i : Fin n) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : StructIR.ObjEnv) (runFresh freshBase : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
        (.readMember dest self member :: rest)) =
      let path := objEnv (StructIRFreshen.freshMap freshBase self)
      let val := wt (encodeWitnessVar witnessBase path member.val)
      let wt' : FlatIR.Witness F :=
        fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v
      let objEnvStep :=
        StructIR.ObjEnv.update objEnv
          (StructIRFreshen.freshMap freshBase dest) (path ++ [member.val])
      materializeConstrainBody witnessBase m i wt'
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        objEnvStep runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) := by
  simp [materializeConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt]

theorem materializeConstrainBody_call_rename_eq (witnessBase : Nat)
    (m : StructIR.Module n F) (i : Fin n) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : StructIR.ObjEnv) (runFresh freshBase : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
        (.call target args :: rest)) =
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let adjustedObjEnv : StructIR.ObjEnv := fun v =>
        if runFresh ≤ v then
          match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
          | some arg => objEnv arg
          | none => []
        else
          []
      let wtParams : FlatIR.Witness F := fun v =>
        if runFresh ≤ v ∧ v - runFresh < (m.structs j).constrain.numParams then
          match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
          | some arg => wt arg
          | none => 0
        else
          wt v
      let adjustedEnv : LocalEnv F := fun v =>
        if runFresh ≤ v ∧ v - runFresh < (m.structs j).constrain.numParams then
          match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
          | some arg => env arg
          | none => 0
        else
          0
      let reservedNextFresh :=
        max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
          (runFresh + (m.structs j).constrain.numParams)
      let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
      let wtAfterCallee :=
        materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
          reservedNextFresh freshBody
      let nextFresh'' :=
        (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
      materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) := by
  simp [materializeConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt,
    StructIRFreshen.freshenBody]
  rfl

omit [Field F] in
/-- Updating witness at freshened destination does not affect smaller slots. -/
lemma witness_update_fresh_frame (wt : FlatIR.Witness F) (nextFresh dest v : Nat) (val : F)
    (hv : v < nextFresh) :
    (fun u => if u = StructIRFreshen.freshMap nextFresh dest then val else wt u) v = wt v := by
  have hne : v ≠ StructIRFreshen.freshMap nextFresh dest :=
    StructIRFreshen.fresh_old_disjoint nextFresh v dest hv
  simp [hne]

/-- Parameter seeding for inlined calls does not affect slots below `nextFresh`. -/
lemma materialize_call_param_seed_frame (wt : FlatIR.Witness F)
    (numParams nextFresh v : Nat) (args : List Nat) (hv : v < nextFresh) :
    (let wtParams : FlatIR.Witness F := fun u =>
      if nextFresh ≤ u ∧ u - nextFresh < numParams then
        match args[u - nextFresh]? with
        | some arg => wt arg
        | none => 0
      else
        wt u
    wtParams v) = wt v := by
  have hlt : ¬ (nextFresh ≤ v ∧ v - nextFresh < numParams) := by
    intro h
    omega
  simp [hlt]

omit [Field F] in
/-- Freshness counter used after inlined call stays above original `nextFresh`. -/
lemma call_reservedNextFresh_ge (m : Module n F) (i : Fin n) (target : Fin i)
    (nextFresh : Nat) :
    nextFresh ≤
      max (StructIRFreshen.freshenBody nextFresh (m.structs ⟨target.val,
            Nat.lt_trans target.isLt i.isLt⟩).constrain.body).2
        (nextFresh +
          (m.structs ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩).constrain.numParams) := by
  apply le_max_of_le_left
  exact StructIRFreshen.freshenBody_next_ge nextFresh _

/-- Tail induction remains usable after fresh-only witness update. -/
lemma materialize_tail_of_witness_update_frame_gen
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
      (objEnv : ObjEnv) (runFresh v : Nat),
      freshBase ≤ runFresh →
      v < freshBase →
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v = wt v)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest v : Nat) (val : F) (hle : freshBase ≤ runFresh) (hv : v < freshBase) :
    materializeConstrainBody witnessBase m i
        (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u)
        env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v = wt v := by
  have hvRun : v < runFresh := lt_of_lt_of_le hv hle
  calc
    materializeConstrainBody witnessBase m i
        (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u)
        env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
      = (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u) v :=
          ih freshBase _ _ _ _ _ hle hv
    _ = wt v := witness_update_fresh_frame _ _ _ _ _ hv

/-- Tail induction also survives matching object-environment update at fresh destination. -/
lemma materialize_tail_of_read_frame_gen
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
      (objEnv : ObjEnv) (runFresh v : Nat),
      freshBase ≤ runFresh →
      v < freshBase →
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v = wt v)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest v : Nat) (val : F) (path : InstancePath)
    (hle : freshBase ≤ runFresh) (hv : v < freshBase) :
    materializeConstrainBody witnessBase m i
        (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u)
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest) path)
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v = wt v := by
  calc
    materializeConstrainBody witnessBase m i
        (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u)
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest) path)
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
      = (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u) v :=
          ih freshBase _ _ _ _ _ hle hv
    _ = wt v := witness_update_fresh_frame _ _ _ _ _ hv

/-- Materializing a freshened body never changes witness slots below `freshBase`. -/
theorem materializeConstrainBody_fresh_frame_aux
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (runFresh v : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      freshBase ≤ runFresh →
      v < freshBase →
        materializeConstrainBody witnessBase m j wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hle : freshBase ≤ runFresh) (hv : v < freshBase) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  induction stmts generalizing freshBase wt env objEnv runFresh v with
  | nil => simp [materializeConstrainBody, StructIRFreshen.renameBody]
  | cons stmt rest ih =>
      cases stmt with
      | feltAdd dest src1 src2 =>
          let val :=
            env (StructIRFreshen.freshMap freshBase src1) +
              env (StructIRFreshen.freshMap freshBase src2)
          simpa [materializeConstrainBody_feltAdd_rename_eq] using
            materialize_tail_of_witness_update_frame_gen witnessBase m i rest ih
              freshBase wt (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv
              runFresh dest v val hle hv
      | feltSub dest src1 src2 =>
          let val :=
            env (StructIRFreshen.freshMap freshBase src1) -
              env (StructIRFreshen.freshMap freshBase src2)
          simpa [materializeConstrainBody, StructIRFreshen.renameBody,
            StructIRFreshen.renameStmt] using
            materialize_tail_of_witness_update_frame_gen witnessBase m i rest ih
              freshBase wt (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv
              runFresh dest v val hle hv
      | feltMul dest src1 src2 =>
          let val :=
            env (StructIRFreshen.freshMap freshBase src1) *
              env (StructIRFreshen.freshMap freshBase src2)
          simpa [materializeConstrainBody, StructIRFreshen.renameBody,
            StructIRFreshen.renameStmt] using
            materialize_tail_of_witness_update_frame_gen witnessBase m i rest ih
              freshBase wt (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv
              runFresh dest v val hle hv
      | feltDiv dest src1 src2 =>
          let val :=
            env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹
          simpa [materializeConstrainBody, StructIRFreshen.renameBody,
            StructIRFreshen.renameStmt] using
            materialize_tail_of_witness_update_frame_gen witnessBase m i rest ih
              freshBase wt (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv
              runFresh dest v val hle hv
      | feltNeg dest src =>
          let val := -(env (StructIRFreshen.freshMap freshBase src))
          simpa [materializeConstrainBody, StructIRFreshen.renameBody,
            StructIRFreshen.renameStmt] using
            materialize_tail_of_witness_update_frame_gen witnessBase m i rest ih
              freshBase wt (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv
              runFresh dest v val hle hv
      | feltConst dest c =>
          simpa [materializeConstrainBody, StructIRFreshen.renameBody,
            StructIRFreshen.renameStmt] using
            materialize_tail_of_witness_update_frame_gen witnessBase m i rest ih
              freshBase wt (env.update (StructIRFreshen.freshMap freshBase dest) c) objEnv
              runFresh dest v c hle hv
      | readMember dest self member =>
          let path := objEnv (StructIRFreshen.freshMap freshBase self)
          let val := wt (encodeWitnessVar witnessBase path member.val)
          simpa [materializeConstrainBody_readMember_rename_eq, path, val] using
            materialize_tail_of_read_frame_gen witnessBase m i rest ih
              freshBase wt env objEnv runFresh dest v val (path ++ [member.val]) hle hv
      | constrainEq src1 src2 =>
          simpa [materializeConstrainBody_constrainEq_rename_eq] using
            ih freshBase wt env objEnv runFresh v hle hv
      | call target args =>
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let calleeBody := (m.structs j).constrain.body
          let adjustedObjEnv : ObjEnv := fun x =>
            if runFresh ≤ x then
              match Option.map (StructIRFreshen.freshMap freshBase) args[x - runFresh]? with
              | some arg => objEnv arg
              | none => []
            else
              []
          let wtParams : FlatIR.Witness F := fun x =>
            if runFresh ≤ x ∧ x - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase) args[x - runFresh]? with
              | some arg => wt arg
              | none => 0
            else
              wt x
          let adjustedEnv : LocalEnv F := fun x =>
            if runFresh ≤ x ∧ x - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase) args[x - runFresh]? with
              | some arg => env arg
              | none => 0
            else
              0
          let reservedNextFresh :=
            max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
              (runFresh + (m.structs j).constrain.numParams)
          let freshBody := StructIRFreshen.renameBody (fun x => runFresh + x) calleeBody
          let wtAfterCallee :=
            materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
              reservedNextFresh freshBody
          let nextFresh'' :=
            (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
          have hReserved : runFresh ≤ reservedNextFresh := by
            have hReserved' :=
              call_reservedNextFresh_ge (m := m) (i := i) (target := target) runFresh
            simpa [reservedNextFresh, calleeBody] using hReserved'
          have hvRun : v < runFresh := lt_of_lt_of_le hv hle
          have hCalleeFrame : wtAfterCallee v = wt v := by
            calc
              wtAfterCallee v = wtParams v := by
                simpa [j, calleeBody, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
                  freshBody, wtAfterCallee] using
                  ih_i j target.isLt runFresh wtParams adjustedEnv adjustedObjEnv
                    reservedNextFresh v calleeBody hReserved hvRun
              _ = wt v := by
                simpa [wtParams] using
                  materialize_call_param_seed_frame wt (m.structs j).constrain.numParams
                    runFresh v (args.map (StructIRFreshen.freshMap freshBase)) hvRun
          have hNextFresh : reservedNextFresh ≤ nextFresh'' := by
            simpa [j, adjustedObjEnv, reservedNextFresh, freshBody, nextFresh''] using
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh freshBody
          have hleTail : freshBase ≤ nextFresh'' := le_trans hle (le_trans hReserved hNextFresh)
          have hCall :
              materializeConstrainBody witnessBase m i wt env objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
                  (.call target args :: rest)) v =
              materializeConstrainBody witnessBase m i wtAfterCallee env objEnv
                nextFresh''
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v := by
            have h := congrArg (fun w => w v)
              (materializeConstrainBody_call_rename_eq witnessBase m i wt env objEnv runFresh
                freshBase target args rest)
            simpa [j, calleeBody, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
              freshBody, wtAfterCallee, nextFresh''] using h
          calc
            materializeConstrainBody witnessBase m i wt env objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
                  (.call target args :: rest)) v
              = materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
                  (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v := hCall
            _ = wtAfterCallee v := ih freshBase wtAfterCallee env objEnv nextFresh'' v hleTail hv
            _ = wt v := hCalleeFrame

/-- Materializing a freshened body never changes witness slots below fresh prefix. -/
theorem materializeConstrainBody_fresh_frame (witnessBase : Nat) (m : Module n F)
    (i : Fin n) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : ObjEnv) (runFresh v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hle : freshBase ≤ runFresh) (hv : v < freshBase) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  revert i freshBase wt env objEnv runFresh v stmts hle hv
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (runFresh v : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      freshBase ≤ runFresh →
      v < freshBase →
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v)
  · intro k ih_k i hi freshBase wt env objEnv runFresh v stmts hle hv
    refine materializeConstrainBody_fresh_frame_aux witnessBase m i ?_ freshBase wt env objEnv
      runFresh v stmts hle hv
    intro j hj freshBase' wt' env' objEnv' runFresh' v' stmts' hle' hv'
    exact ih_k j.val (hi ▸ hj) j rfl freshBase' wt' env' objEnv' runFresh' v' stmts' hle' hv'
  · rfl

/-- Materializing a freshened body does not change slots in `[low, freshBase)`.
    Useful after inlined calls: caller tail starts at `nextFresh''`, while callee
    writes stay either below `runFresh` or above/equal `nextFresh''`. -/
theorem materializeConstrainBody_interval_frame (witnessBase : Nat) (m : Module n F)
    (i : Fin n) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : ObjEnv) (runFresh low v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hle : freshBase ≤ runFresh) (hlow : low ≤ v) (hv : v < freshBase) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  exact materializeConstrainBody_fresh_frame witnessBase m i freshBase wt env objEnv runFresh v stmts
    hle hv

/-! ## High-frame lemmas: materializer writes never touch slots ≥ `localCeil` -/

omit [Field F] in
/-- Writing at `freshMap freshBase dest` does not affect slots above `runFresh`,
    when `freshBase + dest < runFresh`. -/
lemma witness_update_high_frame (wt : FlatIR.Witness F)
    (freshBase dest runFresh v : Nat) (val : F)
    (hlt : freshBase + dest < runFresh) (hle : runFresh ≤ v) :
    (fun u => if u = StructIRFreshen.freshMap freshBase dest then val else wt u) v = wt v := by
  have hne : v ≠ StructIRFreshen.freshMap freshBase dest := by
    intro h
    simp [StructIRFreshen.freshMap] at h
    omega
  simp [hne]

/-- Renaming a body does not change its local ceiling. -/
theorem localCeilConstrainBody_rename (m : Module n F)
    (i : Fin n) (nextFresh : Nat) (ρ : Nat → Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    localCeilConstrainBody m i nextFresh (StructIRFreshen.renameBody ρ stmts) =
      localCeilConstrainBody m i nextFresh stmts := by
  induction stmts generalizing nextFresh with
  | nil => simp [localCeilConstrainBody, StructIRFreshen.renameBody]
  | cons stmt rest ih =>
      cases stmt <;>
        (simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            localCeilConstrainBody]
         exact ih _)

omit [Field F] in
/-- `maxVarStmt stmt ≤ maxVarBody (stmt :: rest)`. -/
lemma maxVarStmt_le_maxVarBody_cons {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm)) :
    StructIRFreshen.maxVarStmt stmt ≤ StructIRFreshen.maxVarBody (stmt :: rest) := by
  rw [maxVarBody_cons]; exact le_max_left _ _

omit [Field F] in
/-- `maxVarBody rest ≤ maxVarBody (stmt :: rest)`. -/
lemma maxVarBody_tail_le_cons {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm)) :
    StructIRFreshen.maxVarBody rest ≤ StructIRFreshen.maxVarBody (stmt :: rest) := by
  rw [maxVarBody_cons]; exact le_max_right _ _

/-- High-frame aux: one i-level induction step.  Materializing a freshened body
    leaves slots at or above the body's local ceiling untouched, provided the
    body fits below the current run-fresh prefix. -/
theorem materializeConstrainBody_high_frame_aux
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (runFresh v : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      freshBase + StructIRFreshen.maxVarBody stmts < runFresh →
      localCeilConstrainBody m j runFresh stmts ≤ v →
      materializeConstrainBody witnessBase m j wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < runFresh)
    (hv : localCeilConstrainBody m i runFresh stmts ≤ v) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  induction stmts generalizing wt env objEnv runFresh with
  | nil => simp [materializeConstrainBody, StructIRFreshen.renameBody]
  | cons stmt rest ih =>
      have hFitRest : freshBase + StructIRFreshen.maxVarBody rest < runFresh := by
        have := maxVarBody_tail_le_cons stmt rest; omega
      have hRun_le_v : runFresh ≤ v := by
        have := localCeilConstrainBody_next_ge m i runFresh (stmt :: rest); omega
      cases stmt with
      | feltAdd dest src1 src2 =>
          rw [materializeConstrainBody_feltAdd_rename_eq]; simp only
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.feltAdd dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | feltSub dest src1 src2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.feltSub dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | feltMul dest src1 src2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.feltMul dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | feltDiv dest src1 src2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.feltDiv dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | feltNeg dest src =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.feltNeg dest src : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | feltConst dest c =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.feltConst dest c : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | readMember dest self member =>
          rw [materializeConstrainBody_readMember_rename_eq]; simp only
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.readMember dest self member : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | constrainEq src1 src2 =>
          rw [materializeConstrainBody_constrainEq_rename_eq]
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            simp [localCeilConstrainBody] at hv; exact hv
          exact ih _ _ _ _ hFitRest hv'
      | call target args =>
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let calleeBody := (m.structs j).constrain.body
          let adjustedObjEnv : ObjEnv := fun x =>
            if runFresh ≤ x then
              match Option.map (StructIRFreshen.freshMap freshBase)
                  args[x - runFresh]? with
              | some arg => objEnv arg | none => []
            else []
          let wtParams : FlatIR.Witness F := fun x =>
            if runFresh ≤ x ∧
                x - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase)
                  args[x - runFresh]? with
              | some arg => wt arg | none => 0
            else wt x
          let reservedNextFresh :=
            max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
              (runFresh + (m.structs j).constrain.numParams)
          let freshBody :=
            StructIRFreshen.renameBody (fun x => runFresh + x) calleeBody
          let wtAfterCallee :=
            materializeConstrainBody witnessBase m j wtParams
              (fun x =>
                if runFresh ≤ x ∧
                    x - runFresh < (m.structs j).constrain.numParams then
                  match Option.map (StructIRFreshen.freshMap freshBase)
                      args[x - runFresh]? with
                  | some arg => env arg | none => 0
                else 0)
              adjustedObjEnv reservedNextFresh freshBody
          let nextFresh'' :=
            (compileConstrainBody witnessBase m j adjustedObjEnv
              reservedNextFresh freshBody).2.2
          have hNextFresh''_eq :
              nextFresh'' =
                localCeilConstrainBody m j reservedNextFresh freshBody :=
            compileConstrainBody_localCeil_eq witnessBase m j adjustedObjEnv
              reservedNextFresh freshBody
          have hCeil_callee_ge : reservedNextFresh ≤
              localCeilConstrainBody m j reservedNextFresh freshBody :=
            localCeilConstrainBody_next_ge m j reservedNextFresh freshBody
          have hRunFresh_le_nextFresh'' : runFresh ≤ nextFresh'' := by
            have : runFresh ≤ reservedNextFresh := by
              simp [reservedNextFresh]
            rw [hNextFresh''_eq]; omega
          have hCeilCons :
              localCeilConstrainBody m i runFresh
                ((.call target args : ConstrainStmt n i F _) :: rest) =
              localCeilConstrainBody m i nextFresh'' rest := by
            simp only [localCeilConstrainBody, StructIRFreshen.freshenBody,
              hNextFresh''_eq]; rfl
          have hv_tail :
              localCeilConstrainBody m i nextFresh'' rest ≤ v :=
            hCeilCons ▸ hv
          have hv_nextFresh'' : nextFresh'' ≤ v := by
            have := localCeilConstrainBody_next_ge m i nextFresh'' rest
            omega
          have hFitCallee :
              runFresh + StructIRFreshen.maxVarBody calleeBody <
                reservedNextFresh := by
            simp [reservedNextFresh]
          have hv_callee :
              localCeilConstrainBody m j reservedNextFresh calleeBody ≤ v := by
            have hren :
                localCeilConstrainBody m j reservedNextFresh freshBody =
                localCeilConstrainBody m j reservedNextFresh calleeBody :=
              localCeilConstrainBody_rename m j reservedNextFresh
                (fun x => runFresh + x) calleeBody
            rw [hNextFresh''_eq, hren] at hv_nextFresh''
            exact hv_nextFresh''
          rw [materializeConstrainBody_call_rename_eq]; simp only
          have hTail :
              materializeConstrainBody witnessBase m i wtAfterCallee env
                objEnv nextFresh''
                (StructIRFreshen.renameBody
                  (StructIRFreshen.freshMap freshBase) rest) v
              = wtAfterCallee v :=
            ih _ _ _ _
              (lt_of_lt_of_le hFitRest hRunFresh_le_nextFresh'') hv_tail
          have hCallee : wtAfterCallee v = wtParams v := by
            change materializeConstrainBody witnessBase m j wtParams _
                  adjustedObjEnv reservedNextFresh freshBody v = wtParams v
            rw [show freshBody =
                StructIRFreshen.renameBody
                  (StructIRFreshen.freshMap runFresh) calleeBody from rfl]
            exact ih_i j target.isLt runFresh wtParams _ adjustedObjEnv
              reservedNextFresh v calleeBody hFitCallee hv_callee
          have hParam : wtParams v = wt v := by
            have : ¬ (runFresh ≤ v ∧
                v - runFresh < (m.structs j).constrain.numParams) := by
              intro ⟨_, hsub⟩
              have h1 :
                  runFresh + (m.structs j).constrain.numParams ≤
                    reservedNextFresh := by
                simp [reservedNextFresh]
              rw [hNextFresh''_eq] at hv_nextFresh''; omega
            simp [wtParams, this]
          calc _ = wtAfterCallee v := hTail
            _ = wtParams v := hCallee
            _ = wt v := hParam

/-- High-frame wrapper: writes by materializer never touch slots ≥ ceiling.
    Uses strong recursion on `i` to introduce `ih_i`. -/
theorem materializeConstrainBody_high_frame (witnessBase : Nat)
    (m : Module n F) (i : Fin n) (freshBase : Nat)
    (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < runFresh)
    (hv : localCeilConstrainBody m i runFresh stmts ≤ v) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
        stmts) v = wt v := by
  revert i freshBase wt env objEnv runFresh v stmts hFit hv
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (runFresh v : Nat)
        (stmts : List (ConstrainStmt n i F
          (m.structs i).members.length)),
      freshBase + StructIRFreshen.maxVarBody stmts < runFresh →
      localCeilConstrainBody m i runFresh stmts ≤ v →
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
            stmts) v = wt v)
  · intro k ih_k i hi freshBase wt env objEnv runFresh v stmts hFit hv
    refine materializeConstrainBody_high_frame_aux witnessBase m i
      ?_ freshBase wt env objEnv runFresh v stmts hFit hv
    intro j hj freshBase' wt' env' objEnv' runFresh' v' stmts' hFit' hv'
    exact ih_k j.val (hi ▸ hj) j rfl freshBase' wt' env' objEnv'
      runFresh' v' stmts' hFit' hv'
  · rfl

/-- Materializing a renamed caller suffix preserves any slot in `[anchor, runFresh)`.
    Non-call writes stay below `anchor`; nested calls allocate at or above the
    current `runFresh`, so they also miss this middle interval. -/
theorem materializeConstrainBody_middle_frame_aux
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (anchor runFresh v : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      freshBase + StructIRFreshen.maxVarBody stmts < anchor →
      anchor ≤ runFresh →
      anchor ≤ v →
      v < runFresh →
        materializeConstrainBody witnessBase m j wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (anchor runFresh v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < anchor)
    (hAnchorRun : anchor ≤ runFresh) (hAnchorV : anchor ≤ v) (hv : v < runFresh) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  induction stmts generalizing wt env objEnv runFresh with
  | nil => simp [materializeConstrainBody, StructIRFreshen.renameBody]
  | cons stmt rest ih =>
      have hFitRest : freshBase + StructIRFreshen.maxVarBody rest < anchor := by
        have := maxVarBody_tail_le_cons stmt rest
        omega
      cases stmt with
      | feltAdd dest src1 src2 =>
          rw [materializeConstrainBody_feltAdd_rename_eq]
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.feltAdd dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) +
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) +
                    env (StructIRFreshen.freshMap freshBase src2)))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) +
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := _)
                      (objEnv := objEnv)
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | feltSub dest src1 src2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.feltSub dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) -
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) -
                    env (StructIRFreshen.freshMap freshBase src2)))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) -
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := _)
                      (objEnv := objEnv)
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | feltMul dest src1 src2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.feltMul dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) *
                    env (StructIRFreshen.freshMap freshBase src2)))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := _)
                      (objEnv := objEnv)
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | feltDiv dest src1 src2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.feltDiv dest src1 src2 : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      (env (StructIRFreshen.freshMap freshBase src2))⁻¹
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) *
                    (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      (env (StructIRFreshen.freshMap freshBase src2))⁻¹
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := _)
                      (objEnv := objEnv)
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | feltNeg dest src =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.feltNeg dest src : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    -(env (StructIRFreshen.freshMap freshBase src))
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (-(env (StructIRFreshen.freshMap freshBase src))))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    -(env (StructIRFreshen.freshMap freshBase src))
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := _)
                      (objEnv := objEnv)
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | feltConst dest c =>
          simp only [StructIRFreshen.renameBody, List.map_cons,
            StructIRFreshen.renameStmt, materializeConstrainBody]
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.feltConst dest c : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then c else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest) c)
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then c else wt u) v := by
                    exact ih (wt := _)
                      (env := env.update (StructIRFreshen.freshMap freshBase dest) c)
                      (objEnv := objEnv)
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | readMember dest self member =>
          rw [materializeConstrainBody_readMember_rename_eq]
          simp only
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons (.readMember dest self member : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
                      member.val)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
                    member.val)))
                (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
                  (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
                runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
                      member.val)
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := env.update (StructIRFreshen.freshMap freshBase dest)
                        (wt (encodeWitnessVar witnessBase
                          (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
                      (objEnv := StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
                        (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
                      (runFresh := runFresh)
                      hFitRest hAnchorRun hv
            _ = wt v := by
                  exact witness_update_high_frame wt freshBase dest anchor v _ hDest hAnchorV
      | constrainEq src1 src2 =>
          rw [materializeConstrainBody_constrainEq_rename_eq]
          exact ih (wt := wt)
            (env := env)
            (objEnv := objEnv)
            (runFresh := runFresh)
            hFitRest hAnchorRun hv
      | call target args =>
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let calleeBody := (m.structs j).constrain.body
          let adjustedObjEnv : ObjEnv := fun x =>
            if runFresh ≤ x then
              match Option.map (StructIRFreshen.freshMap freshBase) args[x - runFresh]? with
              | some arg => objEnv arg
              | none => []
            else
              []
          let wtParams : FlatIR.Witness F := fun x =>
            if runFresh ≤ x ∧ x - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase) args[x - runFresh]? with
              | some arg => wt arg
              | none => 0
            else
              wt x
          let adjustedEnv : LocalEnv F := fun x =>
            if runFresh ≤ x ∧ x - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase) args[x - runFresh]? with
              | some arg => env arg
              | none => 0
            else
              0
          let reservedNextFresh :=
            max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
              (runFresh + (m.structs j).constrain.numParams)
          let freshBody := StructIRFreshen.renameBody (fun x => runFresh + x) calleeBody
          let wtAfterCallee :=
            materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
              reservedNextFresh freshBody
          let nextFresh'' :=
            (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
          have hReserved : runFresh ≤ reservedNextFresh := by
            simp [reservedNextFresh]
          have hCalleeFrame : wtAfterCallee v = wt v := by
            calc
              wtAfterCallee v = wtParams v := by
                change materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
                  reservedNextFresh freshBody v = wtParams v
                rw [show freshBody =
                    StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody by rfl]
                exact materializeConstrainBody_fresh_frame witnessBase m j runFresh wtParams adjustedEnv
                  adjustedObjEnv reservedNextFresh v calleeBody hReserved hv
              _ = wt v := by
                simpa [wtParams] using
                  materialize_call_param_seed_frame wt (m.structs j).constrain.numParams runFresh v
                    (args.map (StructIRFreshen.freshMap freshBase)) hv
          have hNext : runFresh ≤ nextFresh'' := by
            exact le_trans hReserved <|
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh freshBody
          have hAnchorRun' : anchor ≤ nextFresh'' := le_trans hAnchorRun hNext
          have hv' : v < nextFresh'' := lt_of_lt_of_le hv hNext
          have hTail :
              materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v =
                wtAfterCallee v := by
            exact ih (wt := wtAfterCallee)
              (env := env)
              (objEnv := objEnv)
              (runFresh := nextFresh'')
              hFitRest hAnchorRun' hv'
          have hCall :
              materializeConstrainBody witnessBase m i wt env objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
                  (.call target args :: rest)) v =
              materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v := by
            have h := congrArg (fun w => w v)
              (materializeConstrainBody_call_rename_eq witnessBase m i wt env objEnv runFresh
                freshBase target args rest)
            simpa [j, calleeBody, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
              freshBody, wtAfterCallee, nextFresh''] using h
          calc
            materializeConstrainBody witnessBase m i wt env objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
                  (.call target args :: rest)) v
              = materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
                  (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v := hCall
            _ = wtAfterCallee v := hTail
            _ = wt v := hCalleeFrame

/-- Middle-frame wrapper: if caller locals fit below `anchor`, materializing a
    caller suffix with current fresh counter `runFresh` leaves every slot in
    `[anchor, runFresh)` unchanged. -/
theorem materializeConstrainBody_middle_frame (witnessBase : Nat) (m : Module n F)
    (i : Fin n) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : ObjEnv) (anchor runFresh v : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < anchor)
    (hAnchorRun : anchor ≤ runFresh) (hAnchorV : anchor ≤ v) (hv : v < runFresh) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  revert i freshBase wt env objEnv anchor runFresh v stmts hFit hAnchorRun hAnchorV hv
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (anchor runFresh v : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      freshBase + StructIRFreshen.maxVarBody stmts < anchor →
      anchor ≤ runFresh →
      anchor ≤ v →
      v < runFresh →
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v)
  · intro k ih_k i hi freshBase wt env objEnv anchor runFresh v stmts hFit hAnchorRun hAnchorV hv
    refine materializeConstrainBody_middle_frame_aux witnessBase m i ?_ freshBase wt env objEnv
      anchor runFresh v stmts hFit hAnchorRun hAnchorV hv
    intro j hj freshBase' wt' env' objEnv' anchor' runFresh' v' stmts' hFit' hAnchorRun' hAnchorV' hv'
    exact ih_k j.val (hi ▸ hj) j rfl freshBase' wt' env' objEnv' anchor' runFresh' v' stmts'
      hFit' hAnchorRun' hAnchorV' hv'
  · rfl

lemma list_all_true_of_mem {α : Type}
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

omit [Field F] in
/-- In an SSA body, any written destination lies outside the initial set. -/
lemma isSSA_dest_not_init {i : Fin n} {nm : Nat} (init : Nat → Bool) :
    ∀ (body : List (ConstrainStmt n i F nm))
      (stmt : ConstrainStmt n i F nm) (dest : Nat),
      StructIR.isSSA init body = true →
      stmt ∈ body →
      stmt.dest = some dest →
      init dest = false := by
  intro body
  induction body generalizing init with
  | nil =>
      intro stmt dest _ hmem _
      cases hmem
  | cons head tail ih =>
      intro stmt dest hSSA hmem hdest
      simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
      obtain ⟨_, hSSA'⟩ := hSSA
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · subst hEq
        cases hs : stmt.dest with
        | none => simp [hs] at hdest
        | some d =>
            have hdest' : d = dest := by simpa [hs] using hdest
            subst hdest'
            have hHead : init d = false ∧ isSSA (fun x => init x || x == d) tail = true := by
              simpa [hs, Bool.and_eq_true] using hSSA'
            exact hHead.1
      · cases hs : head.dest with
        | none =>
            have hSSA'' : StructIR.isSSA init tail = true := by simpa [hs] using hSSA'
            exact ih init stmt dest hSSA'' hmem hdest
        | some d =>
            have hStep : init d = false ∧ isSSA (fun x => init x || x == d) tail = true := by
              simpa [hs, Bool.and_eq_true] using hSSA'
            have hSSA'' : StructIR.isSSA (fun x => init x || x == d) tail = true := hStep.2
            have hTail : (fun x => init x || x == d) dest = false :=
              ih (fun x => init x || x == d) stmt dest hSSA'' hmem hdest
            cases hInit : init dest with
            | false => rfl
            | true => simp [hInit] at hTail

omit [Field F] in
lemma init_true_dest_ne {init : Nat → Bool} {x dest : Nat}
    (hx : init x = true) (hd : init dest = false) : x ≠ dest := by
  intro h
  subst h
  rw [hx] at hd
  contradiction

/-- Renamed slots corresponding to initially-defined vars stay unchanged under
    materialization of an SSA body, as long as the slot lies below the current
    `runFresh` prefix. -/
theorem materializeConstrainBody_init_frame_aux
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (freshBase runFresh x : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      StructIR.isSSA init stmts = true →
      init x = true →
      StructIRFreshen.freshMap freshBase x < runFresh →
        materializeConstrainBody witnessBase m j wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
          (StructIRFreshen.freshMap freshBase x) =
        wt (StructIRFreshen.freshMap freshBase x))
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh x : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init stmts = true)
    (hx : init x = true)
    (hlt : StructIRFreshen.freshMap freshBase x < runFresh) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
      (StructIRFreshen.freshMap freshBase x) = wt (StructIRFreshen.freshMap freshBase x) := by
  induction stmts generalizing wt env objEnv runFresh init with
  | nil => simp [materializeConstrainBody, StructIRFreshen.renameBody]
  | cons stmt rest ih =>
      simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
      obtain ⟨_, hSSA'⟩ := hSSA
      cases stmt with
      | feltAdd dest src1 src2 =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          rw [materializeConstrainBody_feltAdd_rename_eq]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) +
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) +
                    env (StructIRFreshen.freshMap freshBase src2)))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) +
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u) (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | feltSub dest src1 src2 =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            materializeConstrainBody]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) -
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) -
                    env (StructIRFreshen.freshMap freshBase src2)))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) -
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u) (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | feltMul dest src1 src2 =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            materializeConstrainBody]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) *
                    env (StructIRFreshen.freshMap freshBase src2)))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      env (StructIRFreshen.freshMap freshBase src2)
                  else wt u) (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | feltDiv dest src1 src2 =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            materializeConstrainBody]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      (env (StructIRFreshen.freshMap freshBase src2))⁻¹
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) *
                    (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    env (StructIRFreshen.freshMap freshBase src1) *
                      (env (StructIRFreshen.freshMap freshBase src2))⁻¹
                  else wt u) (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | feltNeg dest src =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            materializeConstrainBody]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    -(env (StructIRFreshen.freshMap freshBase src))
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (-(env (StructIRFreshen.freshMap freshBase src))))
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    -(env (StructIRFreshen.freshMap freshBase src))
                  else wt u) (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | feltConst dest c =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            materializeConstrainBody]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then c else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest) c)
                objEnv runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then c else wt u)
                  (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | readMember dest self member =>
          have hStep : !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' : (!init dest = true) ∧ StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hdest : init dest = false := by simpa using hStep'.1
          have hne : x ≠ dest := init_true_dest_ne hx hdest
          rw [materializeConstrainBody_readMember_rename_eq]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
                      member.val)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
                    member.val)))
                (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
                  (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
                runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
                      member.val)
                  else wt u) (StructIRFreshen.freshMap freshBase x) := by
                    apply ih
                    · exact hStep'.2
                    · simp [hx]
                    · exact hlt
            _ = wt (StructIRFreshen.freshMap freshBase x) := by simp [StructIRFreshen.freshMap, hne]
      | constrainEq src1 src2 =>
          rw [materializeConstrainBody_constrainEq_rename_eq]
          exact ih init wt env objEnv runFresh hSSA' hx hlt
      | call target args =>
          rw [materializeConstrainBody_call_rename_eq]
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let calleeBody := (m.structs j).constrain.body
          let adjustedObjEnv : ObjEnv := fun z =>
            if runFresh ≤ z then
              match Option.map (StructIRFreshen.freshMap freshBase) args[z - runFresh]? with
              | some arg => objEnv arg
              | none => []
            else []
          let wtParams : FlatIR.Witness F := fun z =>
            if runFresh ≤ z ∧ z - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase) args[z - runFresh]? with
              | some arg => wt arg
              | none => 0
            else wt z
          let adjustedEnv : LocalEnv F := fun z =>
            if runFresh ≤ z ∧ z - runFresh < (m.structs j).constrain.numParams then
              match Option.map (StructIRFreshen.freshMap freshBase) args[z - runFresh]? with
              | some arg => env arg
              | none => 0
            else 0
          let reservedNextFresh :=
            max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
              (runFresh + (m.structs j).constrain.numParams)
          let freshBody := StructIRFreshen.renameBody (fun z => runFresh + z) calleeBody
          let wtAfterCallee :=
            materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
              reservedNextFresh freshBody
          let nextFresh'' :=
            (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
          have hReserved : runFresh ≤ reservedNextFresh := by simp [reservedNextFresh]
          have hCallee : wtAfterCallee (StructIRFreshen.freshMap freshBase x) =
              wtParams (StructIRFreshen.freshMap freshBase x) := by
            change materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
              reservedNextFresh freshBody (StructIRFreshen.freshMap freshBase x) =
              wtParams (StructIRFreshen.freshMap freshBase x)
            rw [show freshBody = StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody from rfl]
            exact materializeConstrainBody_fresh_frame witnessBase m j runFresh wtParams adjustedEnv
              adjustedObjEnv reservedNextFresh (StructIRFreshen.freshMap freshBase x) calleeBody hReserved hlt
          have hParams : wtParams (StructIRFreshen.freshMap freshBase x) =
              wt (StructIRFreshen.freshMap freshBase x) := by
            simpa [j, wtParams] using materialize_call_param_seed_frame wt
              (m.structs j).constrain.numParams runFresh (StructIRFreshen.freshMap freshBase x)
              (args.map (StructIRFreshen.freshMap freshBase)) hlt
          have hNext : runFresh ≤ nextFresh'' := by
            exact le_trans hReserved <|
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh freshBody
          calc
            materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = wtAfterCallee (StructIRFreshen.freshMap freshBase x) := by
                  apply ih
                  · exact hSSA'
                  · exact hx
                  · exact lt_of_lt_of_le hlt hNext
            _ = wtParams (StructIRFreshen.freshMap freshBase x) := hCallee
            _ = wt (StructIRFreshen.freshMap freshBase x) := hParams

theorem materializeConstrainBody_init_frame
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh x : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init stmts = true)
    (hx : init x = true)
    (hlt : StructIRFreshen.freshMap freshBase x < runFresh) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
      (StructIRFreshen.freshMap freshBase x) = wt (StructIRFreshen.freshMap freshBase x) := by
  revert i init wt env objEnv freshBase runFresh x stmts hSSA hx hlt
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (freshBase runFresh x : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      StructIR.isSSA init stmts = true →
      init x = true →
      StructIRFreshen.freshMap freshBase x < runFresh →
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
          (StructIRFreshen.freshMap freshBase x) =
        wt (StructIRFreshen.freshMap freshBase x))
  · intro k ih_k i hi init wt env objEnv freshBase runFresh x stmts hSSA hx hlt
    refine materializeConstrainBody_init_frame_aux witnessBase m i ?_ init wt env objEnv
      freshBase runFresh x stmts hSSA hx hlt
    intro j hj init' wt' env' objEnv' freshBase' runFresh' x' stmts' hSSA' hx' hlt'
    exact ih_k j.val (hi ▸ hj) j rfl init' wt' env' objEnv' freshBase' runFresh' x' stmts'
      hSSA' hx' hlt'
  · rfl

/-- Generic shifted-slot frame: if seeded witness slots agree with `ws`, they
    still agree after materializing a freshened body whose writes stay below
    `witnessBase`. -/
theorem materializeConstrainBody_slot_frame
    (witnessBase : Nat) (m : Module n F) (i : Fin n) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F) (env : LocalEnv F)
    (objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh stmts ≤ witnessBase)
    (pos : StructIR.VarId) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
      (encodeWitnessPos witnessBase pos) = ws pos := by
  have hv : localCeilConstrainBody m i runFresh stmts ≤ encodeWitnessPos witnessBase pos := by
    exact le_trans hCeil (by simp [encodeWitnessPos])
  calc
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
        (encodeWitnessPos witnessBase pos)
      = wt (encodeWitnessPos witnessBase pos) :=
          materializeConstrainBody_high_frame witnessBase m i freshBase wt env objEnv runFresh
            (encodeWitnessPos witnessBase pos) stmts hFit hv
    _ = ws pos := hSlots pos

/-- Shifted witness slots stay equal to seeded `StructIR` witness values after
    materializing a freshened body whose writes remain below `witnessBase`. -/
theorem materializeConstrainBody_slot_lift
    (witnessBase : Nat) (m : Module n F) (i : Fin n) (freshBase : Nat)
    (ws : StructIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh stmts ≤ witnessBase)
    (pos : StructIR.VarId) :
    materializeConstrainBody witnessBase m i (witnessSlotLift witnessBase ws) env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
      (encodeWitnessPos witnessBase pos) = ws pos := by
  refine materializeConstrainBody_slot_frame witnessBase m i freshBase
    (witnessSlotLift witnessBase ws) ws env objEnv runFresh stmts ?_ hFit hCeil pos
  intro pos'
  exact witnessSlotLift_encodeWitnessPos witnessBase ws pos'

 /-- Specialized forward witness for `compileProgram`: seed shifted witness slots
    from `ws`, seed renamed main params from canonical param coords, then
    materialize renamed main body locals. -/
def witnessCompile (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    FlatIR.Witness F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let numParams := (m.structs mainIdx).constrain.numParams
  let numMembers := (m.structs mainIdx).members.length
  let localBase := localBoundOfModule m
  let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
  let renamedBody := StructIRFreshen.renameBody ρ mainBody
  let initObjEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) (ρ 0) []
  let initNextFresh :=
    max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
  let wBase := witnessBase m
  let wtSeed := seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  materializeConstrainBody wBase m mainIdx wtSeed envSeed initObjEnv
    initNextFresh renamedBody

/-- `witnessCompile` preserves shifted witness-slot relation by construction. -/
theorem witnessCompile_rel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) :
    CorrectPass (F := F) (n := n) |>.witnessRel m ws (witnessCompile (n := n) m ws) := by
  intro pos
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let numParams := (m.structs mainIdx).constrain.numParams
  let numMembers := (m.structs mainIdx).members.length
  let localBase := localBoundOfModule m
  let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
  let renamedBody := StructIRFreshen.renameBody ρ mainBody
  let initObjEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) (ρ 0) []
  let initNextFresh :=
    max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
  let wBase := witnessBase m
  let wtSeed := seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  have hwBase_ge_params : localBase + numParams ≤ wBase := by
    have hInit : localBase + numParams ≤ initNextFresh := by simp [initNextFresh]
    have hCeil : initNextFresh ≤ wBase := by
      simp [wBase, witnessBase]
      exact localCeilConstrainBody_next_ge m mainIdx initNextFresh renamedBody
    exact le_trans hInit hCeil
  have hFit : localBase + StructIRFreshen.maxVarBody mainBody < initNextFresh := by
    simp [initNextFresh]
  have hCeil : localCeilConstrainBody m mainIdx initNextFresh mainBody ≤ wBase := by
    have hRename := localCeilConstrainBody_rename m mainIdx initNextFresh ρ mainBody
    have hwBase : wBase = localCeilConstrainBody m mainIdx initNextFresh renamedBody := by
      simp [wBase, witnessBase, mainIdx, mainBody, numParams, localBase, ρ, renamedBody,
        initNextFresh]
    rw [← hRename]
    simpa [hwBase, renamedBody]
  refine Eq.trans ?_ (materializeConstrainBody_slot_frame wBase m mainIdx localBase wtSeed ws envSeed
    initObjEnv initNextFresh mainBody ?_ hFit hCeil pos)
  · simp [witnessCompile, mainIdx, mainBody, numParams, numMembers, localBase, ρ,
      renamedBody, initObjEnv, initNextFresh, wBase, wtSeed, envSeed]
  · intro pos'
    have hsub : numParams ≤ encodeWitnessPos wBase pos' - localBase := by
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact le_trans hwBase_ge_params (by simp [encodeWitnessPos])
    have hnot : ¬ (localBase ≤ encodeWitnessPos wBase pos' ∧
        encodeWitnessPos wBase pos' - localBase < numParams) := by
      intro h
      exact Nat.not_lt_of_ge hsub h.2
    rw [show wtSeed (encodeWitnessPos wBase pos') =
        (if localBase ≤ encodeWitnessPos wBase pos' ∧
            encodeWitnessPos wBase pos' - localBase < numParams then
          ws (StructIR.paramCoord numMembers (encodeWitnessPos wBase pos' - localBase))
        else
          witnessSlotLift wBase ws (encodeWitnessPos wBase pos')) by rfl]
    rw [if_neg hnot]
    exact witnessSlotLift_encodeWitnessPos wBase ws pos'

theorem witnessCompile_main_param_stable (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (p : Nat)
    (hp : p < (m.main).constrain.numParams) :
    let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
    let mainBody := (m.structs mainIdx).constrain.body
    let numParams := (m.structs mainIdx).constrain.numParams
    let numMembers := (m.structs mainIdx).members.length
    let localBase := localBoundOfModule m
    let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
    let renamedBody := StructIRFreshen.renameBody ρ mainBody
    let initObjEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) (ρ 0) []
    let initNextFresh :=
      max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
    let wBase := witnessBase m
    let wtSeed := seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
    let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
    materializeConstrainBody wBase m mainIdx wtSeed envSeed initObjEnv initNextFresh renamedBody (ρ p) =
      wtSeed (ρ p) := by
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let numParams := (m.structs mainIdx).constrain.numParams
  let numMembers := (m.structs mainIdx).members.length
  let localBase := localBoundOfModule m
  let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
  let renamedBody := StructIRFreshen.renameBody ρ mainBody
  let initObjEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) (ρ 0) []
  let initNextFresh :=
    max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
  let wBase := witnessBase m
  let wtSeed := seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  have hp' : p < numParams := by simpa [Module.main, mainIdx, numParams] using hp
  have hx : (fun v => decide (v < numParams)) p = true := by simp [hp']
  have hlt : ρ p < initNextFresh := by
    have h1 : localBase + p < localBase + numParams := by omega
    exact lt_of_lt_of_le h1 (Nat.le_max_right _ _)
  simpa [mainIdx, mainBody, numParams, numMembers, localBase, ρ,
    renamedBody, initObjEnv, initNextFresh, wBase, wtSeed, envSeed] using
    materializeConstrainBody_init_frame wBase m mainIdx (fun v => decide (v < numParams)) wtSeed envSeed
      initObjEnv localBase initNextFresh p mainBody (m.all_ssa mainIdx) hx hlt

theorem witnessCompile_main_param_bindings_satisfy
    (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
    let numParams := (m.structs mainIdx).constrain.numParams
    let numMembers := (m.structs mainIdx).members.length
    let localBase := localBoundOfModule m
    let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
    let wBase := witnessBase m
    FlatIR.satisfies (witnessCompile m ws)
      (compileMainParamBindings (F := F) wBase numMembers numParams ρ) := by
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numParams := (m.structs mainIdx).constrain.numParams
  let numMembers := (m.structs mainIdx).members.length
  let localBase := localBoundOfModule m
  let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
  let wBase := witnessBase m
  apply compileMainParamBindings_satisfies_of_agree
  intro p hp
  have hstable := witnessCompile_main_param_stable (m := m) (ws := ws) p hp
  have hseed :
      (let wtSeed :=
        seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
       wtSeed (ρ p)) = ws (StructIR.paramCoord numMembers p) := by
    rw [show ρ p = localBase + p by simp [ρ, StructIRFreshen.freshMap]]
    rw [show (let wtSeed :=
          seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
        wtSeed (localBase + p)) =
        seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
          (localBase + p) by rfl]
    have hpos : localBase ≤ localBase + p ∧ localBase + p - localBase < numParams := by
      constructor
      · omega
      · simpa using hp
    rw [show seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
        (localBase + p) =
        (if localBase ≤ localBase + p ∧ localBase + p - localBase < numParams then
          ws (StructIR.paramCoord numMembers (localBase + p - localBase))
        else
          witnessSlotLift wBase ws (localBase + p)) by rfl]
    rw [if_pos hpos]
    simp
  calc
    witnessCompile m ws (ρ p)
      = ws (StructIR.paramCoord numMembers p) := by
          simpa [witnessCompile, mainIdx, numParams, numMembers, localBase, ρ, wBase] using
            Eq.trans hstable hseed
    _ = witnessCompile m ws (encodeParamVar wBase numMembers p) := by
          symm
          have hrel := witnessCompile_rel (m := m) (ws := ws) (pos := StructIR.paramCoord numMembers p)
          simpa [encodeParamVar] using hrel

lemma witness_env_agree_after_write
    (freshBase : Nat) (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (dest : Nat) (val : F)
    (hAgree : ∀ x, init x = true →
      wt (StructIRFreshen.freshMap freshBase x) = env (StructIRFreshen.freshMap freshBase x))
    (hDest : init dest = false) :
    ∀ x, (init x || x == dest) = true →
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
          (StructIRFreshen.freshMap freshBase x) =
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
          (StructIRFreshen.freshMap freshBase x) := by
  intro x hx
  simp only [Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with hinit | rfl
  · by_cases hxe : x = dest
    · subst hxe
      rw [hinit] at hDest
      contradiction
    · have hne : StructIRFreshen.freshMap freshBase x ≠ StructIRFreshen.freshMap freshBase dest := by
        intro h
        exact hxe (StructIRFreshen.freshMap_injective _ h)
      simp [LocalEnv.update, hne, hAgree _ hinit]
  · simp [LocalEnv.update]

theorem materializeConstrainBody_init_readback
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh x : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init stmts = true)
    (hInit : init x = true)
    (hAgree : wt (StructIRFreshen.freshMap freshBase x) = env (StructIRFreshen.freshMap freshBase x))
    (hlt : StructIRFreshen.freshMap freshBase x < runFresh) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
      (StructIRFreshen.freshMap freshBase x) =
        env (StructIRFreshen.freshMap freshBase x) := by
  calc
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)
        (StructIRFreshen.freshMap freshBase x)
      = wt (StructIRFreshen.freshMap freshBase x) :=
          materializeConstrainBody_init_frame witnessBase m i init wt env objEnv freshBase runFresh x
            stmts hSSA hInit hlt
    _ = env (StructIRFreshen.freshMap freshBase x) := hAgree

lemma isSSA_tail_of_dest {i : Fin n} {nm : Nat}
    (init : Nat → Bool) (stmt : ConstrainStmt n i F nm)
    (rest : List (ConstrainStmt n i F nm)) (dest : Nat)
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hd : stmt.dest = some dest) :
    StructIR.isSSA (fun x => init x || x == dest) rest = true := by
  simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
  cases hdest : stmt.dest with
  | none => simp [hd] at hdest
  | some d =>
      have hd' : d = dest := by simpa [hdest] using hd
      have htail : init d = false ∧ StructIR.isSSA (fun x => init x || x == d) rest = true := by
        simpa [hdest, Bool.and_eq_true] using hSSA.2
      subst hd'
      exact htail.2

lemma isSSA_tail_of_no_dest {i : Fin n} {nm : Nat}
    (init : Nat → Bool) (stmt : ConstrainStmt n i F nm)
    (rest : List (ConstrainStmt n i F nm))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hd : stmt.dest = none) :
    StructIR.isSSA init rest = true := by
  simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
  cases hdest : stmt.dest with
  | none => simpa [hdest] using hSSA.2
  | some d => simp [hd] at hdest

lemma isSSA_read_true_of_mem {i : Fin n} {nm : Nat}
    (init : Nat → Bool) (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (x : Nat)
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hx : x ∈ stmt.reads) :
    init x = true := by
  simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
  exact list_all_true_of_mem _ _ _ hSSA.1 hx

lemma isSSA_read_ne_dest {i : Fin n} {nm : Nat}
    (init : Nat → Bool) (stmt : ConstrainStmt n i F nm)
    (rest : List (ConstrainStmt n i F nm))
    (dest x : Nat)
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hd : stmt.dest = some dest)
    (hx : x ∈ stmt.reads) :
    x ≠ dest := by
  have hxInit : init x = true := isSSA_read_true_of_mem init stmt rest x hSSA hx
  have hdFalse : init dest = false :=
    isSSA_dest_not_init init (stmt :: rest) stmt dest hSSA (by simp) hd
  exact init_true_dest_ne hxInit hdFalse

theorem materializeConstrainBody_tail_readback_after_dest
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh dest x : Nat) (val : F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hd : stmt.dest = some dest)
    (hx : (init x || x == dest) = true)
    (hlt : StructIRFreshen.freshMap freshBase x < runFresh) :
    materializeConstrainBody witnessBase m i
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
      (env.update (StructIRFreshen.freshMap freshBase dest) val)
      objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
      (StructIRFreshen.freshMap freshBase x) =
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
          (StructIRFreshen.freshMap freshBase x) := by
  have hSSA' : StructIR.isSSA (fun y => init y || y == dest) rest = true :=
    isSSA_tail_of_dest init stmt rest dest hSSA hd
  have hDestFalse : init dest = false := by
    exact isSSA_dest_not_init init (stmt :: rest) stmt dest hSSA (by simp) hd
  have hAgree' :
      ∀ y, (init y || y == dest) = true →
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
            (StructIRFreshen.freshMap freshBase y) =
          (env.update (StructIRFreshen.freshMap freshBase dest) val)
            (StructIRFreshen.freshMap freshBase y) :=
    witness_env_agree_after_write freshBase init wt env dest val hAgree hDestFalse
  exact materializeConstrainBody_init_readback witnessBase m i (fun y => init y || y == dest)
    (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
    (env.update (StructIRFreshen.freshMap freshBase dest) val)
    objEnv freshBase runFresh x rest hSSA' hx (hAgree' x hx) hlt

theorem materializeConstrainBody_tail_readback_no_dest
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh x : Nat)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hd : stmt.dest = none)
    (hx : init x = true)
    (hlt : StructIRFreshen.freshMap freshBase x < runFresh) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
      (StructIRFreshen.freshMap freshBase x) =
        env (StructIRFreshen.freshMap freshBase x) := by
  have hSSA' : StructIR.isSSA init rest = true :=
    isSSA_tail_of_no_dest init stmt rest hSSA hd
  exact materializeConstrainBody_init_readback witnessBase m i init wt env objEnv freshBase runFresh x
    rest hSSA' hx (hAgree x hx) hlt

lemma runFresh_le_witnessBase_of_ceiling
    (m : Module n F) (i : Fin n) (runFresh witnessBase : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hCeil : localCeilConstrainBody m i runFresh stmts ≤ witnessBase) :
    runFresh ≤ witnessBase := by
  exact le_trans (localCeilConstrainBody_next_ge m i runFresh stmts) hCeil

lemma witness_slots_agree_after_write
    (witnessBase freshBase dest runFresh : Nat)
    (wt : FlatIR.Witness F) (w : StructIR.Witness F) (val : F)
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = w pos)
    (hDestLt : freshBase + dest < runFresh)
    (hRunFreshLe : runFresh ≤ witnessBase) :
    ∀ pos,
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (encodeWitnessPos witnessBase pos) = w pos := by
  intro pos
  calc
    (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (encodeWitnessPos witnessBase pos)
      = wt (encodeWitnessPos witnessBase pos) := by
          apply witness_update_high_frame
          · exact hDestLt
          · exact le_trans hRunFreshLe (by simp [encodeWitnessPos])
    _ = w pos := hSlots pos

theorem materialize_call_init_readback
    (witnessBase : Nat) (m : Module n F) (j : Fin n)
    (wt : FlatIR.Witness F) (env : LocalEnv F)
    (adjustedEnv : LocalEnv F) (adjustedObjEnv : ObjEnv)
    (freshBase runFresh reservedNextFresh x numParams : Nat)
    (args : List Nat)
    (calleeBody : List (ConstrainStmt n j F (m.structs j).members.length))
    (hAgree : wt (StructIRFreshen.freshMap freshBase x) = env (StructIRFreshen.freshMap freshBase x))
    (hRun : StructIRFreshen.freshMap freshBase x < runFresh)
    (hReserved : runFresh ≤ reservedNextFresh) :
    let wtParams : FlatIR.Witness F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match args[v - runFresh]? with
        | some arg => wt arg
        | none => 0
      else
        wt v
    materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv reservedNextFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody)
      (StructIRFreshen.freshMap freshBase x) =
        env (StructIRFreshen.freshMap freshBase x) := by
  let wtParams : FlatIR.Witness F := fun v =>
    if runFresh ≤ v ∧ v - runFresh < numParams then
      match args[v - runFresh]? with
      | some arg => wt arg
      | none => 0
    else
      wt v
  calc
    materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv reservedNextFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody)
        (StructIRFreshen.freshMap freshBase x)
      = wtParams (StructIRFreshen.freshMap freshBase x) :=
          materializeConstrainBody_fresh_frame witnessBase m j runFresh wtParams adjustedEnv
            adjustedObjEnv reservedNextFresh (StructIRFreshen.freshMap freshBase x)
            calleeBody hReserved hRun
    _ = wt (StructIRFreshen.freshMap freshBase x) := by
          simpa [wtParams] using
            materialize_call_param_seed_frame wt numParams runFresh
              (StructIRFreshen.freshMap freshBase x) args hRun
    _ = env (StructIRFreshen.freshMap freshBase x) := hAgree

theorem materialize_call_slot_readback
    (witnessBase : Nat) (m : Module n F) (j : Fin n)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (adjustedEnv : LocalEnv F) (adjustedObjEnv : ObjEnv)
    (runFresh reservedNextFresh : Nat)
    (calleeBody : List (ConstrainStmt n j F (m.structs j).members.length))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : runFresh + StructIRFreshen.maxVarBody calleeBody < reservedNextFresh)
    (hCeil : localCeilConstrainBody m j reservedNextFresh calleeBody ≤ witnessBase)
    (pos : StructIR.VarId) :
    materializeConstrainBody witnessBase m j wt adjustedEnv adjustedObjEnv reservedNextFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody)
      (encodeWitnessPos witnessBase pos) = ws pos := by
  exact materializeConstrainBody_slot_frame witnessBase m j runFresh wt ws adjustedEnv adjustedObjEnv
    reservedNextFresh calleeBody hSlots hFit hCeil pos

omit [Field F] in
lemma foldl_max_ge_seed (seed : Nat) (xs : List Nat) :
    seed ≤ xs.foldl max seed := by
  induction xs generalizing seed with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (Nat.le_max_left _ _) (ih _)

omit [Field F] in
lemma le_foldl_max_of_mem_seed (seed x : Nat) (xs : List Nat) (hx : x ∈ xs) :
    x ≤ xs.foldl max seed := by
  induction xs generalizing seed x with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · exact le_trans (Nat.le_max_right _ _) (foldl_max_ge_seed _ _)
      · exact ih _ _ hx

omit [Field F] in
lemma read_le_maxVarStmt {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (x : Nat) (hx : x ∈ stmt.reads) :
    x ≤ StructIRFreshen.maxVarStmt stmt := by
  cases stmt with
  | feltAdd dest src1 src2 =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl | rfl <;> simp
  | feltSub dest src1 src2 =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl | rfl <;> simp
  | feltMul dest src1 src2 =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl | rfl <;> simp
  | feltDiv dest src1 src2 =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl | rfl <;> simp
  | feltNeg dest src =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl <;> simp
  | feltConst dest c =>
      simp [ConstrainStmt.reads] at hx
  | readMember dest self member =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl <;> simp
  | constrainEq src1 src2 =>
      simp [ConstrainStmt.reads, StructIRFreshen.maxVarStmt] at hx ⊢
      rcases hx with rfl | rfl <;> simp
  | call target args =>
      exact le_foldl_max_of_mem_seed 0 x _ hx

omit [Field F] in
lemma read_lt_maxVarBody_cons {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (x : Nat) (hx : x ∈ stmt.reads) :
    x < StructIRFreshen.maxVarBody (stmt :: rest) + 1 := by
  have h1 : x ≤ StructIRFreshen.maxVarStmt stmt := read_le_maxVarStmt stmt x hx
  have h2 : StructIRFreshen.maxVarStmt stmt ≤ StructIRFreshen.maxVarBody (stmt :: rest) :=
    maxVarStmt_le_maxVarBody_cons stmt rest
  omega

omit [Field F] in
lemma dest_le_maxVarStmt {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (dest : Nat) (hd : stmt.dest = some dest) :
    dest ≤ StructIRFreshen.maxVarStmt stmt := by
  cases stmt with
  | feltAdd dest' src1 src2 => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | feltSub dest' src1 src2 => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | feltMul dest' src1 src2 => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | feltDiv dest' src1 src2 => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | feltNeg dest' src => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | feltConst dest' c => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | readMember dest' self member => cases hd; simp [ConstrainStmt.dest, StructIRFreshen.maxVarStmt]
  | constrainEq src1 src2 => cases hd
  | call target args => cases hd

omit [Field F] in
lemma dest_lt_maxVarBody_cons {i : Fin n} {nm : Nat}
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (dest : Nat) (hd : stmt.dest = some dest) :
    dest < StructIRFreshen.maxVarBody (stmt :: rest) + 1 := by
  have h1 : dest ≤ StructIRFreshen.maxVarStmt stmt := dest_le_maxVarStmt stmt dest hd
  have h2 : StructIRFreshen.maxVarStmt stmt ≤ StructIRFreshen.maxVarBody (stmt :: rest) :=
    maxVarStmt_le_maxVarBody_cons stmt rest
  omega

omit [Field F] in
lemma freshMap_read_lt_runFresh_of_fit_cons {i : Fin n} {nm : Nat}
    (freshBase runFresh x : Nat)
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hx : x ∈ stmt.reads) :
    StructIRFreshen.freshMap freshBase x < runFresh := by
  have hx' : x < StructIRFreshen.maxVarBody (stmt :: rest) + 1 :=
    read_lt_maxVarBody_cons stmt rest x hx
  simp [StructIRFreshen.freshMap]
  omega

omit [Field F] in
lemma freshMap_dest_lt_runFresh_of_fit_cons {i : Fin n} {nm : Nat}
    (freshBase runFresh dest : Nat)
    (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hd : stmt.dest = some dest) :
    StructIRFreshen.freshMap freshBase dest < runFresh := by
  have hd' : dest < StructIRFreshen.maxVarBody (stmt :: rest) + 1 :=
    dest_lt_maxVarBody_cons stmt rest dest hd
  simp [StructIRFreshen.freshMap]
  omega

omit [Field F] in
lemma freshMap_dest_lt_witnessBase_of_fit_cons {i : Fin n} {nm : Nat}
    (freshBase runFresh witnessBase dest : Nat)
    (m : Module n F) (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hRun : runFresh ≤ witnessBase)
    (hd : stmt.dest = some dest) :
    StructIRFreshen.freshMap freshBase dest < witnessBase := by
  exact lt_of_lt_of_le
    (freshMap_dest_lt_runFresh_of_fit_cons freshBase runFresh dest stmt rest hFit hd) hRun

theorem materializeConstrainBody_head_readback
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh x : Nat)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hx : x ∈ stmt.reads) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) (stmt :: rest))
      (StructIRFreshen.freshMap freshBase x) =
        env (StructIRFreshen.freshMap freshBase x) := by
  have hInit : init x = true := isSSA_read_true_of_mem init stmt rest x hSSA hx
  have hlt : StructIRFreshen.freshMap freshBase x < runFresh :=
    freshMap_read_lt_runFresh_of_fit_cons freshBase runFresh x stmt rest hFit hx
  exact materializeConstrainBody_init_readback witnessBase m i init wt env objEnv freshBase runFresh x
    (stmt :: rest) hSSA hInit (hAgree x hInit) hlt

theorem materialize_call_param_slot_readback
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.call target args :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hFit : freshBase + StructIRFreshen.maxVarBody (.call target args :: rest) < runFresh)
    (p : Nat)
    (hp : p < (m.structs ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩).constrain.numParams) :
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let numParams := (m.structs j).constrain.numParams
    let calleeBody := (m.structs j).constrain.body
    let adjustedObjEnv : ObjEnv := fun v =>
      if runFresh ≤ v then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => objEnv arg
        | none => []
      else
        []
    let wtParams : FlatIR.Witness F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => wt arg
        | none => 0
      else
        wt v
    let adjustedEnv : LocalEnv F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => env arg
        | none => 0
      else
        0
    let reservedNextFresh := max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
      (runFresh + numParams)
    let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
    let wtAfterCallee :=
      materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
        reservedNextFresh freshBody
    let nextFresh'' :=
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
    let wtFinal :=
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) (.call target args :: rest))
    wtFinal (StructIRFreshen.freshMap runFresh p) =
      match args[p]? with
      | some arg => env (StructIRFreshen.freshMap freshBase arg)
      | none => 0 := by
  let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
  let numParams := (m.structs j).constrain.numParams
  let calleeBody := (m.structs j).constrain.body
  let adjustedObjEnv : ObjEnv := fun v =>
    if runFresh ≤ v then
      match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
      | some arg => objEnv arg
      | none => []
    else
      []
  let wtParams : FlatIR.Witness F := fun v =>
    if runFresh ≤ v ∧ v - runFresh < numParams then
      match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
      | some arg => wt arg
      | none => 0
    else
      wt v
  let adjustedEnv : LocalEnv F := fun v =>
    if runFresh ≤ v ∧ v - runFresh < numParams then
      match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
      | some arg => env arg
      | none => 0
    else
      0
  let reservedNextFresh := max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
    (runFresh + numParams)
  let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
  let wtAfterCallee :=
    materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
      reservedNextFresh freshBody
  let nextFresh'' :=
    (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
  let wtFinal :=
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) (.call target args :: rest))
  have hp' : p < numParams := by simpa [numParams] using hp
  have hParamLt : runFresh + p < reservedNextFresh := by
    have : runFresh + p < runFresh + numParams := by omega
    exact lt_of_lt_of_le this (Nat.le_max_right _ _)
  have hReservedBody : reservedNextFresh ≤ nextFresh'' :=
    compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh freshBody
  have hRunTail : runFresh ≤ nextFresh'' := le_trans (by simp [reservedNextFresh]) hReservedBody
  have hFitRest : freshBase + StructIRFreshen.maxVarBody rest < runFresh := by
    have := maxVarBody_tail_le_cons (.call target args : ConstrainStmt n i F _) rest
    omega
  have hParamSeedAgree : wtParams (StructIRFreshen.freshMap runFresh p) = adjustedEnv (StructIRFreshen.freshMap runFresh p) := by
    have hcond : runFresh ≤ StructIRFreshen.freshMap runFresh p ∧
        StructIRFreshen.freshMap runFresh p - runFresh < numParams := by
      constructor
      · simp [StructIRFreshen.freshMap]
      · simpa [StructIRFreshen.freshMap] using hp'
    rw [show wtParams (StructIRFreshen.freshMap runFresh p) =
        (if runFresh ≤ StructIRFreshen.freshMap runFresh p ∧
            StructIRFreshen.freshMap runFresh p - runFresh < numParams then
          match Option.map (StructIRFreshen.freshMap freshBase)
              args[StructIRFreshen.freshMap runFresh p - runFresh]? with
          | some arg => wt arg
          | none => 0
        else
          wt (StructIRFreshen.freshMap runFresh p)) by rfl]
    rw [show adjustedEnv (StructIRFreshen.freshMap runFresh p) =
        (if runFresh ≤ StructIRFreshen.freshMap runFresh p ∧
            StructIRFreshen.freshMap runFresh p - runFresh < numParams then
          match Option.map (StructIRFreshen.freshMap freshBase)
              args[StructIRFreshen.freshMap runFresh p - runFresh]? with
          | some arg => env arg
          | none => 0
        else
          0) by rfl]
    rw [if_pos hcond, if_pos hcond]
    rw [show StructIRFreshen.freshMap runFresh p - runFresh = p by simp [StructIRFreshen.freshMap]]
    cases harg : args[p]? with
    | none => simp [harg]
    | some arg =>
        simp [harg]
        exact hAgree arg <|
          isSSA_read_true_of_mem init (.call target args) rest arg hSSA
            (by simpa [ConstrainStmt.reads] using List.mem_of_getElem? harg)
  have hParamAfterCallee : wtAfterCallee (StructIRFreshen.freshMap runFresh p) =
      adjustedEnv (StructIRFreshen.freshMap runFresh p) := by
    have hInit : (fun v => decide (v < numParams)) p = true := by simp [hp']
    have hlt : StructIRFreshen.freshMap runFresh p < reservedNextFresh := by
      simpa [StructIRFreshen.freshMap] using hParamLt
    simpa [wtAfterCallee, freshBody] using
      materializeConstrainBody_init_readback witnessBase m j (fun v => decide (v < numParams)) wtParams
        adjustedEnv adjustedObjEnv runFresh reservedNextFresh p calleeBody (m.all_ssa j)
        hInit hParamSeedAgree hlt
  have hCallEq :
      wtFinal (StructIRFreshen.freshMap runFresh p) =
        materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap runFresh p) := by
    have h := congrArg (fun w => w (StructIRFreshen.freshMap runFresh p))
      (materializeConstrainBody_call_rename_eq witnessBase m i wt env objEnv runFresh freshBase
        target args rest)
    simpa [j, numParams, calleeBody, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
      freshBody, wtAfterCallee, nextFresh'', wtFinal] using h
  have hMid :
      materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
        (StructIRFreshen.freshMap runFresh p) = wtAfterCallee (StructIRFreshen.freshMap runFresh p) := by
    apply materializeConstrainBody_middle_frame witnessBase m i freshBase wtAfterCallee env objEnv
      runFresh nextFresh'' (StructIRFreshen.freshMap runFresh p) rest
    · exact hFitRest
    · exact hRunTail
    · simp [StructIRFreshen.freshMap]
    · exact lt_of_lt_of_le hParamLt hReservedBody
  calc
    wtFinal (StructIRFreshen.freshMap runFresh p)
      = materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap runFresh p) := hCallEq
    _ = wtAfterCallee (StructIRFreshen.freshMap runFresh p) := hMid
    _ = adjustedEnv (StructIRFreshen.freshMap runFresh p) := hParamAfterCallee
    _ = match args[p]? with
        | some arg => env (StructIRFreshen.freshMap freshBase arg)
        | none => 0 := by
          rw [show adjustedEnv (StructIRFreshen.freshMap runFresh p) =
              (if runFresh ≤ StructIRFreshen.freshMap runFresh p ∧
                  StructIRFreshen.freshMap runFresh p - runFresh < numParams then
                match Option.map (StructIRFreshen.freshMap freshBase)
                    args[StructIRFreshen.freshMap runFresh p - runFresh]? with
                | some arg => env arg
                | none => 0
              else
                0) by rfl]
          have hcond : runFresh ≤ StructIRFreshen.freshMap runFresh p ∧
              StructIRFreshen.freshMap runFresh p - runFresh < numParams := by
            constructor
            · simp [StructIRFreshen.freshMap]
            · simpa [StructIRFreshen.freshMap] using hp'
          rw [if_pos hcond]
          rw [show StructIRFreshen.freshMap runFresh p - runFresh = p by simp [StructIRFreshen.freshMap]]
          cases harg : args[p]? <;> simp [harg]

theorem materialize_call_param_binds_satisfy
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (ws : StructIR.Witness F)
    (target : Fin i) (args : List Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.call target args :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hFit : freshBase + StructIRFreshen.maxVarBody (.call target args :: rest) < runFresh) :
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let numParams := (m.structs j).constrain.numParams
    let wtFinal :=
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) (.call target args :: rest))
    FlatIR.satisfies wtFinal
      (compileParamBindings (F := F) numParams (args.map (StructIRFreshen.freshMap freshBase))
        (StructIRFreshen.freshMap runFresh)) := by
  let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
  let numParams := (m.structs j).constrain.numParams
  let wtFinal :=
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) (.call target args :: rest))
  apply compileParamBindings_satisfies_of_agree
  intro p hp
  have hLeft := materialize_call_param_slot_readback witnessBase m i init freshBase wt env objEnv runFresh
    target args rest hSSA hAgree hFit p (by simpa [numParams] using hp)
  cases harg : args[p]? with
  | none =>
      have hmap : (args.map (StructIRFreshen.freshMap freshBase))[p]? = none := by
        simp [harg]
      simpa [wtFinal, StructIRFreshen.freshMap, hmap, harg] using hLeft
  | some arg =>
      have hmap : (args.map (StructIRFreshen.freshMap freshBase))[p]? =
          some (StructIRFreshen.freshMap freshBase arg) := by
        simp [harg]
      have hRight :
          wtFinal (StructIRFreshen.freshMap freshBase arg) =
            env (StructIRFreshen.freshMap freshBase arg) := by
        simpa [wtFinal] using
          materializeConstrainBody_head_readback witnessBase m i init wt env objEnv freshBase runFresh arg
            (.call target args) rest hSSA hAgree hFit
            (by simpa [ConstrainStmt.reads] using List.mem_of_getElem? harg)
      calc
        wtFinal (StructIRFreshen.freshMap runFresh p)
          = env (StructIRFreshen.freshMap freshBase arg) := by simpa [harg] using hLeft
        _ = wtFinal (StructIRFreshen.freshMap freshBase arg) := by symm; exact hRight
        _ = match (args.map (StructIRFreshen.freshMap freshBase))[p]? with
            | some arg' => wtFinal arg'
            | none => 0 := by simp [hmap]

theorem materializeConstrainBody_slot_readback
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh (stmt :: rest) ≤ witnessBase)
    (pos : StructIR.VarId) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) (stmt :: rest))
      (encodeWitnessPos witnessBase pos) = ws pos := by
  exact materializeConstrainBody_slot_frame witnessBase m i freshBase wt ws env objEnv runFresh
    (stmt :: rest) hSlots hFit hCeil pos

theorem witness_slots_agree_after_head_write
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase runFresh dest : Nat) (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (val : F)
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh (stmt :: rest) ≤ witnessBase)
    (hd : stmt.dest = some dest) :
    ∀ pos,
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (encodeWitnessPos witnessBase pos) = ws pos := by
  have hRun : runFresh ≤ witnessBase :=
    runFresh_le_witnessBase_of_ceiling m i runFresh witnessBase (stmt :: rest) hCeil
  have hDestLt : StructIRFreshen.freshMap freshBase dest < witnessBase :=
    freshMap_dest_lt_witnessBase_of_fit_cons freshBase runFresh witnessBase dest m stmt rest hFit hRun hd
  have hDestLt' : freshBase + dest < runFresh := by
    simpa [StructIRFreshen.freshMap] using
      freshMap_dest_lt_runFresh_of_fit_cons freshBase runFresh dest stmt rest hFit hd
  exact witness_slots_agree_after_write witnessBase freshBase dest runFresh wt ws val hSlots hDestLt' hRun

theorem materializeConstrainBody_head_dest_after_write
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh dest : Nat) (val : F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hd : stmt.dest = some dest)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh) :
    materializeConstrainBody witnessBase m i
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
      (env.update (StructIRFreshen.freshMap freshBase dest) val)
      objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
      (StructIRFreshen.freshMap freshBase dest) = val := by
  have hlt : StructIRFreshen.freshMap freshBase dest < runFresh :=
    freshMap_dest_lt_runFresh_of_fit_cons freshBase runFresh dest stmt rest hFit hd
  have hx : (init dest || dest == dest) = true := by simp
  simpa [LocalEnv.update] using
    materializeConstrainBody_tail_readback_after_dest witnessBase m i init wt env objEnv freshBase
      runFresh dest dest val stmt rest hSSA hAgree hd hx hlt

theorem materializeConstrainBody_head_read_after_write
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (freshBase runFresh dest x : Nat) (val : F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hd : stmt.dest = some dest)
    (hxread : x ∈ stmt.reads)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh) :
    materializeConstrainBody witnessBase m i
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
      (env.update (StructIRFreshen.freshMap freshBase dest) val)
      objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
      (StructIRFreshen.freshMap freshBase x) =
        (if x = dest then val else env (StructIRFreshen.freshMap freshBase x)) := by
  have hx : (init x || x == dest) = true := by
    have hinit : init x = true := isSSA_read_true_of_mem init stmt rest x hSSA hxread
    simp [hinit]
  have hlt : StructIRFreshen.freshMap freshBase x < runFresh :=
    freshMap_read_lt_runFresh_of_fit_cons freshBase runFresh x stmt rest hFit hxread
  have htail :=
    materializeConstrainBody_tail_readback_after_dest witnessBase m i init wt env objEnv freshBase
      runFresh dest x val stmt rest hSSA hAgree hd hx hlt
  by_cases hxd : x = dest
  · subst hxd
    simpa [LocalEnv.update] using htail
  · have hne : StructIRFreshen.freshMap freshBase x ≠ StructIRFreshen.freshMap freshBase dest := by
      intro h
      exact hxd (StructIRFreshen.freshMap_injective _ h)
    simpa [LocalEnv.update, hxd, hne] using htail

theorem materializeConstrainBody_tail_slot_after_write
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase runFresh dest : Nat) (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (val : F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (hd : stmt.dest = some dest)
    (hCeilCons : localCeilConstrainBody m i runFresh (stmt :: rest) ≤ witnessBase)
    (pos : StructIR.VarId) :
    materializeConstrainBody witnessBase m i
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
      (env.update (StructIRFreshen.freshMap freshBase dest) val)
      objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
      (encodeWitnessPos witnessBase pos) = ws pos := by
  have hFitRest : freshBase + StructIRFreshen.maxVarBody rest < runFresh := by
    have := maxVarBody_tail_le_cons stmt rest
    omega
  have hSlots' : ∀ pos, (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
      (encodeWitnessPos witnessBase pos) = ws pos :=
    witness_slots_agree_after_head_write witnessBase m i freshBase runFresh dest wt ws stmt rest val
      hSlots hFit hCeilCons hd
  exact materializeConstrainBody_slot_frame witnessBase m i freshBase
    (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v) ws
    (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv runFresh rest hSlots' hFitRest hCeilRest pos

def BodySatCtx
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) : Prop :=
  StructIR.isSSA init stmts = true ∧
    (∀ y, init y = true → wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y)) ∧
    (∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos) ∧
    freshBase + StructIRFreshen.maxVarBody stmts < runFresh ∧
    localCeilConstrainBody m i runFresh stmts ≤ witnessBase ∧
    (∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh)

lemma bodySatCtx.mk
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init stmts = true)
    (hAgree : ∀ y, init y = true → wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh stmts ≤ witnessBase)
    (hInitBound : ∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh) :
    BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts :=
  ⟨hSSA, hAgree, hSlots, hFit, hCeil, hInitBound⟩

lemma bodySatCtx.ssa
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    StructIR.isSSA init stmts = true := h.1

lemma bodySatCtx.agree
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    ∀ y, init y = true → wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y) := h.2.1

lemma bodySatCtx.slots
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos := h.2.2.1

lemma bodySatCtx.fit
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    freshBase + StructIRFreshen.maxVarBody stmts < runFresh := h.2.2.2.1

lemma bodySatCtx.ceil
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    localCeilConstrainBody m i runFresh stmts ≤ witnessBase := h.2.2.2.2.1

lemma bodySatCtx.initBound
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    ∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh := h.2.2.2.2.2

theorem body_satisfies_tail_ctx_after_dest
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh dest : Nat) (val : F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (stmt :: rest) ≤ witnessBase)
    (hNoCall : ∀ target args, stmt ≠ .call target args)
    (hd : stmt.dest = some dest)
    (hInitBound : ∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh) :
    BodySatCtx witnessBase m i (fun y => init y || y == dest) freshBase
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v) ws
      (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv runFresh rest := by
  refine bodySatCtx.mk witnessBase m i (fun y => init y || y == dest) freshBase
    (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v) ws
    (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv runFresh rest ?_ ?_ ?_ ?_ ?_ ?_
  · exact isSSA_tail_of_dest init stmt rest dest hSSA hd
  · have hDestFalse : init dest = false :=
      isSSA_dest_not_init init (stmt :: rest) stmt dest hSSA (by simp) hd
    exact witness_env_agree_after_write freshBase init wt env dest val hAgree hDestFalse
  · exact witness_slots_agree_after_head_write witnessBase m i freshBase runFresh dest wt ws stmt rest val
      hSlots hFit hCeilCons hd
  · have := maxVarBody_tail_le_cons stmt rest
    omega
  · exact localCeilConstrainBody_noncall_tail_le m runFresh witnessBase stmt rest hNoCall hCeilCons
  · intro y hy
    simp only [Bool.or_eq_true, beq_iff_eq] at hy
    rcases hy with hy | heq
    · exact hInitBound y hy
    · rw [heq]
      have hle := dest_lt_maxVarBody_cons stmt rest dest hd
      simp [StructIRFreshen.freshMap]; omega

theorem body_satisfies_tail_ctx_no_dest
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (stmt :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (stmt :: rest) ≤ witnessBase)
    (hNoCall : ∀ target args, stmt ≠ .call target args)
    (hd : stmt.dest = none)
    (hInitBound : ∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh) :
    BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh rest := by
  refine bodySatCtx.mk witnessBase m i init freshBase wt ws env objEnv runFresh rest ?_ hAgree hSlots ?_ ?_ hInitBound
  · exact isSSA_tail_of_no_dest init stmt rest hSSA hd
  · have := maxVarBody_tail_le_cons stmt rest
    omega
  · exact localCeilConstrainBody_noncall_tail_le m runFresh witnessBase stmt rest hNoCall hCeilCons

theorem bodySatCtx_after_dest_noncall
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh dest : Nat) (val : F)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh (stmt :: rest))
    (hNoCall : ∀ target args, stmt ≠ .call target args)
    (hd : stmt.dest = some dest) :
    BodySatCtx witnessBase m i (fun y => init y || y == dest) freshBase
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v) ws
      (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv runFresh rest := by
  exact body_satisfies_tail_ctx_after_dest witnessBase m i init freshBase wt ws env objEnv runFresh
    dest val stmt rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx) hNoCall hd (bodySatCtx.initBound hctx)

theorem bodySatCtx_after_no_dest_noncall
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (stmt : ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh (stmt :: rest))
    (hNoCall : ∀ target args, stmt ≠ .call target args)
    (hd : stmt.dest = none) :
    BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh rest := by
  exact body_satisfies_tail_ctx_no_dest witnessBase m i init freshBase wt ws env objEnv runFresh
    stmt rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx) hNoCall hd (bodySatCtx.initBound hctx)

theorem materialize_compile_constrainEq_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hEq :
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src2)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.constrainEq src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.constrainEq src1 src2 :: rest))).1 := by
  rw [materializeConstrainBody_constrainEq_rename_eq]
  intro instr hmem
  simp [compileConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt] at hmem
  rcases hmem with rfl | hmem
  · simp [FlatIR.satisfiesInstr, hEq]
  · exact ih instr hmem

theorem materialize_compile_feltAdd_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2))
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src2) =
        env (StructIRFreshen.freshMap freshBase src2)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltAdd dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltAdd dest src1 src2 :: rest))).1 := by
  rw [materializeConstrainBody_feltAdd_rename_eq]
  intro instr hmem
  simp [compileConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt] at hmem
  rcases hmem with rfl | hmem
  · simp [FlatIR.satisfiesInstr, hDest, hSrc1, hSrc2]
  · exact ih instr hmem

theorem materialize_compile_feltSub_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2))
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src2) =
        env (StructIRFreshen.freshMap freshBase src2)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltSub dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltSub dest src1 src2 :: rest))).1 := by
  simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
    materializeConstrainBody]
  intro instr hmem
  simp [compileConstrainBody] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
          env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc1' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) =
          env (StructIRFreshen.freshMap freshBase src1) := by
        simpa [StructIRFreshen.renameBody] using hSrc1
    have hSrc2' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src2) =
          env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hSrc2
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
          (StructIRFreshen.freshMap freshBase dest)
        = env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2) := hDest'
      _ = materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) -
          materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src2) := by rw [hSrc1', hSrc2']
  · exact ih instr hmem

theorem materialize_compile_feltMul_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2))
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src2) =
        env (StructIRFreshen.freshMap freshBase src2)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltMul dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltMul dest src1 src2 :: rest))).1 := by
  simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
    materializeConstrainBody]
  intro instr hmem
  simp [compileConstrainBody] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
          env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc1' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) =
          env (StructIRFreshen.freshMap freshBase src1) := by
        simpa [StructIRFreshen.renameBody] using hSrc1
    have hSrc2' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src2) =
          env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hSrc2
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
          (StructIRFreshen.freshMap freshBase dest)
        = env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2) := hDest'
      _ = materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) *
          materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src2) := by rw [hSrc1', hSrc2']
  · exact ih instr hmem

theorem materialize_compile_feltDiv_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) *
            (env (StructIRFreshen.freshMap freshBase src2))⁻¹
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) *
            (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hSrc2Nz : env (StructIRFreshen.freshMap freshBase src2) ≠ 0)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) *
          (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src2) =
        env (StructIRFreshen.freshMap freshBase src2)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltDiv dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltDiv dest src1 src2 :: rest))).1 := by
  simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
    materializeConstrainBody]
  intro instr hmem
  simp [compileConstrainBody] at hmem
  rcases hmem with rfl | hmem
  · constructor
    · have hSrc2' :
          materializeConstrainBody witnessBase m i
              (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹
               else wt v)
              (env.update (StructIRFreshen.freshMap freshBase dest)
                (env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
              objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
              (StructIRFreshen.freshMap freshBase src2) =
            env (StructIRFreshen.freshMap freshBase src2) := by
          simpa [StructIRFreshen.renameBody] using hSrc2
      rw [hSrc2']
      exact hSrc2Nz
    · have hDest' :
          materializeConstrainBody witnessBase m i
              (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹
               else wt v)
              (env.update (StructIRFreshen.freshMap freshBase dest)
                (env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
              objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
              (StructIRFreshen.freshMap freshBase dest) =
            env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹ := by
          simpa [StructIRFreshen.renameBody] using hDest
      have hSrc1' :
          materializeConstrainBody witnessBase m i
              (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹
               else wt v)
              (env.update (StructIRFreshen.freshMap freshBase dest)
                (env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
              objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
              (StructIRFreshen.freshMap freshBase src1) =
            env (StructIRFreshen.freshMap freshBase src1) := by
          simpa [StructIRFreshen.renameBody] using hSrc1
      have hSrc2' :
          materializeConstrainBody witnessBase m i
              (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹
               else wt v)
              (env.update (StructIRFreshen.freshMap freshBase dest)
                (env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
              objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
              (StructIRFreshen.freshMap freshBase src2) =
            env (StructIRFreshen.freshMap freshBase src2) := by
          simpa [StructIRFreshen.renameBody] using hSrc2
      exact calc
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) *
                (env (StructIRFreshen.freshMap freshBase src2))⁻¹
             else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (env (StructIRFreshen.freshMap freshBase src1) *
                (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest)
          = env (StructIRFreshen.freshMap freshBase src1) *
              (env (StructIRFreshen.freshMap freshBase src2))⁻¹ := hDest'
        _ = materializeConstrainBody witnessBase m i
              (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹
               else wt v)
              (env.update (StructIRFreshen.freshMap freshBase dest)
                (env (StructIRFreshen.freshMap freshBase src1) *
                  (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
              objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
              (StructIRFreshen.freshMap freshBase src1) *
            (materializeConstrainBody witnessBase m i
                (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                  env (StructIRFreshen.freshMap freshBase src1) *
                    (env (StructIRFreshen.freshMap freshBase src2))⁻¹
                 else wt v)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) *
                    (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
                objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
                (StructIRFreshen.freshMap freshBase src2))⁻¹ := by rw [hSrc1', hSrc2']
  · exact ih instr hmem

theorem materialize_compile_feltNeg_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest src : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (-(env (StructIRFreshen.freshMap freshBase src))))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (-(env (StructIRFreshen.freshMap freshBase src))))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        -(env (StructIRFreshen.freshMap freshBase src)))
    (hSrc :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (-(env (StructIRFreshen.freshMap freshBase src))))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src) =
        env (StructIRFreshen.freshMap freshBase src)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltNeg dest src :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltNeg dest src :: rest))).1 := by
  simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
    materializeConstrainBody]
  intro instr hmem
  simp [compileConstrainBody] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (-(env (StructIRFreshen.freshMap freshBase src))))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
          -(env (StructIRFreshen.freshMap freshBase src)) := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (-(env (StructIRFreshen.freshMap freshBase src))))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src) =
          env (StructIRFreshen.freshMap freshBase src) := by
        simpa [StructIRFreshen.renameBody] using hSrc
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (-(env (StructIRFreshen.freshMap freshBase src))))
          objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
          (StructIRFreshen.freshMap freshBase dest)
        = -(env (StructIRFreshen.freshMap freshBase src)) := hDest'
      _ = -materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (-(env (StructIRFreshen.freshMap freshBase src))))
            objEnv runFresh (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src) := by rw [hSrc']
  · exact ih instr hmem

theorem materialize_compile_feltConst_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest : Nat) (c : F)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then c else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest) c)
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then c else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest) c)
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) = c) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltConst dest c :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltConst dest c :: rest))).1 := by
  simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
    materializeConstrainBody]
  intro instr hmem
  simp [compileConstrainBody] at hmem
  rcases hmem with rfl | hmem
  · simpa [StructIRFreshen.renameBody, FlatIR.satisfiesInstr] using hDest
  · exact ih instr hmem

theorem materialize_compile_readMember_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
            member.val)))
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
          (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
          (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
              member.val)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
              member.val)))
          (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
            (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
          runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val))
    (hWitness :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
              member.val)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self))
              member.val)))
          (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
            (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
          runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val) =
        wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest))).1 := by
  rw [materializeConstrainBody_readMember_rename_eq]
  intro instr hmem
  simp [compileConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt] at hmem
  rcases hmem with rfl | hmem
  · simp [FlatIR.satisfiesInstr, hDest, hWitness]
  · exact ih instr hmem

theorem materialize_step_constrainEq_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.constrainEq src1 src2 :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.constrainEq src1 src2 :: rest) < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh (.constrainEq src1 src2 :: rest) ≤ witnessBase)
    (hEq : env (StructIRFreshen.freshMap freshBase src1) = env (StructIRFreshen.freshMap freshBase src2))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.constrainEq src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.constrainEq src1 src2 :: rest))).1 := by
  have hEq1 := materializeConstrainBody_head_readback witnessBase m i init wt env objEnv freshBase runFresh
    src1 (.constrainEq src1 src2) rest hSSA hAgree hFit (by simp [ConstrainStmt.reads])
  have hEq2 := materializeConstrainBody_head_readback witnessBase m i init wt env objEnv freshBase runFresh
    src2 (.constrainEq src1 src2) rest hSSA hAgree hFit (by simp [ConstrainStmt.reads])
  have hTailEq :
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src2) := by
    calc
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1)
        = env (StructIRFreshen.freshMap freshBase src1) := by
            simpa [ConstrainStmt.dest] using
              materializeConstrainBody_tail_readback_no_dest witnessBase m i init wt env objEnv freshBase
                runFresh src1 (.constrainEq src1 src2) rest hSSA hAgree rfl
                (isSSA_read_true_of_mem init (.constrainEq src1 src2) rest src1 hSSA (by simp [ConstrainStmt.reads]))
                (freshMap_read_lt_runFresh_of_fit_cons freshBase runFresh src1 (.constrainEq src1 src2)
                  rest hFit (by simp [ConstrainStmt.reads]))
      _ = env (StructIRFreshen.freshMap freshBase src2) := hEq
      _ = materializeConstrainBody witnessBase m i wt env objEnv runFresh
            (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
            (StructIRFreshen.freshMap freshBase src2) := by
            symm
            simpa [ConstrainStmt.dest] using
              materializeConstrainBody_tail_readback_no_dest witnessBase m i init wt env objEnv freshBase
                runFresh src2 (.constrainEq src1 src2) rest hSSA hAgree rfl
                (isSSA_read_true_of_mem init (.constrainEq src1 src2) rest src2 hSSA (by simp [ConstrainStmt.reads]))
                (freshMap_read_lt_runFresh_of_fit_cons freshBase runFresh src2 (.constrainEq src1 src2)
                  rest hFit (by simp [ConstrainStmt.reads]))
  exact materialize_compile_constrainEq_satisfies witnessBase m i freshBase wt env objEnv runFresh
    src1 src2 rest ih hTailEq

theorem materialize_step_feltAdd_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltAdd dest src1 src2 :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltAdd dest src1 src2 :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.feltAdd dest src1 src2 :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltAdd dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltAdd dest src1 src2 :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltAdd dest src1 src2
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src1 (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src2 (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc1_ne : src1 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src1 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  have hsrc2_ne : src2 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src2 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltAdd_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src1 src2 rest ih hDest (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)

theorem materialize_step_feltSub_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltSub dest src1 src2 :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltSub dest src1 src2 :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.feltSub dest src1 src2 :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltSub dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltSub dest src1 src2 :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltSub dest src1 src2
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src1 (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src2 (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc1_ne : src1 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src1 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  have hsrc2_ne : src2 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src2 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltSub_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src1 src2 rest ih hDest (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)

theorem materialize_step_feltMul_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltMul dest src1 src2 :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltMul dest src1 src2 :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.feltMul dest src1 src2 :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltMul dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltMul dest src1 src2 :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltMul dest src1 src2
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src1 (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src2 (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2))
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc1_ne : src1 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src1 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  have hsrc2_ne : src2 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src2 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltMul_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src1 src2 rest ih hDest (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)

theorem materialize_step_feltNeg_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltNeg dest src :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltNeg dest src :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.feltNeg dest src :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (-(env (StructIRFreshen.freshMap freshBase src))))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltNeg dest src :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltNeg dest src :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltNeg dest src
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest (-(env (StructIRFreshen.freshMap freshBase src))) stmt rest hSSA hAgree hd hFit
  have hSrc := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src (-(env (StructIRFreshen.freshMap freshBase src))) stmt rest hSSA hAgree hd
    (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc_ne : src ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltNeg_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src rest ih hDest (by simpa [hsrc_ne] using hSrc)

theorem materialize_step_feltConst_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest : Nat) (c : F)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltConst dest c :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltConst dest c :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.feltConst dest c :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then c else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest) c)
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltConst dest c :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltConst dest c :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltConst dest c
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest c stmt rest hSSA hAgree hd hFit
  exact materialize_compile_feltConst_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest c rest ih hDest

theorem materialize_step_feltDiv_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltDiv dest src1 src2 :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltDiv dest src1 src2 :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.feltDiv dest src1 src2 :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (hSrc2Nz : env (StructIRFreshen.freshMap freshBase src2) ≠ 0)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltDiv dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltDiv dest src1 src2 :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltDiv dest src1 src2
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest (env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src1 (env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env objEnv freshBase
    runFresh dest src2 (env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc1_ne : src1 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src1 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  have hsrc2_ne : src2 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src2 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltDiv_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src1 src2 rest ih hSrc2Nz hDest (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)

theorem materialize_step_readMember_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.readMember dest self member :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.readMember dest self member :: rest) < runFresh)
    (hCeilCons : localCeilConstrainBody m i runFresh (.readMember dest self member :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
          (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
          (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .readMember dest self member
  let val := wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
  let objEnvStep := StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
    (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val])
  have hd : stmt.dest = some dest := by rfl
  have hSSA' : StructIR.isSSA (fun x => init x || x == dest) rest = true :=
    isSSA_tail_of_dest init stmt rest dest hSSA hd
  have hDestFalse : init dest = false :=
    isSSA_dest_not_init init (stmt :: rest) stmt dest hSSA (by simp) hd
  have hAgree' :
      ∀ y, (init y || y == dest) = true →
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
            (StructIRFreshen.freshMap freshBase y) =
          (env.update (StructIRFreshen.freshMap freshBase dest) val)
            (StructIRFreshen.freshMap freshBase y) :=
    witness_env_agree_after_write freshBase init wt env dest val hAgree hDestFalse
  have hDestLt : StructIRFreshen.freshMap freshBase dest < runFresh :=
    freshMap_dest_lt_runFresh_of_fit_cons freshBase runFresh dest stmt rest hFit hd
  have hDest :
      materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        objEnvStep runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
        (StructIRFreshen.freshMap freshBase dest) = val := by
    have hx : ((init dest || dest == dest)) = true := by simp
    simpa [LocalEnv.update] using
      materializeConstrainBody_init_readback witnessBase m i (fun x => init x || x == dest)
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        objEnvStep freshBase runFresh dest rest hSSA' hx (hAgree' dest hx) hDestLt
  have hWitness :
      materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest) val)
        objEnvStep runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
        (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val) = val := by
    let pos : StructIR.VarId := (objEnv (StructIRFreshen.freshMap freshBase self), member.val)
    have hslot :
        materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest) val)
          objEnvStep runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (encodeWitnessPos witnessBase pos) = ws pos :=
      materializeConstrainBody_tail_slot_after_write witnessBase m i freshBase runFresh dest wt ws env
        objEnvStep val stmt rest hSlots hFit hCeilRest hd hCeilCons pos
    calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest) val)
          objEnvStep runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
        = ws pos := by simpa [pos, encodeWitnessVar]
      _ = val := by simpa [pos, val] using (hSlots pos).symm
  exact materialize_compile_readMember_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest self member rest ih hDest hWitness

theorem bodySatCtx_constrainEq_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.constrainEq src1 src2 :: rest))
    (hEq : env (StructIRFreshen.freshMap freshBase src1) = env (StructIRFreshen.freshMap freshBase src2))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.constrainEq src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.constrainEq src1 src2 :: rest))).1 := by
  exact materialize_step_constrainEq_satisfies witnessBase m i init freshBase wt ws env objEnv
    runFresh src1 src2 rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx) hEq ih

theorem bodySatCtx_feltAdd_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltAdd dest src1 src2 :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltAdd dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltAdd dest src1 src2 :: rest))).1 := by
  exact materialize_step_feltAdd_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest src1 src2 rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest (env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2))
      (.feltAdd dest src1 src2) rest hctx (by intro target args h; cases h) rfl))
    ih

theorem bodySatCtx_feltSub_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltSub dest src1 src2 :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltSub dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltSub dest src1 src2 :: rest))).1 := by
  exact materialize_step_feltSub_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest src1 src2 rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest (env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2))
      (.feltSub dest src1 src2) rest hctx (by intro target args h; cases h) rfl))
    ih

theorem bodySatCtx_feltMul_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltMul dest src1 src2 :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltMul dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltMul dest src1 src2 :: rest))).1 := by
  exact materialize_step_feltMul_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest src1 src2 rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest (env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2))
      (.feltMul dest src1 src2) rest hctx (by intro target args h; cases h) rfl))
    ih

theorem bodySatCtx_feltNeg_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltNeg dest src :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (-(env (StructIRFreshen.freshMap freshBase src))))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltNeg dest src :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltNeg dest src :: rest))).1 := by
  exact materialize_step_feltNeg_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest src rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest (-(env (StructIRFreshen.freshMap freshBase src)))
      (.feltNeg dest src) rest hctx (by intro target args h; cases h) rfl))
    ih

theorem bodySatCtx_feltConst_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest : Nat) (c : F)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltConst dest c :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then c else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest) c)
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltConst dest c :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltConst dest c :: rest))).1 := by
  exact materialize_step_feltConst_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest c rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest c (.feltConst dest c) rest hctx (by intro target args h; cases h) rfl))
    ih

theorem bodySatCtx_feltDiv_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltDiv dest src1 src2 :: rest))
    (hSrc2Nz : env (StructIRFreshen.freshMap freshBase src2) ≠ 0)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltDiv dest src1 src2 :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltDiv dest src1 src2 :: rest))).1 := by
  exact materialize_step_feltDiv_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest src1 src2 rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest (env (StructIRFreshen.freshMap freshBase src1) * (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
      (.feltDiv dest src1 src2) rest hctx (by intro target args h; cases h) rfl))
    hSrc2Nz ih

theorem bodySatCtx_readMember_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.readMember dest self member :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
          (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i
        (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
          (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
        runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest))).1 := by
  exact materialize_step_readMember_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest self member rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv runFresh
      dest (wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val))
      (.readMember dest self member) rest hctx (by intro target args h; cases h) rfl))
    ih

/-- Transfer `FlatIR.satisfies` between pointwise-agreeing witnesses. -/
theorem FlatIR_satisfies_of_eq (w1 w2 : FlatIR.Witness F) (prog : FlatIR.Program F)
    (h : ∀ instr ∈ prog, ∀ v ∈ FlatIR.instrVars instr, w1 v = w2 v)
    (hSat : FlatIR.satisfies w2 prog) :
    FlatIR.satisfies w1 prog := by
  intro instr hInstr
  exact (FlatIR.satisfiesInstr_congr (h instr hInstr)).mpr (hSat instr hInstr)

/-- The `call` case for forward body satisfaction.

    Given `BodySatCtx` for `call target args :: rest`, callee evaluation,
    callee forward satisfaction (via smaller struct index), and rest forward
    satisfaction (via smaller list), produces `FlatIR.satisfies` for the
    whole compiled `call :: rest`. -/
theorem bodySatCtx_call_callee_ctx
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (hSSA_all : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.call target args :: rest)) :
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let calleeBody := (m.structs j).constrain.body
    let numParams := (m.structs j).constrain.numParams
    let adjustedObjEnv : ObjEnv := fun v =>
      if runFresh ≤ v then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => objEnv arg
        | none => []
      else []
    let wtParams : FlatIR.Witness F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => wt arg
        | none => 0
      else wt v
    let adjustedEnv : LocalEnv F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => env arg
        | none => 0
      else 0
    let reservedNextFresh :=
      max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
        (runFresh + numParams)
    BodySatCtx witnessBase m j (fun v => decide (v < numParams)) runFresh wtParams ws
      adjustedEnv adjustedObjEnv reservedNextFresh calleeBody := by
  obtain ⟨hSSA, hAgree, hSlots, hFit, hCeil, hInitBound⟩ := hctx
  intro j calleeBody numParams adjustedObjEnv wtParams adjustedEnv reservedNextFresh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- SSA for callee
  · exact hSSA_all j
  -- agree: callee adjusted env agrees with wtParams on param slots
  · intro y hy
    simp only [decide_eq_true_eq] at hy
    have hcond :
        runFresh ≤ StructIRFreshen.freshMap runFresh y ∧
          StructIRFreshen.freshMap runFresh y - runFresh < numParams := by
      constructor
      · simp [StructIRFreshen.freshMap]
      · simpa [StructIRFreshen.freshMap] using hy
    rw [show wtParams (StructIRFreshen.freshMap runFresh y) =
        (if runFresh ≤ StructIRFreshen.freshMap runFresh y ∧
            StructIRFreshen.freshMap runFresh y - runFresh < numParams then
          match Option.map (StructIRFreshen.freshMap freshBase)
              args[StructIRFreshen.freshMap runFresh y - runFresh]? with
          | some arg => wt arg
          | none => 0
        else wt (StructIRFreshen.freshMap runFresh y)) by rfl]
    rw [show adjustedEnv (StructIRFreshen.freshMap runFresh y) =
        (if runFresh ≤ StructIRFreshen.freshMap runFresh y ∧
            StructIRFreshen.freshMap runFresh y - runFresh < numParams then
          match Option.map (StructIRFreshen.freshMap freshBase)
              args[StructIRFreshen.freshMap runFresh y - runFresh]? with
          | some arg => env arg
          | none => 0
        else 0) by rfl]
    rw [if_pos hcond, if_pos hcond]
    rw [show StructIRFreshen.freshMap runFresh y - runFresh = y by
      simp [StructIRFreshen.freshMap]]
    cases h : args[y]? with
    | none => simp [h]
    | some arg =>
        simpa [h] using
          hAgree arg <|
            isSSA_read_true_of_mem init (.call target args) rest arg hSSA
              (by simpa [ConstrainStmt.reads] using List.mem_of_getElem? h)
  -- slots: witness slots pass through wtParams unchanged
  · intro pos
    simp only [wtParams]
    have hCeil' : localCeilConstrainBody m i
        (localCeilConstrainBody m j reservedNextFresh
          (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest ≤ witnessBase := by
      simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody, reservedNextFresh] using hCeil
    have hReservedLeWitness : reservedNextFresh ≤ witnessBase := by
      exact le_trans
        (le_trans
          (by simpa [reservedNextFresh] using
            (le_max_right (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1)) (runFresh + numParams)))
          (localCeilConstrainBody_next_ge m j reservedNextFresh
            (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)))
        (le_trans
          (localCeilConstrainBody_next_ge m i
            (localCeilConstrainBody m j reservedNextFresh
              (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest)
          hCeil')
    have hCeilNum : runFresh + numParams ≤ witnessBase := by
      exact le_trans (le_max_right _ _) hReservedLeWitness
    have hlt : ¬ (runFresh ≤ encodeWitnessPos witnessBase pos ∧
        encodeWitnessPos witnessBase pos - runFresh < numParams) := by
      intro ⟨_, hlt⟩
      have hge : witnessBase ≤ encodeWitnessPos witnessBase pos := by
        simp [encodeWitnessPos]
      have hsub : numParams ≤ encodeWitnessPos witnessBase pos - runFresh := by
        omega
      exact Nat.not_lt_of_ge hsub hlt
    simp only [hlt, ite_false]
    exact hSlots pos
  -- fit: callee body fits below reservedNextFresh
  · simp only [reservedNextFresh, calleeBody]
    exact lt_max_of_lt_left (Nat.lt_succ_self _)
  -- ceil: callee localCeil ≤ witnessBase via call-case chain
  · have hCeil' : localCeilConstrainBody m i
        (localCeilConstrainBody m j reservedNextFresh
          (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest ≤ witnessBase := by
      simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody, reservedNextFresh] using hCeil
    have hCeilRenamed : localCeilConstrainBody m j reservedNextFresh
        (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody) ≤ witnessBase := by
      exact le_trans
        (localCeilConstrainBody_next_ge m i
          (localCeilConstrainBody m j reservedNextFresh
            (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest)
        hCeil'
    exact (localCeilConstrainBody_rename m j reservedNextFresh (fun v => runFresh + v) calleeBody) ▸
      hCeilRenamed
  -- initBound: y < numParams → runFresh + y < reservedNextFresh
  · intro y hy
    simp only [decide_eq_true_eq] at hy
    have hy' : runFresh + y < runFresh + numParams := Nat.add_lt_add_left hy runFresh
    exact Nat.lt_of_lt_of_le (by simpa [StructIRFreshen.freshMap] using hy') (le_max_right _ _)

theorem bodySatCtx_call_rest_ctx
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.call target args :: rest)) :
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let calleeBody := (m.structs j).constrain.body
    let numParams := (m.structs j).constrain.numParams
    let adjustedObjEnv : ObjEnv := fun v =>
      if runFresh ≤ v then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => objEnv arg
        | none => []
      else []
    let wtParams : FlatIR.Witness F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => wt arg
        | none => 0
      else wt v
    let adjustedEnv : LocalEnv F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => env arg
        | none => 0
      else 0
    let reservedNextFresh :=
      max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
        (runFresh + numParams)
    let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
    let wtAfterCallee :=
      materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
        reservedNextFresh freshBody
    let nextFresh'' :=
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
    BodySatCtx witnessBase m i init freshBase wtAfterCallee ws env objEnv nextFresh'' rest := by
  obtain ⟨hSSA, hAgree, hSlots, hFit, hCeil, hInitBound⟩ := hctx
  intro j calleeBody numParams adjustedObjEnv wtParams adjustedEnv reservedNextFresh freshBody
    wtAfterCallee nextFresh''
  have hReserved : runFresh ≤ reservedNextFresh := le_trans (Nat.le_add_right _ _) (le_max_left _ _)
  have hNextEq : nextFresh'' = localCeilConstrainBody m j reservedNextFresh freshBody := by
    simpa [nextFresh'', freshBody] using
      (compileConstrainBody_localCeil_eq witnessBase m j adjustedObjEnv reservedNextFresh freshBody)
  have hRunLeNext : runFresh ≤ nextFresh'' := by
    exact le_trans hReserved
      (compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh freshBody)
  have hCeil' : localCeilConstrainBody m i
      (localCeilConstrainBody m j reservedNextFresh freshBody) rest ≤ witnessBase := by
    simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody, reservedNextFresh,
      freshBody] using hCeil
  have hCeilFresh : localCeilConstrainBody m j reservedNextFresh freshBody ≤ witnessBase := by
    exact le_trans (localCeilConstrainBody_next_ge m i _ rest) hCeil'
  have hCeilCallee : localCeilConstrainBody m j reservedNextFresh calleeBody ≤ witnessBase := by
    rw [← localCeilConstrainBody_rename m j reservedNextFresh (fun v => runFresh + v) calleeBody]
    simpa [freshBody] using hCeilFresh
  have hFitCallee : runFresh + StructIRFreshen.maxVarBody calleeBody < reservedNextFresh := by
    simpa [reservedNextFresh] using (lt_max_of_lt_left (Nat.lt_succ_self _))
  have hReservedLeWitness : reservedNextFresh ≤ witnessBase := by
    exact le_trans
      (le_trans
        (by simpa [reservedNextFresh] using
          (le_max_right (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1)) (runFresh + numParams)))
        (localCeilConstrainBody_next_ge m j reservedNextFresh freshBody))
      hCeilFresh
  have hSlotsParams : ∀ pos, wtParams (encodeWitnessPos witnessBase pos) = ws pos := by
    intro pos
    simp only [wtParams]
    have hlt : ¬ (runFresh ≤ encodeWitnessPos witnessBase pos ∧
        encodeWitnessPos witnessBase pos - runFresh < numParams) := by
      intro ⟨_, hlt⟩
      have hsub : numParams ≤ encodeWitnessPos witnessBase pos - runFresh := by
        have hge : witnessBase ≤ encodeWitnessPos witnessBase pos := by simp [encodeWitnessPos]
        have hCeilNum : runFresh + numParams ≤ witnessBase := by
          exact le_trans (le_max_right _ _) hReservedLeWitness
        omega
      exact Nat.not_lt_of_ge hsub hlt
    simp only [hlt, ite_false]
    exact hSlots pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd :
        ((.call target args : ConstrainStmt n i F (m.structs i).members.length)).dest = none := by
      simp [ConstrainStmt.dest]
    exact isSSA_tail_of_no_dest init (.call target args) rest hSSA hd
  · intro y hy
    simpa [wtAfterCallee, freshBody, reservedNextFresh, wtParams, adjustedEnv] using
      (materialize_call_init_readback witnessBase m j wt env adjustedEnv adjustedObjEnv
        freshBase runFresh reservedNextFresh y numParams
        (args.map (StructIRFreshen.freshMap freshBase)) calleeBody
        (hAgree y hy) (hInitBound y hy) hReserved)
  · intro pos
    simpa [wtAfterCallee, freshBody] using
      (materialize_call_slot_readback witnessBase m j wtParams ws adjustedEnv adjustedObjEnv
        runFresh reservedNextFresh calleeBody hSlotsParams hFitCallee hCeilCallee pos)
  · have hFitRest : freshBase + StructIRFreshen.maxVarBody rest < runFresh := by
      exact lt_of_le_of_lt (Nat.add_le_add_left (maxVarBody_tail_le_cons (.call target args) rest) _) hFit
    exact lt_of_lt_of_le hFitRest hRunLeNext
  · simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody, reservedNextFresh,
      freshBody, nextFresh'', hNextEq] using hCeil
  · intro y hy
    exact lt_of_lt_of_le (hInitBound y hy) hRunLeNext

/-- All instruction variables in a compiled renamed body are either
    in `[base, ceil)` or `≥ witnessBase`. -/
private theorem compileConstrainBody_instrVars_in_range_aux
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (objEnv : ObjEnv) (base nextFresh : Nat)
        (origBody : List (ConstrainStmt n j F (m.structs j).members.length)),
      base + StructIRFreshen.maxVarBody origBody < nextFresh →
      ∀ (instr : FlatIR.Instr F),
      instr ∈ (compileConstrainBody witnessBase m j objEnv nextFresh
        (StructIRFreshen.renameBody (fun v => base + v) origBody)).1 →
      ∀ v ∈ FlatIR.instrVars instr,
        (base ≤ v ∧ v < (compileConstrainBody witnessBase m j objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) origBody)).2.2) ∨
        witnessBase ≤ v)
    (objEnv : ObjEnv) (base nextFresh : Nat)
    (origBody : List (ConstrainStmt n i F (m.structs i).members.length))
    (hBound : base + StructIRFreshen.maxVarBody origBody < nextFresh)
    (instr : FlatIR.Instr F)
    (hInstr : instr ∈ (compileConstrainBody witnessBase m i objEnv nextFresh
      (StructIRFreshen.renameBody (fun v => base + v) origBody)).1)
    (v : Nat) (hv : v ∈ FlatIR.instrVars instr) :
    (base ≤ v ∧ v < (compileConstrainBody witnessBase m i objEnv nextFresh
      (StructIRFreshen.renameBody (fun v => base + v) origBody)).2.2) ∨
    witnessBase ≤ v := by
  sorry
  /- Old proof cases for reference:
    | feltSub d s1 s2 | feltMul d s1 s2 | feltDiv d s1 s2 =>
      all_goals (
        simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
          compileConstrainBody, List.mem_cons] at hInstr
        have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
            (StructIRFreshen.renameBody (fun v => base + v) (_ :: rest'))).2.2 =
          (compileConstrainBody witnessBase m i objEnv nextFresh
            (StructIRFreshen.renameBody (fun v => base + v) rest')).2.2 := by
          simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
        rcases hInstr with rfl | hTail
        · have hmv := maxVarStmt_le_maxVarBody_cons _ rest'
          have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
            (StructIRFreshen.renameBody (fun v => base + v) rest')
          simp only [FlatIR.instrVars, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hv
          rw [hS]
          rcases hv with rfl | rfl | rfl <;>
            (left; exact ⟨by omega, by
              simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
        · rcases ih objEnv nextFresh hBound' instr hTail v hv with ⟨hlo, hhi⟩ | hge
          · left; exact ⟨hlo, hS ▸ hhi⟩
          · right; exact hge)
    | feltNeg d s =>
      simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
        compileConstrainBody, List.mem_cons] at hInstr
      have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v)
            (ConstrainStmt.feltNeg d s :: rest'))).2.2 =
        (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')).2.2 := by
        simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
      rcases hInstr with rfl | hTail
      · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltNeg d s) rest'
        have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')
        simp only [FlatIR.instrVars, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hv
        rw [hS]
        rcases hv with rfl | rfl <;>
          (left; exact ⟨by omega, by
            simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
      · rcases ih objEnv nextFresh hBound' instr hTail v hv with ⟨hlo, hhi⟩ | hge
        · left; exact ⟨hlo, hS ▸ hhi⟩
        · right; exact hge
    | feltConst d c =>
      simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
        compileConstrainBody, List.mem_cons] at hInstr
      have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v)
            (ConstrainStmt.feltConst d c :: rest'))).2.2 =
        (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')).2.2 := by
        simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
      rcases hInstr with rfl | hTail
      · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltConst d c) rest'
        have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')
        simp only [FlatIR.instrVars, List.mem_singleton] at hv
        rw [hS]
        rcases hv with rfl <;>
          (left; exact ⟨by omega, by
            simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
      · rcases ih objEnv nextFresh hBound' instr hTail v hv with ⟨hlo, hhi⟩ | hge
        · left; exact ⟨hlo, hS ▸ hhi⟩
        · right; exact hge
    | readMember d s member =>
      simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
        compileConstrainBody, List.mem_cons] at hInstr
      have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v)
            (ConstrainStmt.readMember d s member :: rest'))).2.2 =
        (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')).2.2 := by
        simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
      rcases hInstr with rfl | hTail
      · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.readMember d s member) rest'
        have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')
        simp only [FlatIR.instrVars, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hv
        rw [hS]
        rcases hv with rfl | rfl
        · left; exact ⟨by omega, by
            simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩
        · right; simp [encodeWitnessVar, encodeWitnessPos]; omega
      · rcases ih objEnv nextFresh hBound' instr hTail v hv with ⟨hlo, hhi⟩ | hge
        · left; exact ⟨hlo, hS ▸ hhi⟩
        · right; exact hge
    | constrainEq s1 s2 =>
      simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
        compileConstrainBody, List.mem_cons] at hInstr
      have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v)
            (ConstrainStmt.constrainEq s1 s2 :: rest'))).2.2 =
        (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')).2.2 := by
        simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
      rcases hInstr with rfl | hTail
      · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.constrainEq s1 s2) rest'
        have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) rest')
        simp only [FlatIR.instrVars, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hv
        rw [hS]
        rcases hv with rfl | rfl <;>
          (left; exact ⟨by omega, by
            simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
      · rcases ih objEnv nextFresh hBound' instr hTail v hv with ⟨hlo, hhi⟩ | hge
        · left; exact ⟨hlo, hS ▸ hhi⟩
        · right; exact hge
    | call target args =>
      sorry -/

/-- Wrapper: instruction variables of compiled renamed body are in [base, ceil) ∨ ≥ witnessBase. -/
theorem compileConstrainBody_instrVars_in_range
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (objEnv : ObjEnv) (base nextFresh : Nat)
    (origBody : List (ConstrainStmt n i F (m.structs i).members.length))
    (hBound : base + StructIRFreshen.maxVarBody origBody < nextFresh)
    (instr : FlatIR.Instr F)
    (hInstr : instr ∈ (compileConstrainBody witnessBase m i objEnv nextFresh
      (StructIRFreshen.renameBody (fun v => base + v) origBody)).1)
    (v : Nat) (hv : v ∈ FlatIR.instrVars instr) :
    (base ≤ v ∧ v < (compileConstrainBody witnessBase m i objEnv nextFresh
      (StructIRFreshen.renameBody (fun v => base + v) origBody)).2.2) ∨
    witnessBase ≤ v := by
  revert i objEnv base nextFresh origBody hBound instr hInstr v hv
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (objEnv : ObjEnv) (base nextFresh : Nat)
        (origBody : List (ConstrainStmt n i F (m.structs i).members.length)),
      base + StructIRFreshen.maxVarBody origBody < nextFresh →
      ∀ (instr : FlatIR.Instr F),
      instr ∈ (compileConstrainBody witnessBase m i objEnv nextFresh
        (StructIRFreshen.renameBody (fun v => base + v) origBody)).1 →
      ∀ v ∈ FlatIR.instrVars instr,
        (base ≤ v ∧ v < (compileConstrainBody witnessBase m i objEnv nextFresh
          (StructIRFreshen.renameBody (fun v => base + v) origBody)).2.2) ∨
        witnessBase ≤ v)
  · intro k ih_k i hi objEnv base nextFresh origBody hBound instr hInstr v hv
    exact compileConstrainBody_instrVars_in_range_aux witnessBase m i
      (fun j hj => ih_k j.val (hi ▸ hj) j rfl) objEnv base nextFresh origBody hBound instr hInstr v hv
  · rfl

theorem bodySatCtx_call_callee_frame
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.call target args :: rest))
    (hCalleeSat :
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let numParams := (m.structs j).constrain.numParams
      let adjustedObjEnv : ObjEnv := fun v =>
        if runFresh ≤ v then
          match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
          | some arg => objEnv arg
          | none => []
        else []
      let wtParams : FlatIR.Witness F := fun v =>
        if runFresh ≤ v ∧ v - runFresh < numParams then
          match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
          | some arg => wt arg
          | none => 0
        else wt v
      let adjustedEnv : LocalEnv F := fun v =>
        if runFresh ≤ v ∧ v - runFresh < numParams then
          match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
          | some arg => env arg
          | none => 0
        else 0
      let reservedNextFresh :=
        max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
          (runFresh + numParams)
      let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
      let wtAfterCallee :=
        materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
          reservedNextFresh freshBody
      FlatIR.satisfies wtAfterCallee
        (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1) :
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let calleeBody := (m.structs j).constrain.body
    let numParams := (m.structs j).constrain.numParams
    let adjustedObjEnv : ObjEnv := fun v =>
      if runFresh ≤ v then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => objEnv arg
        | none => []
      else []
    let wtParams : FlatIR.Witness F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => wt arg
        | none => 0
      else wt v
    let adjustedEnv : LocalEnv F := fun v =>
      if runFresh ≤ v ∧ v - runFresh < numParams then
        match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
        | some arg => env arg
        | none => 0
      else 0
    let reservedNextFresh :=
      max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
        (runFresh + numParams)
    let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
    let wtAfterCallee :=
      materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
        reservedNextFresh freshBody
    let nextFresh'' :=
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
    let wtFinal :=
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.call target args :: rest))
    FlatIR.satisfies wtFinal
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1 := by
  intro j calleeBody numParams adjustedObjEnv wtParams adjustedEnv reservedNextFresh freshBody
    wtAfterCallee nextFresh'' wtFinal
  have hFit := bodySatCtx.fit hctx
  have hCeil := bodySatCtx.ceil hctx
  have hFitRest : freshBase + StructIRFreshen.maxVarBody rest < runFresh := by
    exact lt_of_le_of_lt
      (Nat.add_le_add_left (maxVarBody_tail_le_cons (.call target args) rest) _) hFit
  have hReserved : runFresh ≤ reservedNextFresh :=
    le_trans (Nat.le_add_right _ _) (le_max_left _ _)
  have hNextGe : reservedNextFresh ≤ nextFresh'' :=
    compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh freshBody
  have hRunLeNext : runFresh ≤ nextFresh'' := le_trans hReserved hNextGe
  have hCeilRest : localCeilConstrainBody m i nextFresh'' rest ≤ witnessBase := by
    have := hCeil
    simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody,
      reservedNextFresh, freshBody, nextFresh'',
      compileConstrainBody_localCeil_eq witnessBase m j adjustedObjEnv reservedNextFresh
        freshBody] using this
  have hMatEq : wtFinal =
      materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) := by
    simpa [j, calleeBody, numParams, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
      freshBody, wtAfterCallee, nextFresh'', wtFinal] using
      materializeConstrainBody_call_rename_eq witnessBase m i wt env objEnv runFresh freshBase
        target args rest
  have hMaxBound : runFresh + StructIRFreshen.maxVarBody calleeBody < reservedNextFresh := by
    simp only [reservedNextFresh]
    exact lt_of_lt_of_le (by omega) (le_max_left _ _)
  -- Frame arguments
  have hMiddle : ∀ u, runFresh ≤ u → u < nextFresh'' → wtFinal u = wtAfterCallee u := by
    intro u hru hu
    have hEq := congrFun hMatEq u
    rw [hEq]
    exact materializeConstrainBody_middle_frame witnessBase m i freshBase wtAfterCallee env objEnv
      runFresh nextFresh'' u rest hFitRest hRunLeNext hru hu
  have hHigh : ∀ u, witnessBase ≤ u → wtFinal u = wtAfterCallee u := by
    intro u hu
    have hEq := congrFun hMatEq u
    rw [hEq]
    have hFitRest' : freshBase + StructIRFreshen.maxVarBody rest < nextFresh'' :=
      lt_of_lt_of_le hFitRest hRunLeNext
    exact materializeConstrainBody_high_frame witnessBase m i freshBase wtAfterCallee env objEnv
      nextFresh'' u rest hFitRest' (le_trans hCeilRest hu)
  -- Transfer using FlatIR_satisfies_of_eq
  apply FlatIR_satisfies_of_eq wtFinal wtAfterCallee
    (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1
    _ hCalleeSat
  intro instr hInstr u hu
  have hRange := compileConstrainBody_instrVars_in_range witnessBase m j
    adjustedObjEnv runFresh reservedNextFresh calleeBody hMaxBound instr
    hInstr u hu
  cases hRange with
  | inl h =>
    exact hMiddle u h.1 h.2
  | inr h => exact hHigh u h

theorem bodySatCtx_call_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (hSSA_all : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.call target args :: rest))
    (hCalleeEval : let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      evalConstrainBody m ws j
        (fun param =>
          match args[param]? with
          | some arg => env (StructIRFreshen.freshMap freshBase arg)
          | none => 0)
        (fun param =>
          match args[param]? with
          | some arg => objEnv (StructIRFreshen.freshMap freshBase arg)
          | none => [])
        (m.structs j).constrain.body)
    (hRestEval : evalConstrainBody m ws i
      (fun x => env (StructIRFreshen.freshMap freshBase x))
      (fun x => objEnv (StructIRFreshen.freshMap freshBase x))
      rest)
    (ihCallee : let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      ∀ (init' : Nat → Bool) (freshBase' : Nat) (wt' : FlatIR.Witness F)
        (env' : LocalEnv F) (objEnv' : ObjEnv) (runFresh' : Nat)
        (stmts' : List (ConstrainStmt n j F (m.structs j).members.length)),
      BodySatCtx witnessBase m j init' freshBase' wt' ws env' objEnv' runFresh' stmts' →
      evalConstrainBody m ws j
        (fun x => env' (StructIRFreshen.freshMap freshBase' x))
        (fun x => objEnv' (StructIRFreshen.freshMap freshBase' x)) stmts' →
      FlatIR.satisfies
        (materializeConstrainBody witnessBase m j wt' env' objEnv' runFresh'
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase') stmts'))
        (compileConstrainBody witnessBase m j objEnv' runFresh'
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase') stmts')).1)
    (ihRest : ∀ (init' : Nat → Bool) (wt' : FlatIR.Witness F)
        (env' : LocalEnv F) (objEnv' : ObjEnv) (runFresh' : Nat),
      BodySatCtx witnessBase m i init' freshBase wt' ws env' objEnv' runFresh' rest →
      evalConstrainBody m ws i
        (fun x => env' (StructIRFreshen.freshMap freshBase x))
        (fun x => objEnv' (StructIRFreshen.freshMap freshBase x)) rest →
      FlatIR.satisfies
        (materializeConstrainBody witnessBase m i wt' env' objEnv' runFresh'
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
        (compileConstrainBody witnessBase m i objEnv' runFresh'
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.call target args :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.call target args :: rest))).1 := by
  let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
  let calleeBody := (m.structs j).constrain.body
  let numParams := (m.structs j).constrain.numParams
  let adjustedObjEnv : ObjEnv := fun v =>
    if runFresh ≤ v then
      match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
      | some arg => objEnv arg
      | none => []
    else []
  let wtParams : FlatIR.Witness F := fun v =>
    if runFresh ≤ v ∧ v - runFresh < numParams then
      match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
      | some arg => wt arg
      | none => 0
    else wt v
  let adjustedEnv : LocalEnv F := fun v =>
    if runFresh ≤ v ∧ v - runFresh < numParams then
      match Option.map (StructIRFreshen.freshMap freshBase) args[v - runFresh]? with
      | some arg => env arg
      | none => 0
    else 0
  let reservedNextFresh :=
    max (runFresh + (StructIRFreshen.maxVarBody calleeBody + 1))
      (runFresh + numParams)
  let freshBody := StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody
  let wtAfterCallee :=
    materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
      reservedNextFresh freshBody
  let nextFresh'' :=
    (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
  let wtFinal :=
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
        (.call target args :: rest))
  have hSSA' := bodySatCtx.ssa hctx
  have hAgree' := bodySatCtx.agree hctx
  have hSlots' := bodySatCtx.slots hctx
  have hFit' := bodySatCtx.fit hctx
  have hParamSat : FlatIR.satisfies wtFinal
      (compileParamBindings (F := F) numParams (args.map (StructIRFreshen.freshMap freshBase))
        (StructIRFreshen.freshMap runFresh)) := by
    simpa [j, numParams, wtFinal] using
      materialize_call_param_binds_satisfy witnessBase m i init freshBase wt env objEnv runFresh ws
        target args rest hSSA' hAgree' hFit'
  have hCalleeCtx : BodySatCtx witnessBase m j (fun v => decide (v < numParams)) runFresh wtParams ws
      adjustedEnv adjustedObjEnv reservedNextFresh calleeBody := by
    simpa [j, calleeBody, numParams, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh] using
      bodySatCtx_call_callee_ctx witnessBase m i hSSA_all init freshBase wt ws env objEnv runFresh
        target args rest hctx
  have hCalleeEvalAdj : evalConstrainBody m ws j
      (fun x => adjustedEnv (StructIRFreshen.freshMap runFresh x))
      (fun x => adjustedObjEnv (StructIRFreshen.freshMap runFresh x)) calleeBody := by
    have hBridge := (evalConstrainBody_call_freshened_iff m ws i freshBase env objEnv runFresh
      target args)
    simpa [j, calleeBody, adjustedObjEnv, adjustedEnv] using hBridge.mpr hCalleeEval
  have hCalleeSat : FlatIR.satisfies wtAfterCallee
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1 := by
    exact ihCallee (fun v => decide (v < numParams)) runFresh wtParams adjustedEnv adjustedObjEnv
      reservedNextFresh calleeBody hCalleeCtx hCalleeEvalAdj
  have hRestCtx : BodySatCtx witnessBase m i init freshBase wtAfterCallee ws env objEnv nextFresh'' rest := by
    simpa [j, calleeBody, numParams, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
      freshBody, wtAfterCallee, nextFresh''] using
      bodySatCtx_call_rest_ctx witnessBase m i init freshBase wt ws env objEnv runFresh target args
        rest hctx
  have hRestSat : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1 := by
    exact ihRest init wtAfterCallee env objEnv nextFresh'' hRestCtx hRestEval
  have hCalleeFrame : FlatIR.satisfies wtFinal
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1 := by
    simpa [j, calleeBody, numParams, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
      freshBody, wtAfterCallee, nextFresh'', wtFinal] using
      bodySatCtx_call_callee_frame witnessBase m i init freshBase wt ws env objEnv runFresh
        target args rest hctx hCalleeSat
  have hMatEq : wtFinal =
      materializeConstrainBody witnessBase m i wtAfterCallee env objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) := by
    simpa [j, calleeBody, numParams, adjustedObjEnv, wtParams, adjustedEnv, reservedNextFresh,
      freshBody, wtAfterCallee, nextFresh'', wtFinal] using
      (materializeConstrainBody_call_rename_eq witnessBase m i wt env objEnv runFresh freshBase
        target args rest)
  have hRestSatFinal : FlatIR.satisfies wtFinal
      (compileConstrainBody witnessBase m i objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1 := by
    rw [hMatEq]
    exact hRestSat
  have hCompEq :
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.call target args :: rest))).1 =
      (compileParamBindings numParams (args.map (StructIRFreshen.freshMap freshBase))
          (StructIRFreshen.freshMap runFresh)) ++
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1 ++
      (compileConstrainBody witnessBase m i objEnv nextFresh''
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1 := by
    let paramInstrs : List (FlatIR.Instr F) :=
      compileParamBindings numParams (args.map (StructIRFreshen.freshMap freshBase))
        (StructIRFreshen.freshMap runFresh)
    let calleeInstrs : List (FlatIR.Instr F) :=
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1
    let tailInstrs : List (FlatIR.Instr F) :=
      (compileConstrainBody witnessBase m i objEnv nextFresh''
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1
    simp only [paramInstrs, calleeInstrs, tailInstrs, adjustedObjEnv, reservedNextFresh,
      freshBody, nextFresh'', numParams, calleeBody, j,
      StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody,
      StructIRFreshen.freshenBody, List.map, ← List.getElem?_map, List.append_assoc]
    rfl
  rw [hCompEq, satisfies_append, satisfies_append]
  exact ⟨⟨hParamSat, hCalleeFrame⟩, hRestSatFinal⟩

/-- Top-level reflection: FlatIR satisfies compiled program → StructIR satisfies source. -/
instance CorrectReflectingPass :
    ReflectingPass (StructIR.Language n F) (FlatIR.Language F) where
  toPass := CorrectPass (F := F) (n := n)
  reflection := by
    intro wt m hSat
    -- Local abbreviations that match the body of `compileProgram` /
    -- `StructIR.satisfies`.  Definitions are written so the compiled program
    -- is *definitionally* `mainParamBinds ++ body'` and the target satisfies
    -- predicate unfolds to `evalConstrainBody ... envSeed canonicalObjEnv ...`.
    let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
    let mainBody := (m.structs mainIdx).constrain.body
    let numParams := (m.structs mainIdx).constrain.numParams
    let numMembers := (m.structs mainIdx).members.length
    let localBase := localBoundOfModule m
    let ρ : Nat → Nat := StructIRFreshen.freshMap localBase
    have hρinj : Function.Injective ρ := StructIRFreshen.freshMap_injective _
    let renamedBody := StructIRFreshen.renameBody ρ mainBody
    let initObjEnv : ObjEnv := StructIR.ObjEnv.update (fun _ => []) (ρ 0) []
    let initNextFresh : Nat :=
      max (localBase + StructIRFreshen.maxVarBody mainBody + 1) (localBase + numParams)
    let wBase := witnessBase m
    let mainParamBinds : List (FlatIR.Instr F) :=
      compileMainParamBindings (F := F) wBase numMembers numParams ρ
    refine ⟨fun pos => wt (encodeWitnessPos wBase pos), ?_, ?_⟩
    · intro pos
      rfl
    · let ws : StructIR.Witness F := fun pos => wt (encodeWitnessPos wBase pos)
      -- Split the compiled program into param-bindings ++ body.
      have hSatProg : FlatIR.satisfies wt
          (mainParamBinds ++
            (compileConstrainBody wBase m mainIdx initObjEnv initNextFresh renamedBody).1) := hSat
      rw [satisfies_append] at hSatProg
      obtain ⟨hParamBinds, hBody⟩ := hSatProg
      -- Leg 1: per-param equality `wt (ρ p) = wt (encodeParamVar numMembers p)`.
      have hParamEq : ∀ p, p < numParams →
          wt (ρ p) = wt (encodeParamVar wBase numMembers p) := fun p hp =>
        compileMainParamBindings_env_agree
          (F := F) wBase numMembers numParams ρ wt hParamBinds p hp
      -- Leg 2: reflect the renamed body.
      have hSlotAgree : ∀ pos, wt (encodeWitnessPos wBase pos) = ws pos := by
        intro pos; rfl
      have hBodyEval : evalConstrainBody m ws mainIdx wt initObjEnv renamedBody :=
        body_reflection_wt (F := F) (n := n + 1) wBase m ws wt hSlotAgree mainIdx m.all_ssa
          initObjEnv initNextFresh renamedBody hBody
      -- Leg 2': fold `ρ` out.
      have hUnrenamed :
          evalConstrainBody m ws mainIdx (wt ∘ ρ) (initObjEnv ∘ ρ) mainBody := by
        have hren :=
          StructIRFreshen.evalConstrainBody_rename
            (F := F) (n := n + 1) m ws mainIdx wt initObjEnv ρ hρinj mainBody
        exact hren.mp hBodyEval
      -- Leg 3a: object env after `∘ ρ` simplifies to the canonical form.
      have hObjEnvComp : initObjEnv ∘ ρ = ObjEnv.update (fun _ => []) 0 [] := by
        funext k
        change initObjEnv (ρ k) = ObjEnv.update (fun _ => []) 0 [] k
        simp only [ObjEnv.update, initObjEnv]
        by_cases hk : k = 0
        · subst hk; simp
        · have hkρ : ρ k ≠ ρ 0 := fun h => hk (hρinj h)
          have hkρ' : (ρ k == ρ 0) = false := by simp [hkρ]
          have hk' : (k == 0) = false := by simp [hk]
          rw [hkρ', hk']
      have hCanonObj :
          evalConstrainBody m ws mainIdx (wt ∘ ρ)
            (ObjEnv.update (fun _ => []) 0 []) mainBody := by
        have := hUnrenamed
        rw [hObjEnvComp] at this
        exact this
      -- Leg 3b: swap `wt' ws ∘ ρ` for the param-seeded local env.
      let envSeed : LocalEnv F :=
        fun k => if k < numParams then ws (StructIR.paramCoord numMembers k) else 0
      have hParamAgree : ∀ p, p < numParams → (wt ∘ ρ) p = envSeed p := by
        intro p hp
        have hWt := hParamEq p hp
        have h3 :
            wt (encodeParamVar wBase numMembers p) = ws (StructIR.paramCoord numMembers p) := by
          exact hSlotAgree (StructIR.paramCoord numMembers p)
        have h4 : (wt ∘ ρ) p = ws (StructIR.paramCoord numMembers p) := by
          calc (wt ∘ ρ) p
              = wt (ρ p) := rfl
            _ = wt (encodeParamVar wBase numMembers p) := hWt
            _ = ws (StructIR.paramCoord numMembers p) := h3
        change (wt ∘ ρ) p =
            (fun k => if k < numParams then ws (StructIR.paramCoord numMembers k) else 0) p
        rw [h4]; simp [hp]
      have hSwap :=
        evalConstrainBody_env_agree_on_init m ws mainIdx (wt ∘ ρ) envSeed
          (ObjEnv.update (fun _ => []) 0 []) mainBody (m.all_ssa mainIdx)
          (by intro v hv
              have hvlt : v < numParams := by simpa using hv
              exact hParamAgree v hvlt)
      -- Conclude: `StructIR.satisfies ws m` unfolds definitionally to this goal.
      change evalConstrainBody m ws mainIdx envSeed
            (ObjEnv.update (fun _ => []) 0 []) mainBody
      exact hSwap.mp hCanonObj

end StructIRToFlatIR
