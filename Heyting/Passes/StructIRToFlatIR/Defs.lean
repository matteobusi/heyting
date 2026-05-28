/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.VarIdEncoding
import Heyting.Core.Pass
import Heyting.Languages.FlatIR
import Heyting.Languages.StructIRFreshen
import Heyting.Languages.StructIR
import Heyting.Passes.StructIRToFlatIRTactics

/-!
# StructIR → FlatIR: Compiler Definitions

`compileConstrainBody`, `compileProgram`, auxiliary encoding definitions,
and the small lemmas that support them (satisfaction decomposition,
local ceiling, parameter bindings, compilation correctness for each
instruction shape).
-/
namespace StructIRToFlatIR

open StructIR
open StructIRToFlatIR.CompressTactics

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
    | .feltInv dest src =>
      let (tail, objEnv', nextFresh') := compileConstrainBody witnessBase m i objEnv nextFresh rest
      (FlatIR.Instr.assignInv dest src :: tail, objEnv', nextFresh')
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

omit [Field F] in
lemma localCeilConstrainBody_noncall_cons {i : Fin n}
    (m : StructIR.Module n F) (nextFresh : Nat)
    (stmt : StructIR.ConstrainStmt n i F (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (hNoCall : ∀ target args, stmt ≠ .call target args) :
    localCeilConstrainBody m i nextFresh (stmt :: rest) =
      localCeilConstrainBody m i nextFresh rest := by
  cases stmt <;> simp only [localCeilConstrainBody]
  · exfalso; exact hNoCall _ _ rfl

omit [Field F] in
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

instance ExecutablePass (F : Type) [Field F] (n : Nat) :
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
    (hAgree : ∀ v,
      (fun v => v < (m.structs i).constrain.numParams) v = true → env1 v = env2 v) :
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
        have hcond' :
            runFresh ≤ runFresh + v ∧
              runFresh + v - runFresh < (m.structs j).constrain.numParams := by
          simpa [StructIRFreshen.freshMap, Nat.add_sub_cancel_left] using hcond
        simp [Function.comp_apply, adjustedEnv, calleeEnv, StructIRFreshen.freshMap, h, hcond',
          Nat.add_sub_cancel_left]
    | some arg =>
        have hcond' :
            runFresh ≤ runFresh + v ∧
              runFresh + v - runFresh < (m.structs j).constrain.numParams := by
          simpa [StructIRFreshen.freshMap, Nat.add_sub_cancel_left] using hcond
        have hnot : ¬ (m.structs j).constrain.numParams ≤ v := Nat.not_le_of_lt hv'
        simp [Function.comp_apply, adjustedEnv, calleeEnv, StructIRFreshen.freshMap, h, hcond',
          Nat.add_sub_cancel_left, hnot]
  calc
    evalConstrainBody m ws j (fun x => adjustedEnv (StructIRFreshen.freshMap runFresh x))
        (fun x => adjustedObjEnv (StructIRFreshen.freshMap runFresh x)) calleeBody
      ↔ evalConstrainBody m ws j calleeEnv (adjustedObjEnv ∘ StructIRFreshen.freshMap runFresh)
          calleeBody :=
            evalConstrainBody_env_agree_on_init m ws j
              (adjustedEnv ∘ StructIRFreshen.freshMap runFresh) calleeEnv
              (adjustedObjEnv ∘ StructIRFreshen.freshMap runFresh) calleeBody
              (m.all_ssa j) hEnvAgree
    _ ↔ evalConstrainBody m ws j calleeEnv calleeObjEnv calleeBody := by
          simp [hObjEq]

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
    | feltInv dest src =>
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
    | feltInv dest src => simpa [compileConstrainBody] using ih objEnv nextFresh
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
      | feltAdd dest src1 src2 =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltSub dest src1 src2 =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltMul dest src1 src2 =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltDiv dest src1 src2 =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltNeg dest src =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltInv dest src =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
      | feltConst dest c =>
          simpa [compileConstrainBody, localCeilConstrainBody] using ih objEnv nextFresh
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
          let reservedNextFresh :=
            max nextFresh' (nextFresh + (m.structs j).constrain.numParams)
          have hCallee :
              (compileConstrainBody witnessBase m j adjustedObjEnv
                reservedNextFresh freshBody).2.2 =
                localCeilConstrainBody m j reservedNextFresh freshBody :=
            ih_i j target.isLt adjustedObjEnv reservedNextFresh freshBody
          have hTail :
              (compileConstrainBody witnessBase m i objEnv
                  (compileConstrainBody witnessBase m j adjustedObjEnv
                    reservedNextFresh freshBody).2.2
                  rest).2.2 =
              localCeilConstrainBody m i
                (localCeilConstrainBody m j reservedNextFresh freshBody) rest := by
            simpa [hCallee] using
              ih objEnv
                (compileConstrainBody witnessBase m j adjustedObjEnv
                  reservedNextFresh freshBody).2.2
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


end StructIRToFlatIR
