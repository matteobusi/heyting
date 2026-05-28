/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.StructIRToFlatIR.FrameLemmas

/-!
# StructIR → FlatIR: Witness Compilation and Readback Lemmas

`witnessCompile` constructs the FlatIR witness from a StructIR witness
by running the materializer. The readback lemmas then prove that:

- Shifted witness slots remain equal to their StructIR originals.
- Materialised local slots read back the correct computed values.
- Call parameter bindings satisfy their compiled instructions.
- Head/tail decomposition lemmas for propagating readback through bodies.

These lemmas are the key bridge used by `BodySatCtx` in `ForwardPass`.
-/
namespace StructIRToFlatIR

open StructIR
open StructIRToFlatIR.CompressTactics

variable {F : Type} [Field F] {n : Nat}

/-- Specialized forward witness for `compileProgram`: seed shifted witness slots
    from a StructIR witness `ws`, seed renamed main params from canonical param
    coords, then materialize renamed main body locals. -/
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
  let wtSeed :=
    seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  materializeConstrainBody wBase m mainIdx wtSeed envSeed initObjEnv
    initNextFresh renamedBody

/-- `witnessCompile` preserves shifted witness-slot relation by construction. -/
theorem witnessCompile_rel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) :
    ExecutablePass (F := F) (n := n) |>.witnessRel m ws (witnessCompile (n := n) m ws) := by
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
  let wtSeed :=
    seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  have hwBase_ge_params : localBase + numParams ≤ wBase := by
    have hInit : localBase + numParams ≤ initNextFresh := by simp [initNextFresh]
    have hCeil : initNextFresh ≤ wBase := by
      simpa [wBase, witnessBase] using
        (localCeilConstrainBody_next_ge m mainIdx initNextFresh renamedBody)
    exact le_trans hInit hCeil
  have hFit : localBase + StructIRFreshen.maxVarBody mainBody < initNextFresh := by
    simp [initNextFresh]
  have hCeil : localCeilConstrainBody m mainIdx initNextFresh mainBody ≤ wBase := by
    have hRename := localCeilConstrainBody_rename m mainIdx initNextFresh ρ mainBody
    have hwBase : wBase = localCeilConstrainBody m mainIdx initNextFresh renamedBody := by
      simp [wBase, witnessBase, mainIdx, mainBody, numParams, localBase, ρ, renamedBody,
        initNextFresh]
    rw [← hRename, hwBase]
  refine Eq.trans ?_
    (materializeConstrainBody_slot_frame wBase m mainIdx localBase wtSeed ws envSeed
      initObjEnv initNextFresh mainBody ?_ hFit hCeil pos)
  · simp [witnessCompile, mainIdx, mainBody, numParams, numMembers, localBase, ρ,
      initObjEnv, initNextFresh, wBase, wtSeed, envSeed]
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
    let wtSeed :=
      seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
    let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
    materializeConstrainBody wBase m mainIdx wtSeed envSeed initObjEnv initNextFresh
        renamedBody (ρ p) =
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
  let wtSeed :=
    seedMainParamLocalsWitness localBase numParams numMembers ws (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  have hp' : p < numParams := by simpa [Module.main, mainIdx, numParams] using hp
  have hx : (fun v => decide (v < numParams)) p = true := by simp [hp']
  have hlt : ρ p < initNextFresh := by
    have h1 : localBase + p < localBase + numParams := by omega
    exact lt_of_lt_of_le h1 (Nat.le_max_right _ _)
  simpa [mainIdx, mainBody, numParams, numMembers, localBase, ρ,
    renamedBody, initObjEnv, initNextFresh, wBase, wtSeed, envSeed] using
    materializeConstrainBody_init_frame wBase m mainIdx
      (fun v => decide (v < numParams)) wtSeed envSeed initObjEnv localBase initNextFresh
      p mainBody (m.all_ssa mainIdx) hx hlt

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
          have hrel := witnessCompile_rel (m := m) (ws := ws)
            (pos := StructIR.paramCoord numMembers p)
          simpa [encodeParamVar] using hrel

omit [Field F] in
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
    · have hne :
          StructIRFreshen.freshMap freshBase x ≠ StructIRFreshen.freshMap freshBase dest := by
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
    (hAgree :
      wt (StructIRFreshen.freshMap freshBase x) = env (StructIRFreshen.freshMap freshBase x))
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
          materializeConstrainBody_init_frame witnessBase m i init wt env objEnv freshBase
            runFresh x stmts hSSA hInit hlt
    _ = env (StructIRFreshen.freshMap freshBase x) := hAgree

omit [Field F] in
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

omit [Field F] in
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

omit [Field F] in
lemma isSSA_read_true_of_mem {i : Fin n} {nm : Nat}
    (init : Nat → Bool) (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
    (x : Nat)
    (hSSA : StructIR.isSSA init (stmt :: rest) = true)
    (hx : x ∈ stmt.reads) :
    init x = true := by
  simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
  exact list_all_true_of_mem _ _ _ hSSA.1 hx

omit [Field F] in
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
  exact materializeConstrainBody_init_readback witnessBase m i init wt env objEnv freshBase
    runFresh x rest hSSA' hx (hAgree x hx) hlt

lemma runFresh_le_witnessBase_of_ceiling
    (m : Module n F) (i : Fin n) (runFresh witnessBase : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hCeil : localCeilConstrainBody m i runFresh stmts ≤ witnessBase) :
    runFresh ≤ witnessBase := by
  exact le_trans (localCeilConstrainBody_next_ge m i runFresh stmts) hCeil

omit [Field F] in
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
    (hAgree :
      wt (StructIRFreshen.freshMap freshBase x) = env (StructIRFreshen.freshMap freshBase x))
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
  exact materializeConstrainBody_slot_frame witnessBase m j runFresh wt ws adjustedEnv
    adjustedObjEnv reservedNextFresh calleeBody hSlots hFit hCeil pos

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
      have hx' : x = src1 ∨ x = src2 := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl | rfl <;> simp [StructIRFreshen.maxVarStmt]
  | feltSub dest src1 src2 =>
      have hx' : x = src1 ∨ x = src2 := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl | rfl <;> simp [StructIRFreshen.maxVarStmt]
  | feltMul dest src1 src2 =>
      have hx' : x = src1 ∨ x = src2 := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl | rfl <;> simp [StructIRFreshen.maxVarStmt]
  | feltDiv dest src1 src2 =>
      have hx' : x = src1 ∨ x = src2 := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl | rfl <;> simp [StructIRFreshen.maxVarStmt]
  | feltNeg dest src =>
      have hx' : x = src := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl
      simp [StructIRFreshen.maxVarStmt]
  | feltInv dest src =>
      have hx' : x = src := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl
      simp [StructIRFreshen.maxVarStmt]
  | feltConst dest c =>
      simp [ConstrainStmt.reads] at hx
  | readMember dest self member =>
      have hx' : x = self := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl
      simp [StructIRFreshen.maxVarStmt]
  | constrainEq src1 src2 =>
      have hx' : x = src1 ∨ x = src2 := by
        simpa [ConstrainStmt.reads] using hx
      rcases hx' with rfl | rfl <;> simp [StructIRFreshen.maxVarStmt]
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
  | feltAdd dest' src1 src2 => cases hd; simp [StructIRFreshen.maxVarStmt]
  | feltSub dest' src1 src2 => cases hd; simp [StructIRFreshen.maxVarStmt]
  | feltMul dest' src1 src2 => cases hd; simp [StructIRFreshen.maxVarStmt]
  | feltDiv dest' src1 src2 => cases hd; simp [StructIRFreshen.maxVarStmt]
  | feltNeg dest' src => cases hd; simp [StructIRFreshen.maxVarStmt]
  | feltInv dest' src => cases hd; simp [StructIRFreshen.maxVarStmt]
  | feltConst dest' c => cases hd; simp [StructIRFreshen.maxVarStmt]
  | readMember dest' self member => cases hd; simp [StructIRFreshen.maxVarStmt]
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
    (_m : Module n F) (stmt : ConstrainStmt n i F nm) (rest : List (ConstrainStmt n i F nm))
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
  exact materializeConstrainBody_init_readback witnessBase m i init wt env objEnv freshBase
    runFresh x (stmt :: rest) hSSA hInit (hAgree x hInit) hlt

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
    let _wtAfterCallee :=
      materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
        reservedNextFresh freshBody
    let _nextFresh'' :=
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
    let wtFinal :=
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
         (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
           (.call target args :: rest))
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
  have hParamSeedAgree :
      wtParams (StructIRFreshen.freshMap runFresh p) =
        adjustedEnv (StructIRFreshen.freshMap runFresh p) := by
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
    | none => simp
    | some arg =>
        simp only [Option.map_some]
        exact hAgree arg <|
          isSSA_read_true_of_mem init (.call target args) rest arg hSSA
            (by simpa [ConstrainStmt.reads] using List.mem_of_getElem? harg)
  have hParamAfterCallee : wtAfterCallee (StructIRFreshen.freshMap runFresh p) =
      adjustedEnv (StructIRFreshen.freshMap runFresh p) := by
    have hInit : (fun v => decide (v < numParams)) p = true := by simp [hp']
    have hlt : StructIRFreshen.freshMap runFresh p < reservedNextFresh := by
      simpa [StructIRFreshen.freshMap] using hParamLt
    simpa [wtAfterCallee, freshBody] using
      materializeConstrainBody_init_readback witnessBase m j
        (fun v => decide (v < numParams)) wtParams adjustedEnv adjustedObjEnv runFresh
        reservedNextFresh p calleeBody (m.all_ssa j) hInit hParamSeedAgree hlt
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
        (StructIRFreshen.freshMap runFresh p) =
          wtAfterCallee (StructIRFreshen.freshMap runFresh p) := by
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
          rw [show StructIRFreshen.freshMap runFresh p - runFresh = p by
            simp [StructIRFreshen.freshMap]]
          cases harg : args[p]? <;> simp

theorem materialize_call_param_binds_satisfy
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (_ws : StructIR.Witness F)
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
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.call target args :: rest))
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
  have hLeft := materialize_call_param_slot_readback witnessBase m i init freshBase wt env
    objEnv runFresh target args rest hSSA hAgree hFit p (by simpa [numParams] using hp)
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
          materializeConstrainBody_head_readback witnessBase m i init wt env objEnv freshBase
            runFresh arg (.call target args) rest hSSA hAgree hFit
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
    freshMap_dest_lt_witnessBase_of_fit_cons freshBase runFresh witnessBase dest m stmt rest
      hFit hRun hd
  have hDestLt' : freshBase + dest < runFresh := by
    simpa [StructIRFreshen.freshMap] using
      freshMap_dest_lt_runFresh_of_fit_cons freshBase runFresh dest stmt rest hFit hd
  exact witness_slots_agree_after_write witnessBase freshBase dest runFresh wt ws val
    hSlots hDestLt' hRun

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
  · have hne :
        StructIRFreshen.freshMap freshBase x ≠ StructIRFreshen.freshMap freshBase dest := by
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
  have hSlots' : ∀ pos,
      (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
        (encodeWitnessPos witnessBase pos) = ws pos :=
    witness_slots_agree_after_head_write witnessBase m i freshBase runFresh dest wt ws stmt
      rest val hSlots hFit hCeilCons hd
  exact materializeConstrainBody_slot_frame witnessBase m i freshBase
    (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v) ws
    (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv runFresh rest
    hSlots' hFitRest hCeilRest pos


end StructIRToFlatIR
