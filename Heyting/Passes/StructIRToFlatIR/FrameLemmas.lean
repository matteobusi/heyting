/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.StructIRToFlatIR.Materializer

/-!
# StructIR → FlatIR: Frame Lemmas

Frame theorems ensuring the materializer only writes to local slots below
`witnessBase`, leaving shifted witness slots (≥ witnessBase) and other
zones intact:

- **High-frame**: writes stay below `localCeil` (slots ≥ localCeil untouched)
- **Middle-frame**: writes outside `[anchor, runFresh)` leave that window
- **Init-frame**: SSA-initialized slots survive materialisation untouched
- **Slot/interval frames**: shifted witness slots survive unchanged
-/
namespace StructIRToFlatIR

open StructIR
open StructIRToFlatIR.CompressTactics

variable {F : Type} [Field F] {n : Nat}

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

omit [Field F] in
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
    (_ih_i : ∀ (j : Fin n), j.val < i.val →
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
          materialize_high_frame_felt_case (.feltAdd dest src1 src2)
      | feltSub dest src1 src2 =>
          materialize_high_frame_felt_case (.feltSub dest src1 src2)
      | feltMul dest src1 src2 =>
          materialize_high_frame_felt_case (.feltMul dest src1 src2)
      | feltDiv dest src1 src2 =>
          materialize_high_frame_felt_case (.feltDiv dest src1 src2)
      | feltNeg dest src =>
          materialize_high_frame_felt_case (.feltNeg dest src)
      | feltInv dest src =>
          materialize_high_frame_felt_case (.feltInv dest src)
      | feltConst dest c =>
          materialize_high_frame_felt_case (.feltConst dest c)
      | readMember dest self member =>
          rw [materializeConstrainBody_readMember_rename_eq]; simp only
          have hDest : freshBase + dest < runFresh := by
            have := maxVarStmt_le_maxVarBody_cons
              (.readMember dest self member : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this; omega
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            exact localCeilConstrainBody_noncall_tail_le m runFresh v
              (.readMember dest self member) rest (by intro target args hCall; cases hCall) hv
          calc _ = _ := ih _ _ _ _ hFitRest hv'
            _ = wt v :=
              witness_update_high_frame wt freshBase dest runFresh v _ hDest hRun_le_v
      | constrainEq src1 src2 =>
          rw [materializeConstrainBody_constrainEq_rename_eq]
          have hv' : localCeilConstrainBody m i runFresh rest ≤ v := by
            exact localCeilConstrainBody_noncall_tail_le m runFresh v
              (.constrainEq src1 src2) rest (by intro target args hCall; cases hCall) hv
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
            exact _ih_i j target.isLt runFresh wtParams _ adjustedObjEnv
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
    (_ih_i : ∀ (j : Fin n), j.val < i.val →
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
          materialize_middle_frame_felt_case (.feltAdd dest src1 src2)
      | feltSub dest src1 src2 =>
          materialize_middle_frame_felt_case (.feltSub dest src1 src2)
      | feltMul dest src1 src2 =>
          materialize_middle_frame_felt_case (.feltMul dest src1 src2)
      | feltDiv dest src1 src2 =>
          materialize_middle_frame_felt_case (.feltDiv dest src1 src2)
      | feltNeg dest src =>
          materialize_middle_frame_felt_case (.feltNeg dest src)
      | feltInv dest src =>
          materialize_middle_frame_felt_case (.feltInv dest src)
      | feltConst dest c =>
          materialize_middle_frame_felt_case (.feltConst dest c)
      | readMember dest self member =>
          rw [materializeConstrainBody_readMember_rename_eq]
          simp only
          have hDest : freshBase + dest < anchor := by
            have := maxVarStmt_le_maxVarBody_cons
              (.readMember dest self member : ConstrainStmt n i F _) rest
            simp [StructIRFreshen.maxVarStmt] at this
            omega
          calc
            materializeConstrainBody witnessBase m i
                (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    wt
                      (encodeWitnessVar witnessBase
                        (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (wt
                    (encodeWitnessVar witnessBase
                      (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
                (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
                  (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
                runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest) v
              = (fun u =>
                  if u = StructIRFreshen.freshMap freshBase dest then
                    wt
                      (encodeWitnessVar witnessBase
                        (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
                  else wt u) v := by
                    exact ih (wt := _)
                      (env := env.update (StructIRFreshen.freshMap freshBase dest)
                        (wt (encodeWitnessVar witnessBase
                          (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
                      (objEnv :=
                        StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
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
                      StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody
                    from rfl]
                exact materializeConstrainBody_fresh_frame witnessBase m j runFresh wtParams
                  adjustedEnv adjustedObjEnv reservedNextFresh v calleeBody hReserved hv
              _ = wt v := by
                simpa [wtParams] using
                  materialize_call_param_seed_frame wt (m.structs j).constrain.numParams runFresh v
                    (args.map (StructIRFreshen.freshMap freshBase)) hv
          have hNext : runFresh ≤ nextFresh'' := by
            exact le_trans hReserved <|
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh
                freshBody
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
    intro j hj freshBase' wt' env' objEnv' anchor' runFresh' v' stmts'
        hFit' hAnchorRun' hAnchorV' hv'
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
            exact ih init stmt dest (by simpa [hs] using hSSA') hmem hdest
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
    (_ih_i : ∀ (j : Fin n), j.val < i.val →
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
      | feltAdd dest src1 src2 => materialize_init_frame_felt_case
      | feltSub dest src1 src2 => materialize_init_frame_felt_case
      | feltMul dest src1 src2 => materialize_init_frame_felt_case
      | feltDiv dest src1 src2 => materialize_init_frame_felt_case
      | feltNeg dest src       => materialize_init_frame_felt_case
      | feltInv dest src       => materialize_init_frame_felt_case
      | feltConst dest c       => materialize_init_frame_felt_case
      | readMember dest self member =>
          have hStep :
              !init dest && StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [ConstrainStmt.dest] using hSSA'
          have hStep' :
              (!init dest = true) ∧
                StructIR.isSSA (fun y => init y || y == dest) rest = true := by
            simpa [Bool.and_eq_true] using hStep
          have hne : x ≠ dest := init_true_dest_ne hx (by simpa using hStep'.1)
          rw [materializeConstrainBody_readMember_rename_eq]
          calc
            materializeConstrainBody witnessBase m i
                (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    wt (encodeWitnessVar witnessBase
                          (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
                  else wt u)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (wt (encodeWitnessVar witnessBase
                    (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
                (StructIR.ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest)
                  (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
                runFresh
                (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
                (StructIRFreshen.freshMap freshBase x)
              = (fun u => if u = StructIRFreshen.freshMap freshBase dest then
                    wt (encodeWitnessVar witnessBase
                          (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
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
            rw [show freshBody =
                  StructIRFreshen.renameBody (StructIRFreshen.freshMap runFresh) calleeBody
                from rfl]
            exact materializeConstrainBody_fresh_frame witnessBase m j runFresh wtParams
              adjustedEnv adjustedObjEnv reservedNextFresh
              (StructIRFreshen.freshMap freshBase x) calleeBody hReserved hlt
          have hParams : wtParams (StructIRFreshen.freshMap freshBase x) =
              wt (StructIRFreshen.freshMap freshBase x) := by
            simpa [j, wtParams] using materialize_call_param_seed_frame wt
              (m.structs j).constrain.numParams runFresh (StructIRFreshen.freshMap freshBase x)
              (args.map (StructIRFreshen.freshMap freshBase)) hlt
          have hNext : runFresh ≤ nextFresh'' := by
            exact le_trans hReserved <|
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh
                freshBody
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

end StructIRToFlatIR
