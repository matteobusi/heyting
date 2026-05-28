/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.StructIRToFlatIR.Defs

/-!
# StructIR → FlatIR: Forward Materializer

`materializeConstrainBody` mirrors `compileConstrainBody` one-to-one,
writing into a FlatIR witness `wt` so each emitted instruction is satisfied.
Includes `_rename_eq` lemmas, frame setup helpers (`materialize_tail_of_*`,
`materialize_call_param_seed_frame`, `call_reservedNextFresh_ge`) and the
`fresh_frame` theorem family.
-/
namespace StructIRToFlatIR

open StructIR
open StructIRToFlatIR.CompressTactics

variable {F : Type} [Field F] {n : Nat}

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
    | .feltInv dest src =>
      let val := (env src)⁻¹
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
      | feltInv dest src =>
          let val := (env (StructIRFreshen.freshMap freshBase src))⁻¹
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
            exact le_trans (Nat.le_add_right _ _) (le_max_left _ _)
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
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh
                freshBody
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
    (hle : freshBase ≤ runFresh) (_hlow : low ≤ v) (hv : v < freshBase) :
    materializeConstrainBody witnessBase m i wt env objEnv runFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts) v = wt v := by
  exact materializeConstrainBody_fresh_frame witnessBase m i freshBase wt env objEnv runFresh v
    stmts hle hv


end StructIRToFlatIR
