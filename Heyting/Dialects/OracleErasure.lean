/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.TypedSourceSemantics

/-!
# Oracle erasure for constraint compilation

The full typed frontend set retains Oracle operations for compute execution.
Constraint compilation explicitly projects that module to
`[Call, StructObject, Felt, ConstrainEq]`: an oracle read becomes `felt.const 0`
inside witness bodies. This value cannot affect emitted constraints because
constraint bodies reject witness-capability operations. Concrete witnesses are
produced from the un-erased module by `WitnessExecution`.
-/

namespace Dialect.OracleErasure

open Dialect

abbrev SourceSet := LLZK.DialectLowering.WitnessSourceSet
abbrev TargetSet := LLZK.DialectLowering.SourceSet

private abbrev callIx : Fin TargetSet.length := ⟨0, by simp [TargetSet]⟩
private abbrev structIx : Fin TargetSet.length := ⟨1, by simp [TargetSet]⟩
private abbrev feltIx : Fin TargetSet.length := ⟨2, by simp [TargetSet]⟩
private abbrev constrainIx : Fin TargetSet.length := ⟨3, by simp [TargetSet]⟩

abbrev oracleSourceIx : Fin SourceSet.length := ⟨2, by simp [SourceSet]⟩

/-- A body contains no Oracle operation. -/
def OracleFreeBody {ctx : OpCtx} {F : Type}
    (body : List (Stmt SourceSet ctx F)) : Prop :=
  ∀ op : Oracle.Op ctx F, (Stmt.op oracleSourceIx op : Stmt SourceSet ctx F) ∉ body

/-- Oracle syntax cannot occur in a certified constraint body. This is the
semantic reason Oracle projection is irrelevant to source constraints; the
zero emitted for unchecked witness syntax is not used as a correctness axiom. -/
theorem constrain_body_no_oracle {n i numMembers : Nat} {F : Type}
    (fn : FuncDef SourceSet n i F .constraint numMembers)
    (op : Oracle.Op ⟨n, i, numMembers⟩ F)
    (hmem : (Stmt.op oracleSourceIx op :
      Stmt SourceSet ⟨n, i, numMembers⟩ F) ∈ fn.body) : False := by
  have hle := Dialect.cap_le_of_capsLE fn.wf_caps hmem
  change Oracle.cap op ≤ Capability.constraint at hle
  change Capability.witness = Capability.pure ∨
    Capability.witness = Capability.constraint at hle
  rcases hle with h | h <;> cases h

theorem constrain_body_oracleFree {n i numMembers : Nat} {F : Type}
    (fn : FuncDef SourceSet n i F .constraint numMembers) :
    OracleFreeBody fn.body := by
  intro op hmem
  exact constrain_body_no_oracle fn op hmem

theorem OracleFreeBody.tail {ctx : OpCtx} {F : Type}
    {head : Stmt SourceSet ctx F} {tail : List (Stmt SourceSet ctx F)}
    (hfree : OracleFreeBody (head :: tail)) : OracleFreeBody tail := by
  intro op hmem
  exact hfree op (by simp [hmem])

def lowerBody {n i numMembers : Nat} {F : Type} [OfNat F 0] :
    List (Stmt SourceSet ⟨n, i, numMembers⟩ F) →
      List (Stmt TargetSet ⟨n, i, numMembers⟩ F)
  | [] => []
  | .op d payload :: rest =>
    let head : Stmt TargetSet ⟨n, i, numMembers⟩ F :=
      match d with
      | ⟨0, _⟩ => .op callIx payload
      | ⟨1, _⟩ => .op structIx payload
      | ⟨2, _⟩ => match payload with
        | .next dest => .op feltIx (.const dest 0)
      | ⟨3, _⟩ => .op feltIx payload
      | ⟨4, _⟩ => .op constrainIx payload
    head :: lowerBody rest

def lowerFunc {n i numMembers : Nat} {F : Type} [OfNat F 0]
    {kind : Capability} (label : String)
    (fn : FuncDef SourceSet n i F kind numMembers) :
    Except String (FuncDef TargetSet n i F kind numMembers) :=
  LLZK.DialectLowering.certifyFunc label fn.numParams
    (lowerBody fn.body) fn.returnVar

theorem lowerFunc_fields {n i numMembers : Nat} {F : Type} [OfNat F 0]
    {kind : Capability} (label : String)
    (fn : FuncDef SourceSet n i F kind numMembers)
    (out : FuncDef TargetSet n i F kind numMembers)
    (hlower : lowerFunc label fn = .ok out) :
    out.numParams = fn.numParams ∧ out.body = lowerBody fn.body ∧
      out.returnVar = fn.returnVar := by
  unfold lowerFunc LLZK.DialectLowering.certifyFunc at hlower
  split at hlower <;> rename_i hcaps
  · split at hlower <;> rename_i hssa
    · have hout := Except.ok.inj hlower
      subst out
      exact ⟨rfl, rfl, rfl⟩
    · simp at hlower
  · simp at hlower

def lowerStruct {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) (i : Fin n) :
    Except String (StructDef TargetSet n i F) := do
  let source := m.structs i
  let compute ← lowerFunc s!"{source.name}::oracle-erasure/compute" source.compute
  let constrain ← lowerFunc s!"{source.name}::oracle-erasure/constrain" source.constrain
  pure {
    name := source.name
    members := source.members
    compute := compute
    constrain := constrain
  }

theorem lowerStruct_fields {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) (i : Fin n)
    (out : StructDef TargetSet n i F)
    (hlower : lowerStruct m i = .ok out) :
    out.members = (m.structs i).members ∧
      out.constrain.numParams = (m.structs i).constrain.numParams ∧
      HEq out.constrain.body (lowerBody (m.structs i).constrain.body) := by
  change (do
    let compute ← lowerFunc
      s!"{(m.structs i).name}::oracle-erasure/compute" (m.structs i).compute
    let constrain ← lowerFunc
      s!"{(m.structs i).name}::oracle-erasure/constrain" (m.structs i).constrain
    pure ({
      name := (m.structs i).name
      members := (m.structs i).members
      compute := compute
      constrain := constrain
    } : StructDef TargetSet n i F)) = .ok out at hlower
  cases hcompute : lowerFunc
      s!"{(m.structs i).name}::oracle-erasure/compute"
      (m.structs i).compute with
  | error error =>
    rw [hcompute] at hlower
    change (Except.error error : Except String (StructDef TargetSet n i F)) =
      .ok out at hlower
    cases hlower
  | ok compute =>
    rw [hcompute] at hlower
    cases hconstrain : lowerFunc
        s!"{(m.structs i).name}::oracle-erasure/constrain"
        (m.structs i).constrain with
    | error error =>
      rw [hconstrain] at hlower
      change (Except.error error : Except String (StructDef TargetSet n i F)) =
        .ok out at hlower
      cases hlower
    | ok constrain =>
      rw [hconstrain] at hlower
      change Except.ok ({
        name := (m.structs i).name
        members := (m.structs i).members
        compute := compute
        constrain := constrain
      } : StructDef TargetSet n i F) = .ok out at hlower
      have hout := Except.ok.inj hlower
      subst out
      exact ⟨rfl, (lowerFunc_fields _ _ _ hconstrain).1,
        heq_of_eq (lowerFunc_fields _ _ _ hconstrain).2.1⟩

/-- Fields used by direct constraint observation are unchanged by Oracle
projection. -/
theorem lowerStruct_semantic_fields {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) (i : Fin n)
    (out : StructDef TargetSet n i F)
    (hlower : lowerStruct m i = .ok out) :
    out.members = (m.structs i).members ∧
      out.compute.numParams = (m.structs i).compute.numParams ∧
      out.constrain.numParams = (m.structs i).constrain.numParams ∧
      out.constrain.returnVar = (m.structs i).constrain.returnVar ∧
      HEq out.constrain.body (lowerBody (m.structs i).constrain.body) := by
  change (do
    let compute ← lowerFunc
      s!"{(m.structs i).name}::oracle-erasure/compute" (m.structs i).compute
    let constrain ← lowerFunc
      s!"{(m.structs i).name}::oracle-erasure/constrain" (m.structs i).constrain
    pure ({
      name := (m.structs i).name
      members := (m.structs i).members
      compute := compute
      constrain := constrain
    } : StructDef TargetSet n i F)) = .ok out at hlower
  cases hcompute : lowerFunc
      s!"{(m.structs i).name}::oracle-erasure/compute"
      (m.structs i).compute with
  | error error =>
    rw [hcompute] at hlower
    change (Except.error error : Except String (StructDef TargetSet n i F)) =
      .ok out at hlower
    cases hlower
  | ok compute =>
    rw [hcompute] at hlower
    cases hconstrain : lowerFunc
        s!"{(m.structs i).name}::oracle-erasure/constrain"
        (m.structs i).constrain with
    | error error =>
      rw [hconstrain] at hlower
      change (Except.error error : Except String (StructDef TargetSet n i F)) =
        .ok out at hlower
      cases hlower
    | ok constrain =>
      rw [hconstrain] at hlower
      change Except.ok ({
        name := (m.structs i).name
        members := (m.structs i).members
        compute := compute
        constrain := constrain
      } : StructDef TargetSet n i F) = .ok out at hlower
      have hout := Except.ok.inj hlower
      subst out
      have hc := lowerFunc_fields _ _ _ hcompute
      have hk := lowerFunc_fields _ _ _ hconstrain
      exact ⟨rfl, hc.1, hk.1, hk.2.2, heq_of_eq hk.2.1⟩

private structure LoweredPrefix {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) (k : Nat) where
  structs : ∀ j : Fin n, j.val < k → StructDef TargetSet n j F
  lower_eq : ∀ (j : Fin n) (hj : j.val < k),
    lowerStruct m j = .ok (structs j hj)

private def lowerStructsRec {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) (k : Nat) (hk : k ≤ n) :
    Except String (LoweredPrefix m k) := do
  match k with
  | 0 => pure {
      structs := fun _ h => absurd h (Nat.not_lt_zero _)
      lower_eq := fun _ h => absurd h (Nat.not_lt_zero _)
    }
  | k' + 1 =>
    let previous ← lowerStructsRec m k' (Nat.le_of_succ_le hk)
    let hk' : k' < n := hk
    match hcurrent : lowerStruct m ⟨k', hk'⟩ with
    | .error error => .error error
    | .ok current => pure {
        structs := fun j hj =>
          if hjk : j.val < k' then previous.structs j hjk
          else
            have hval : j.val = k' := by omega
            have heq : j = ⟨k', hk'⟩ := Fin.ext hval
            heq ▸ current
        lower_eq := by
          intro j hj
          by_cases hjk : j.val < k'
          · simpa [hjk] using previous.lower_eq j hjk
          · have hval : j.val = k' := by omega
            have heq : j = ⟨k', hk'⟩ := Fin.ext hval
            subst j
            simpa [hjk] using hcurrent
      }

def lowerModule {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) : Except String (Module TargetSet n F) := do
  let lowered ← lowerStructsRec m n le_rfl
  pure { structs := fun i => lowered.structs i i.isLt }

theorem lowerModule_struct {n : Nat} {F : Type} [OfNat F 0]
    (m : Module SourceSet n F) (out : Module TargetSet n F)
    (hlower : lowerModule m = .ok out) (i : Fin n) :
    lowerStruct m i = .ok (out.structs i) := by
  unfold lowerModule at hlower
  cases hrec : lowerStructsRec m n le_rfl with
  | error error =>
    rw [hrec] at hlower
    change (Except.error error : Except String (Module TargetSet n F)) =
      .ok out at hlower
    cases hlower
  | ok lowered =>
    rw [hrec] at hlower
    change Except.ok ({ structs := fun i => lowered.structs i i.isLt } :
      Module TargetSet n F) = .ok out at hlower
    have hout := Except.ok.inj hlower
    subst out
    exact lowered.lower_eq i i.isLt

private theorem evalProjectedBodyIn_heq [Field F] [DecidableEq F]
    {n a b : Nat} (out : Module TargetSet n F) (i : Fin n)
    (state : TypedSourceSemantics.State F)
    (left : List (Stmt TargetSet ⟨n, i.val, a⟩ F))
    (right : List (Stmt TargetSet ⟨n, i.val, b⟩ F))
    (hab : a = b) (hbody : HEq left right) :
    TypedSourceSemantics.evalProjectedBodyIn out i state left =
      TypedSourceSemantics.evalProjectedBodyIn out i state right := by
  subst b
  rw [eq_of_heq hbody]

/-- Oracle projection preserves direct constraint execution. The impossible
Oracle branch is discharged from `FuncDef.wf_caps`, including recursively
entered callees. -/
theorem evalBody_lowerBody [Field F] [DecidableEq F] {n : Nat}
    (m : Module SourceSet n F) (out : Module TargetSet n F)
    (hlower : lowerModule m = .ok out) (i : Fin n)
    (state : TypedSourceSemantics.State F)
    (body : List (Stmt SourceSet
      ⟨n, i.val, (m.structs i).members.length⟩ F))
    (hfree : OracleFreeBody body) :
    TypedSourceSemantics.evalBody m i state body =
      TypedSourceSemantics.evalProjectedBodyIn out i state (lowerBody body) :=
  match body with
  | [] => by
      rw [TypedSourceSemantics.evalBody.eq_def,
        TypedSourceSemantics.evalProjectedBodyIn.eq_def]
      rfl
  | .op d payload :: rest => by
      rcases d with ⟨index, hindex⟩
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
        simp [SourceSet, LLZK.DialectLowering.WitnessSourceSet] at hindex
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · cases payload with
        | call dest target selector args =>
          by_cases hsel : selector = 0
          · let j := Call.moduleTarget target i.isLt
            let calleeState : TypedSourceSemantics.State F := {
              values := TypedSourceSemantics.bindValues state.values args
              objects := TypedSourceSemantics.bindObjects state.objects args
              witness := state.witness
              nextPath := state.nextPath
            }
            have hstruct := lowerModule_struct m out hlower j
            have hfields := lowerStruct_semantic_fields m j (out.structs j) hstruct
            have hcalleeLower := evalBody_lowerBody m out hlower j calleeState
              (m.structs j).constrain.body
              (constrain_body_oracleFree (m.structs j).constrain)
            have hbody := evalProjectedBodyIn_heq out j calleeState
              (out.structs j).constrain.body
              (lowerBody (m.structs j).constrain.body)
              (congrArg List.length hfields.1) hfields.2.2.2.2
            have hresult :
                TypedSourceSemantics.evalBody m j calleeState
                    (m.structs j).constrain.body =
                  TypedSourceSemantics.evalProjectedBodyIn out j calleeState
                    (out.structs j).constrain.body :=
              hcalleeLower.trans hbody.symm
            rw [TypedSourceSemantics.evalBody.eq_def,
              TypedSourceSemantics.evalProjectedBodyIn.eq_def]
            dsimp only [lowerBody]
            simp only [hsel, ↓reduceIte]
            change _ = _
            rw [show Call.moduleTarget target i.isLt = j from rfl]
            rw [show ({
              values := TypedSourceSemantics.bindValues state.values args
              objects := TypedSourceSemantics.bindObjects state.objects args
              witness := state.witness
              nextPath := state.nextPath
            } : TypedSourceSemantics.State F) = calleeState from rfl]
            rw [hresult, hfields.2.2.2.1]
            rw [evalBody_lowerBody m out hlower i _ rest hfree.tail]
          · rw [TypedSourceSemantics.evalBody.eq_def,
              TypedSourceSemantics.evalProjectedBodyIn.eq_def]
            dsimp only [lowerBody]
            simp only [hsel, ↓reduceIte]
            rw [evalBody_lowerBody m out hlower i state rest hfree.tail]
      · rw [TypedSourceSemantics.evalBody.eq_def,
          TypedSourceSemantics.evalProjectedBodyIn.eq_def]
        dsimp only [lowerBody]
        change
          (let step := TypedSourceSemantics.evalLeaf
            (.op ⟨0, by simp⟩ payload) state
          let tail := TypedSourceSemantics.evalBody m i step.1 rest
          (tail.1, step.2 && tail.2)) =
          (let step := TypedSourceSemantics.evalProjectedLeaf
            (.op ⟨0, by simp⟩ payload) state
          let tail := TypedSourceSemantics.evalProjectedBodyIn out i step.1
            (lowerBody rest)
          (tail.1, step.2 && tail.2))
        dsimp only [TypedSourceSemantics.evalLeaf,
          TypedSourceSemantics.evalProjectedLeaf]
        rw [evalBody_lowerBody m out hlower i
          (StructObject.apply payload state) rest hfree.tail]
      · exact False.elim (hfree payload (by simp [oracleSourceIx]))
      · rw [TypedSourceSemantics.evalBody.eq_def,
          TypedSourceSemantics.evalProjectedBodyIn.eq_def]
        dsimp only [lowerBody]
        change
          (let step := TypedSourceSemantics.evalLeaf
            (.op ⟨2, by simp⟩ payload) state
          let tail := TypedSourceSemantics.evalBody m i step.1 rest
          (tail.1, step.2 && tail.2)) =
          (let step := TypedSourceSemantics.evalProjectedLeaf
            (.op ⟨1, by simp⟩ payload) state
          let tail := TypedSourceSemantics.evalProjectedBodyIn out i step.1
            (lowerBody rest)
          (tail.1, step.2 && tail.2))
        dsimp only [TypedSourceSemantics.evalLeaf,
          TypedSourceSemantics.evalProjectedLeaf]
        rw [evalBody_lowerBody m out hlower i
          ({ state with values := Felt.applyOp payload state.values })
          rest hfree.tail]
      · rw [TypedSourceSemantics.evalBody.eq_def,
          TypedSourceSemantics.evalProjectedBodyIn.eq_def]
        dsimp only [lowerBody]
        change
          (let step := TypedSourceSemantics.evalLeaf
            (.op ⟨3, by simp⟩ payload) state
          let tail := TypedSourceSemantics.evalBody m i step.1 rest
          (tail.1, step.2 && tail.2)) =
          (let step := TypedSourceSemantics.evalProjectedLeaf
            (.op ⟨2, by simp⟩ payload) state
          let tail := TypedSourceSemantics.evalProjectedBodyIn out i step.1
            (lowerBody rest)
          (tail.1, step.2 && tail.2))
        dsimp only [TypedSourceSemantics.evalLeaf,
          TypedSourceSemantics.evalProjectedLeaf]
        cases payload with
        | eq left right =>
          rw [evalBody_lowerBody m out hlower i state rest hfree.tail]
termination_by (i.val, body.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Pointwise Oracle-prefix certificate for one selected typed entry. -/
theorem checkAt_eq_checkProjectedAt [Field F] [DecidableEq F] {n : Nat}
    (m : Module SourceSet n F) (out : Module TargetSet n F)
    (hlower : lowerModule m = .ok out) (entry : Fin n)
    (inputs objects : List F) :
    TypedSourceSemantics.checkAt m entry inputs objects =
      TypedSourceSemantics.checkProjectedAt out entry inputs objects := by
  have hstruct := lowerModule_struct m out hlower entry
  have hfields := lowerStruct_semantic_fields m entry (out.structs entry) hstruct
  let initial := TypedSourceSemantics.initialState
    (m.structs entry).constrain.numParams (m.structs entry).compute.numParams
    inputs objects
  have hlowered := evalBody_lowerBody m out hlower entry initial
    (m.structs entry).constrain.body
    (constrain_body_oracleFree (m.structs entry).constrain)
  have hbody := evalProjectedBodyIn_heq out entry initial
    (out.structs entry).constrain.body
    (lowerBody (m.structs entry).constrain.body)
    (congrArg List.length hfields.1) hfields.2.2.2.2
  have heval := hlowered.trans hbody.symm
  unfold TypedSourceSemantics.checkAt TypedSourceSemantics.checkProjectedAt
  dsimp only
  rw [hfields.2.1, hfields.2.2.1]
  change _ = (TypedSourceSemantics.evalProjectedBodyIn out entry initial
    (out.structs entry).constrain.body).2
  exact congrArg Prod.snd heval

end Dialect.OracleErasure
