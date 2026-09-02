/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.ObjectResidualSemantics
import Heyting.Dialects.CallSemantics
import Heyting.Dialects.TypedSourceSemantics
import Heyting.Core.VarIdEncoding

/-!
# StructObject erasure

Call-free lowering

```text
[StructObject, Felt, ConstrainEq] → [Felt, ConstrainEq]
```

Object identities remain compile-time instance paths. A member read aliases
its destination to a dedicated initial witness local identified by the
bijection `VarIdEncoding.encode (path, member)`. Existing non-parameter SSA
locals are shifted above that witness range, so the two namespaces cannot
collide. No object identity is represented by a field value.
-/

namespace Dialect.StructObjectPass

open Dialect

abbrev SourceSet := ObjectResidualSemantics.Set
abbrev TargetSet := CallPass.TargetSet

private abbrev feltTargetIx : Fin TargetSet.length :=
  ⟨0, by simp [TargetSet, CallPass.TargetSet]⟩
private abbrev constrainTargetIx : Fin TargetSet.length :=
  ⟨1, by simp [TargetSet, CallPass.TargetSet]⟩

abbrev AliasEnv := LocalVar → Option LocalVar

def AliasEnv.empty : AliasEnv := fun _ => none
def AliasEnv.update (aliases : AliasEnv) (source target : LocalVar) : AliasEnv :=
  fun v => if v = source then some target else aliases v

structure StaticState where
  objects : StructObject.ObjEnv
  aliases : AliasEnv
  nextPath : Nat

def StaticState.initial : StaticState where
  objects := fun _ => []
  aliases := AliasEnv.empty
  nextPath := 0

def allocatePath (nextPath : Nat) : StructObject.InstancePath :=
  if nextPath == 0 then [] else [nextPath]

def encodedMember (path : StructObject.InstancePath) (member : Nat) : Nat :=
  VarIdEncoding.encode (path, member)

/-- Number of witness parameters needed by a body. This is one past the
largest encoded member position encountered under static path execution. -/
def witnessSpan {n i numMembers : Nat} {F : Type} :
    StructObject.ObjEnv → Nat →
    List (Stmt SourceSet ⟨n, i, numMembers⟩ F) → Nat
  | _, _, [] => 0
  | objects, nextPath, .op d payload :: rest =>
    match d with
    | ⟨0, _⟩ =>
      match payload with
      | .newStruct dest =>
        witnessSpan
          (StructObject.ObjEnv.update objects dest (allocatePath nextPath))
          (nextPath + 1) rest
      | .readMember dest self member =>
        let path := objects self
        max (encodedMember path member.val + 1)
          (witnessSpan
            (StructObject.ObjEnv.update objects dest (path ++ [member.val]))
            nextPath rest)
      | .writeMember _ _ _ => witnessSpan objects nextPath rest
    | ⟨1, _⟩ => witnessSpan objects nextPath rest
    | ⟨2, _⟩ => witnessSpan objects nextPath rest

def funcVarBound {n i numMembers : Nat} {F : Type} {kind : Capability}
    (fn : FuncDef SourceSet n i F kind numMembers) : LocalVar :=
  max fn.numParams
    (max (maxVarBody fn.body) (Option.getD (fn.returnVar.map (fun v => v + 1)) 0))

/-- Rename ordinary locals around the newly inserted witness-parameter range. -/
def baseRename (numParams span : Nat) (v : LocalVar) : LocalVar :=
  if v < numParams then v else v + span

def renameLocal (numParams span : Nat) (aliases : AliasEnv)
    (v : LocalVar) : LocalVar :=
  (aliases v).getD (baseRename numParams span v)

def witnessLocal (numParams : Nat) (path : StructObject.InstancePath)
    (member : Nat) : LocalVar :=
  numParams + encodedMember path member

/-- Erase one body while interpreting object paths statically. -/
def lowerBody {n i numMembers : Nat} {F : Type}
    (numParams span : Nat) :
    StaticState → List (Stmt SourceSet ⟨n, i, numMembers⟩ F) →
      List (Stmt TargetSet ⟨n, i, numMembers⟩ F) × StaticState
  | state, [] => ([], state)
  | state, .op d payload :: rest =>
    match d with
    | ⟨0, _⟩ =>
      match payload with
      | .newStruct dest =>
        let state' := { state with
          objects := StructObject.ObjEnv.update state.objects dest
            (allocatePath state.nextPath)
          nextPath := state.nextPath + 1 }
        lowerBody numParams span state' rest
      | .readMember dest self member =>
        let path := state.objects self
        let slot := witnessLocal numParams path member.val
        let state' := { state with
          objects := StructObject.ObjEnv.update state.objects dest (path ++ [member.val])
          aliases := AliasEnv.update state.aliases dest slot }
        lowerBody numParams span state' rest
      | .writeMember _ _ _ => lowerBody numParams span state rest
    | ⟨1, _⟩ =>
      let rename := renameLocal numParams span state.aliases
      let lowered : Stmt TargetSet ⟨n, i, numMembers⟩ F :=
        .op feltTargetIx (Felt.sig.mapVars rename payload)
      let tail := lowerBody numParams span state rest
      (lowered :: tail.1, tail.2)
    | ⟨2, _⟩ =>
      let rename := renameLocal numParams span state.aliases
      let lowered : Stmt TargetSet ⟨n, i, numMembers⟩ F :=
        .op constrainTargetIx (ConstrainEq.sig.mapVars rename payload)
      let tail := lowerBody numParams span state rest
      (lowered :: tail.1, tail.2)

/-! ## Direct StructObject lowering semantics -/

/-- Constraint semantics at object-erasure target, including backend validity
for division. This mirrors exact FlatIR observation used by Phase 13. -/
def evalTargetStmt [Field F] {ctx : OpCtx} :
    Stmt TargetSet ctx F → (LocalVar → F) → (LocalVar → F) × Prop
  | .op ⟨0, _⟩ op, env =>
      (Felt.applyOp op env, Felt.backendValid op env)
  | .op ⟨1, _⟩ op, env =>
      match op with
      | .eq left right => (env, env left = env right)

def evalTargetBody [Field F] {ctx : OpCtx} :
    List (Stmt TargetSet ctx F) → (LocalVar → F) → (LocalVar → F) × Prop
  | [], env => (env, True)
  | stmt :: rest, env =>
      let step := evalTargetStmt stmt env
      let tail := evalTargetBody rest step.1
      (tail.1, step.2 ∧ tail.2)

@[simp] theorem evalTargetStmt_felt [Field F] {ctx : OpCtx}
    (op : Felt.Op ctx F) (env : LocalVar → F) :
    evalTargetStmt (.op feltTargetIx op) env =
      (Felt.applyOp op env, Felt.backendValid op env) := rfl

@[simp] theorem evalTargetStmt_felt_any [Field F] {ctx : OpCtx}
    (h : 0 < TargetSet.length) (op : Felt.Op ctx F) (env : LocalVar → F) :
    evalTargetStmt (.op ⟨0, h⟩ op) env =
      (Felt.applyOp op env, Felt.backendValid op env) := rfl

@[simp] theorem evalTargetStmt_constrain [Field F] {ctx : OpCtx}
    (left right : LocalVar) (env : LocalVar → F) :
    evalTargetStmt (.op constrainTargetIx
      (.eq left right : ConstrainEq.Op ctx F)) env =
      (env, env left = env right) := rfl

@[simp] theorem evalTargetStmt_constrain_any [Field F] {ctx : OpCtx}
    (h : 1 < TargetSet.length) (left right : LocalVar) (env : LocalVar → F) :
    evalTargetStmt (.op ⟨1, h⟩
      (.eq left right : ConstrainEq.Op ctx F)) env =
      (env, env left = env right) := rfl

def extendDefined (defined : LocalVar → Bool) (dest : Option LocalVar) :
    LocalVar → Bool :=
  match dest with
  | none => defined
  | some d => fun v => defined v || v == d

def AliasesDefined (defined : LocalVar → Bool) (aliases : AliasEnv) : Prop :=
  ∀ source target, aliases source = some target → defined source = true

def AliasesInRange (numParams span : Nat) (aliases : AliasEnv) : Prop :=
  ∀ source target, aliases source = some target →
    numParams ≤ target ∧ target < numParams + span

def ParamsDefined (numParams : Nat) (defined : LocalVar → Bool) : Prop :=
  ∀ v, v < numParams → defined v = true

/-- Dynamic source state, static alias/path state, and erased field state
agree on every currently defined SSA local and reachable object coordinate. -/
structure LowerStateRel [Field F] (numParams span : Nat)
    (defined : LocalVar → Bool) (static : StaticState)
    (source : StructObject.State F) (target : LocalVar → F) : Prop where
  values : CallSemantics.EnvAgreesOn defined
    (renameLocal numParams span static.aliases) source.values target
  objects : static.objects = source.objects
  nextPath : static.nextPath = source.nextPath
  witness : ∀ key, encodedMember key.1 key.2 < span →
    target (witnessLocal numParams key.1 key.2) = source.witness key
  aliasesDefined : AliasesDefined defined static.aliases
  aliasesInRange : AliasesInRange numParams span static.aliases
  paramsDefined : ParamsDefined numParams defined

theorem alias_none_of_fresh [Field F] {numParams span : Nat}
    {defined : LocalVar → Bool} {static : StaticState}
    {source : StructObject.State F} {target : LocalVar → F}
    (rel : LowerStateRel numParams span defined static source target)
    {dest : LocalVar} (hfresh : defined dest = false) :
    static.aliases dest = none := by
  cases h : static.aliases dest with
  | none => rfl
  | some slot =>
      have := rel.aliasesDefined dest slot h
      rw [hfresh] at this
      contradiction

theorem renameLocal_fresh_separate [Field F] {numParams span : Nat}
    {defined : LocalVar → Bool} {static : StaticState}
    {source : StructObject.State F} {target : LocalVar → F}
    (rel : LowerStateRel numParams span defined static source target)
    {dest : LocalVar} (hfresh : defined dest = false) :
    ∀ v, v ≠ dest →
      renameLocal numParams span static.aliases v ≠
        renameLocal numParams span static.aliases dest := by
  have hdestGe : numParams ≤ dest := by
    apply Nat.le_of_not_gt
    intro hlt
    have := rel.paramsDefined dest hlt
    rw [hfresh] at this
    contradiction
  have hdestAlias := alias_none_of_fresh rel hfresh
  have hdestRename : renameLocal numParams span static.aliases dest = dest + span := by
    simp [renameLocal, hdestAlias, baseRename, Nat.not_lt.mpr hdestGe]
  intro v hv
  rw [hdestRename]
  cases halias : static.aliases v with
  | some slot =>
      have hrange := rel.aliasesInRange v slot halias
      simp only [renameLocal, halias, Option.getD_some]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hrange.2
        (Nat.add_le_add_right hdestGe span))
  | none =>
      simp only [renameLocal, halias, Option.getD_none]
      by_cases hvParam : v < numParams
      · rw [baseRename, if_pos hvParam]
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvParam
          (Nat.le_trans hdestGe (Nat.le_add_right dest span)))
      · rw [baseRename, if_neg hvParam]
        intro heq
        exact hv (Nat.add_right_cancel heq)

theorem isSSA_cons_dest_fresh {ctx : OpCtx} {F : Type}
    (defined : LocalVar → Bool) (stmt : Stmt SourceSet ctx F)
    (rest : List (Stmt SourceSet ctx F)) (dest : LocalVar)
    (hssa : isSSA defined (stmt :: rest) = true)
    (hdest : stmt.dest = some dest) : defined dest = false := by
  simp only [isSSA] at hssa
  rw [hdest] at hssa
  simp only [Bool.and_eq_true] at hssa
  simpa using hssa.2.1

theorem capsLE_tail {ctx : OpCtx} {F : Type} {kind : Capability}
    {head : Stmt SourceSet ctx F} {tail : List (Stmt SourceSet ctx F)}
    (hcap : capsLE kind (head :: tail) = true) : capsLE kind tail = true := by
  apply List.all_eq_true.mpr
  intro stmt hmem
  exact (List.all_eq_true.mp hcap) stmt (by simp [hmem])

set_option linter.flexible false in
theorem lowerBody_simulation [Field F]
    {n i numMembers numParams span : Nat}
    (body : List (Stmt SourceSet ⟨n, i, numMembers⟩ F))
    (defined : LocalVar → Bool) (static : StaticState)
    (source : StructObject.State F) (target : LocalVar → F)
    (hssa : isSSA defined body = true)
    (hcaps : capsLE .constraint body = true)
    (hspan : witnessSpan static.objects static.nextPath body ≤ span)
    (rel : LowerStateRel numParams span defined static source target) :
    let lowered := lowerBody numParams span static body
    let sourceResult := ObjectResidualSemantics.evalBody body source
    let targetResult := evalTargetBody lowered.1 target
    (targetResult.2 ↔ sourceResult.2) ∧
      LowerStateRel numParams span
        (CallPass.definedLocalsAfter defined body) lowered.2
        sourceResult.1 targetResult.1 := by
  induction body generalizing defined static source target with
  | nil =>
      change (True ↔ True) ∧ LowerStateRel numParams span defined static source target
      exact ⟨Iff.rfl, rel⟩
  | cons stmt rest ih =>
      have hparts := CallPass.isSSA_cons_parts defined stmt rest hssa
      have htailCaps := capsLE_tail hcaps
      cases stmt with
      | op d payload =>
        rcases d with ⟨index, hindex⟩
        have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by
          simp [SourceSet, ObjectResidualSemantics.Set] at hindex
          omega
        rcases hcases with rfl | rfl | rfl
        · cases payload with
          | newStruct dest =>
              have hcap := Dialect.cap_le_of_capsLE hcaps
                (stmt := (Stmt.op ⟨0, hindex⟩
                  (.newStruct dest) : Stmt SourceSet ⟨n, i, numMembers⟩ F))
                (by simp)
              change Capability.witness = .pure ∨
                Capability.witness = .constraint at hcap
              contradiction
          | writeMember self member src =>
              have hcap := Dialect.cap_le_of_capsLE hcaps
                (stmt := (Stmt.op ⟨0, hindex⟩
                  (.writeMember self member src) :
                    Stmt SourceSet ⟨n, i, numMembers⟩ F)) (by simp)
              change Capability.witness = .pure ∨
                Capability.witness = .constraint at hcap
              contradiction
          | readMember dest self member =>
              let path := static.objects self
              let slot := witnessLocal numParams path member.val
              let static' : StaticState := {
                static with
                objects := StructObject.ObjEnv.update static.objects dest
                  (path ++ [member.val])
                aliases := AliasEnv.update static.aliases dest slot }
              let source' := StructObject.apply
                (.readMember dest self member) source
              let defined' := extendDefined defined (some dest)
              have hfresh : defined dest = false :=
                isSSA_cons_dest_fresh defined
                  (.op ⟨0, hindex⟩ (.readMember dest self member)) rest dest hssa rfl
              have hspanHead : encodedMember path member.val < span := by
                change max (encodedMember path member.val + 1)
                  (witnessSpan
                    (StructObject.ObjEnv.update static.objects dest
                      (path ++ [member.val])) static.nextPath rest) ≤ span at hspan
                omega
              have hspanTail : witnessSpan static'.objects static'.nextPath rest ≤ span := by
                change max (encodedMember path member.val + 1)
                  (witnessSpan
                    (StructObject.ObjEnv.update static.objects dest
                      (path ++ [member.val])) static.nextPath rest) ≤ span at hspan
                change witnessSpan
                  (StructObject.ObjEnv.update static.objects dest
                    (path ++ [member.val])) static.nextPath rest ≤ span
                omega
              have hrel' : LowerStateRel numParams span defined' static' source' target := by
                constructor
                · intro v hv
                  change (defined v || v == dest) = true at hv
                  simp only [Bool.or_eq_true, beq_iff_eq] at hv
                  rcases hv with hv | rfl
                  · have hvne : v ≠ dest := by
                      intro heq
                      subst v
                      rw [hfresh] at hv
                      contradiction
                    simpa [static', source', path, slot, renameLocal,
                      AliasEnv.update, hvne, StructObject.apply,
                      StructObject.ValueEnv.update] using rel.values v hv
                  · have hw := rel.witness (path, member.val) hspanHead
                    simpa [static', source', path, slot, renameLocal,
                      AliasEnv.update, StructObject.apply,
                      StructObject.ValueEnv.update, rel.objects] using hw
                · funext v
                  by_cases hv : v = dest
                  · subst v
                    simp [static', source', path, StructObject.apply,
                      StructObject.ObjEnv.update, rel.objects]
                  · simp [static', source', StructObject.apply,
                      StructObject.ObjEnv.update, hv, rel.objects]
                · simpa [static', source', StructObject.apply] using rel.nextPath
                · intro key hkey
                  simpa [source', StructObject.apply] using rel.witness key hkey
                · intro v assigned halias
                  by_cases hv : v = dest
                  · subst v
                    simp [static', AliasEnv.update] at halias
                    change (defined dest || dest == dest) = true
                    simp
                  · simp [static', AliasEnv.update, hv] at halias
                    have := rel.aliasesDefined v assigned halias
                    change (defined v || v == dest) = true
                    rw [this]
                    simp
                · intro v assigned halias
                  by_cases hv : v = dest
                  · subst v
                    simp [static', AliasEnv.update] at halias
                    subst assigned
                    exact ⟨Nat.le_add_right numParams _, by
                      simpa [slot, witnessLocal] using
                        (Nat.add_lt_add_left hspanHead numParams)⟩
                  · simp [static', AliasEnv.update, hv] at halias
                    exact rel.aliasesInRange v assigned halias
                · intro v hv
                  change (defined v || v == dest) = true
                  rw [rel.paramsDefined v hv]
                  simp
              have htailSSA : isSSA defined' rest = true := by
                simpa [defined', extendDefined] using hparts.2
              have htail := ih defined' static' source' target htailSSA
                htailCaps hspanTail hrel'
              simpa [lowerBody, evalTargetBody, ObjectResidualSemantics.evalBody,
                ObjectResidualSemantics.evalStmt, static', source', defined', path,
                slot, CallPass.definedLocalsAfter, extendDefined] using htail
        · let rename := renameLocal numParams span static.aliases
          have hreads : (Felt.reads payload).all defined = true := by
            simpa [SourceSet, ObjectResidualSemantics.Set] using hparts.1
          have hfresh : defined (Felt.destVar payload) = false :=
            isSSA_cons_dest_fresh defined
              (.op ⟨1, hindex⟩ payload) rest (Felt.destVar payload) hssa
              (by simpa [SourceSet, ObjectResidualSemantics.Set] using Felt.dest_eq payload)
          have hstmtDest :
              (Stmt.op ⟨1, hindex⟩ payload :
                Stmt SourceSet ⟨n, i, numMembers⟩ F).dest =
                some (Felt.destVar payload) := by
            simpa [SourceSet, ObjectResidualSemantics.Set] using Felt.dest_eq payload
          rw [hstmtDest] at hparts
          have hseparate : ∀ v, v ≠ Felt.destVar payload →
              rename v ≠ rename (Felt.destVar payload) :=
            renameLocal_fresh_separate rel hfresh
          have hvalues := CallSemantics.applyOp_lowerFeltOp_agreesOn
            (γ' := ⟨n, i, numMembers⟩) defined rename payload source.values target
            hreads rel.values hseparate
          have hvalid : Felt.backendValid (Felt.mapVars rename payload) target ↔
              Felt.backendValid payload source.values :=
            Felt.backendValid_mapVars rename payload source.values target (by
              intro v hv
              exact rel.values v ((List.all_eq_true.mp hreads) v hv))
          let defined' := extendDefined defined (some (Felt.destVar payload))
          let source' : StructObject.State F :=
            { source with values := Felt.applyOp payload source.values }
          let target' := Felt.applyOp (Felt.mapVars rename payload) target
          have hrel' : LowerStateRel numParams span defined' static source' target' := by
            constructor
            · simpa [defined', extendDefined, source', target', rename,
                CallPass.lowerFeltOp] using hvalues
            · exact rel.objects
            · exact rel.nextPath
            · intro key hkey
              have hslotNe : witnessLocal numParams key.1 key.2 ≠
                  rename (Felt.destVar payload) := by
                have hrange : witnessLocal numParams key.1 key.2 < numParams + span := by
                  simpa [witnessLocal] using Nat.add_lt_add_left hkey numParams
                have hdestGe : numParams ≤ Felt.destVar payload := by
                  apply Nat.le_of_not_gt
                  intro hlt
                  have := rel.paramsDefined _ hlt
                  rw [hfresh] at this
                  contradiction
                have hdestAlias := alias_none_of_fresh rel hfresh
                have hrename : rename (Felt.destVar payload) =
                    Felt.destVar payload + span := by
                  simp [rename, renameLocal, hdestAlias, baseRename,
                    Nat.not_lt.mpr hdestGe]
                rw [hrename]
                exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hrange
                  (Nat.add_le_add_right hdestGe span))
              have hdestMap : Felt.destVar (Felt.mapVars rename payload) =
                  rename (Felt.destVar payload) := by
                cases payload <;> rfl
              change Felt.applyOp (Felt.mapVars rename payload) target
                  (witnessLocal numParams key.1 key.2) = source.witness key
              rw [Felt.applyOp_at_other _ _ _ (by
                rw [hdestMap]
                exact hslotNe)]
              exact rel.witness key hkey
            · intro v assigned halias
              change (defined v || v == Felt.destVar payload) = true
              rw [rel.aliasesDefined v assigned halias]
              simp
            · exact rel.aliasesInRange
            · intro v hv
              simp [defined', extendDefined, rel.paramsDefined v hv]
          have htailSSA : isSSA defined' rest = true := by
            change isSSA (fun v => defined v || v == Felt.destVar payload) rest = true
            exact hparts.2
          have htailSpan : witnessSpan static.objects static.nextPath rest ≤ span := by
            simpa [witnessSpan] using hspan
          have htail := ih defined' static source' target' htailSSA htailCaps
            htailSpan hrel'
          constructor
          · simpa [lowerBody, evalTargetBody,
              ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
              rename, source', target'] using and_congr hvalid htail.1
          · simpa only [CallPass.definedLocalsAfter, hstmtDest, lowerBody,
              evalTargetBody, evalTargetStmt_felt,
              ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
              defined', extendDefined, source', target', rename]
              using htail.2
        · cases payload with
          | eq left right =>
              let rename := renameLocal numParams span static.aliases
              have hleftDefined : defined left = true := by
                apply (List.all_eq_true.mp hparts.1) left
                change left ∈ [left, right]
                simp
              have hrightDefined : defined right = true := by
                apply (List.all_eq_true.mp hparts.1) right
                change right ∈ [left, right]
                simp
              have hleft : target (rename left) = source.values left :=
                rel.values left hleftDefined
              have hright : target (rename right) = source.values right :=
                rel.values right hrightDefined
              have htailSSA : isSSA defined rest = true := by
                simpa [SourceSet, ObjectResidualSemantics.Set,
                  ConstrainEq.dest] using hparts.2
              have htailSpan : witnessSpan static.objects static.nextPath rest ≤ span := by
                simpa [witnessSpan] using hspan
              have htail := ih defined static source target htailSSA htailCaps
                htailSpan rel
              constructor
              · have htruth :
                    (target (rename left) = target (rename right) ∧
                      (evalTargetBody
                        (lowerBody numParams span static rest).1 target).2) ↔
                    (source.values left = source.values right ∧
                      (ObjectResidualSemantics.evalBody rest source).2) := by
                    constructor
                    · rintro ⟨heq, hrest⟩
                      exact ⟨by simpa [hleft, hright] using heq, htail.1.mp hrest⟩
                    · rintro ⟨heq, hrest⟩
                      exact ⟨by simpa [hleft, hright] using heq, htail.1.mpr hrest⟩
                simpa [lowerBody, evalTargetBody, evalTargetStmt,
                  ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
                  rename] using htruth
              · simpa [lowerBody, evalTargetBody, evalTargetStmt,
                  ObjectResidualSemantics.evalBody, ObjectResidualSemantics.evalStmt,
                  rename, CallPass.definedLocalsAfter, SourceSet,
                  ObjectResidualSemantics.Set, ConstrainEq.dest] using htail.2
def certifyFunc {n i numMembers : Nat} {F : Type} {kind : Capability}
    (numParams : Nat) (body : List (Stmt TargetSet ⟨n, i, numMembers⟩ F))
    (returnVar : Option LocalVar) :
    Option (FuncDef TargetSet n i F kind numMembers) :=
  if hcaps : capsLE kind body = true then
    if hssa : isSSA (fun v => decide (v < numParams)) body = true then
      some {
        numParams := numParams
        body := body
        returnVar := returnVar
        wf_caps := hcaps
        wf_ssa := hssa
      }
    else none
  else none

def lowerFunc {n i numMembers : Nat} {F : Type} {kind : Capability}
    (fn : FuncDef SourceSet n i F kind numMembers) :
    Option (FuncDef TargetSet n i F kind numMembers) :=
  let span := witnessSpan StaticState.initial.objects 0 fn.body
  let lowered := lowerBody fn.numParams span StaticState.initial fn.body
  let returnVar := fn.returnVar.map
    (renameLocal fn.numParams span lowered.2.aliases)
  certifyFunc (fn.numParams + span) lowered.1 returnVar

theorem certifyFunc_fields {n i numMembers : Nat} {F : Type}
    {kind : Capability} (numParams : Nat)
    (body : List (Stmt TargetSet ⟨n, i, numMembers⟩ F))
    (returnVar : Option LocalVar)
    (out : FuncDef TargetSet n i F kind numMembers)
    (hcertify : certifyFunc numParams body returnVar = some out) :
    out.numParams = numParams ∧ out.body = body ∧ out.returnVar = returnVar := by
  unfold certifyFunc at hcertify
  split at hcertify <;> rename_i hcaps
  · split at hcertify <;> rename_i hssa
    · have hout := Option.some.inj hcertify
      subst out
      exact ⟨rfl, rfl, rfl⟩
    · simp at hcertify
  · simp at hcertify

theorem lowerFunc_fields {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef SourceSet n i F kind numMembers)
    (out : FuncDef TargetSet n i F kind numMembers)
    (hlower : lowerFunc fn = some out) :
    let span := witnessSpan StaticState.initial.objects 0 fn.body
    out.numParams = fn.numParams + span ∧
      out.body = (lowerBody fn.numParams span StaticState.initial fn.body).1 := by
  unfold lowerFunc at hlower
  have hfields := certifyFunc_fields _ _ _ out hlower
  exact ⟨hfields.1, hfields.2.1⟩

def lowerStruct {n : Nat} {F : Type} (m : Module SourceSet n F) (i : Fin n) :
    Option (StructDef TargetSet n i F) := do
  let compute ← lowerFunc (m.structs i).compute
  let constrain ← lowerFunc (m.structs i).constrain
  pure {
    name := (m.structs i).name
    members := (m.structs i).members
    compute := compute
    constrain := constrain
  }

noncomputable def lowerModule {n : Nat} {F : Type} (m : Module SourceSet n F) :
    Option (Module TargetSet n F) := by
  classical
  exact if h : ∀ i, ∃ out, lowerStruct m i = some out then
    some { structs := fun i => Classical.choose (h i) }
  else none

/-- Expose the selected lowered struct after successful module erasure. -/
theorem lowerModule_struct {n : Nat} {F : Type} (m : Module SourceSet n F)
    (out : Module TargetSet n F) (h : lowerModule m = some out) (i : Fin n) :
    lowerStruct m i = some (out.structs i) := by
  classical
  unfold lowerModule at h
  split at h
  next hall =>
    simp only [Option.some.injEq] at h
    subst out
    exact Classical.choose_spec (hall i)
  next => simp at h

/-! ## Typed state relation and structural certificate -/

abbrev SourceObservation (n : Nat) (F : Type) :=
  ObjectResidualSemantics.ConstraintState n F

abbrev TargetObservation (n : Nat) (F : Type) :=
  Fin n × (LocalVar → F)

/-- The target environment stores original parameters unchanged and the
source witness at its explicit encoded witness local. Object paths themselves
remain on the source side and are never represented as field values. -/
structure StateRel {n : Nat} {F : Type}
    (m : Module SourceSet n F) (source : SourceObservation n F)
    (target : TargetObservation n F) : Prop where
  entry : source.1 = target.1
  params : ∀ v, v < (m.structs source.1).constrain.numParams →
    target.2 v = source.2.values v
  witness : ∀ path member,
    target.2 (witnessLocal (m.structs source.1).constrain.numParams path member) =
      source.2.witness (path, member)

def encodeTargetState {n : Nat} {F : Type} (m : Module SourceSet n F)
    (source : SourceObservation n F) : TargetObservation n F :=
  let numParams := (m.structs source.1).constrain.numParams
  (source.1, fun v =>
    if v < numParams then source.2.values v
    else source.2.witness (VarIdEncoding.decode (v - numParams)))

def decodeSourceState {n : Nat} {F : Type} (m : Module SourceSet n F)
    (target : TargetObservation n F) : SourceObservation n F :=
  let numParams := (m.structs target.1).constrain.numParams
  (target.1, {
    values := target.2
    objects := fun _ => []
    witness := fun key => target.2 (numParams + VarIdEncoding.encode key)
    nextPath := 0
  })

/-- Materialize the flat witness namespace introduced by object erasure.
Parameters occupy the prefix, encoded object members occupy the following
`span`, and downstream SSA locals are initialized to zero.  This is the single
owner of the StructObject layout used by executable witness transport. -/
def seedFlatWitness [OfNat F 0] (numParams span paramOffset : Nat)
    (inputs : List F) (source : StructObject.Witness F) : Witness LocalVar F :=
  fun v =>
    if v < numParams then
      if v < paramOffset then 0 else inputs[v - paramOffset]?.getD 0
    else if v < numParams + span then
      source (VarIdEncoding.decode (v - numParams))
    else 0

/-- Finite canonical form of the same layout. This is the form stored in a
compilation artifact: only selected input and reachable object coordinates are
transported. -/
def seedCanonicalWitness [OfNat F 0] (numParams span paramOffset : Nat)
    (inputs objects : List F) : Witness LocalVar F :=
  fun v =>
    if v < numParams then
      if v < paramOffset then 0 else inputs[v - paramOffset]?.getD 0
    else if v < numParams + span then
      objects[v - numParams]?.getD 0
    else 0

@[simp] theorem seedCanonicalWitness_param [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs objects : List F)
    (v : LocalVar) (hv : v < numParams) :
    seedCanonicalWitness numParams span paramOffset inputs objects v =
      if v < paramOffset then 0 else inputs[v - paramOffset]?.getD 0 := by
  simp [seedCanonicalWitness, hv]

@[simp] theorem seedCanonicalWitness_object [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs objects : List F)
    (slot : Nat) (hslot : slot < span) :
    seedCanonicalWitness numParams span paramOffset inputs objects
        (numParams + slot) = objects[slot]?.getD 0 := by
  have hge : ¬ numParams + slot < numParams := by omega
  have hlt : numParams + slot < numParams + span := by omega
  simp [seedCanonicalWitness, hge, hlt]

@[simp] theorem seedCanonicalWitness_local_above [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs objects : List F)
    (v : LocalVar) (hv : numParams ≤ v) :
    seedCanonicalWitness numParams span paramOffset inputs objects
        (baseRename numParams span v) = 0 := by
  have hbase : baseRename numParams span v = v + span := by
    simp [baseRename, Nat.not_lt.mpr hv]
  rw [hbase]
  have hgeParams : ¬ v + span < numParams :=
    Nat.not_lt_of_ge (Nat.le_trans hv (Nat.le_add_right v span))
  have hgeSpan : ¬ v + span < numParams + span :=
    Nat.not_lt_of_ge (Nat.add_le_add_right hv span)
  simp [seedCanonicalWitness, hgeParams, hgeSpan]

@[simp] theorem seedFlatWitness_object [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs : List F)
    (source : StructObject.Witness F) (slot : Nat) (hslot : slot < span) :
    seedFlatWitness numParams span paramOffset inputs source (numParams + slot) =
      source (VarIdEncoding.decode slot) := by
  have hge : ¬numParams + slot < numParams := by omega
  have hlt : numParams + slot < numParams + span := by omega
  simp [seedFlatWitness, hge, hlt]

/-- Read canonical object coordinates back from an object-erased flat witness. -/
def readbackObjectWitness (numParams : Nat) (target : Witness LocalVar F) :
    StructObject.Witness F :=
  fun key => target (numParams + VarIdEncoding.encode key)

theorem readback_seedFlatWitness [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs : List F)
    (source : StructObject.Witness F) (key : StructObject.InstancePath × Nat)
    (hobservable : VarIdEncoding.encode key < span) :
    readbackObjectWitness numParams
      (seedFlatWitness numParams span paramOffset inputs source) key = source key := by
  rw [readbackObjectWitness, seedFlatWitness_object numParams span paramOffset inputs
    source (VarIdEncoding.encode key) hobservable, VarIdEncoding.decode_encode]

theorem readback_seedCanonicalWitness [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs objects : List F)
    (key : StructObject.InstancePath × Nat)
    (hobservable : VarIdEncoding.encode key < span) :
    readbackObjectWitness numParams
      (seedCanonicalWitness numParams span paramOffset inputs objects) key =
        objects[VarIdEncoding.encode key]?.getD 0 := by
  rw [readbackObjectWitness, seedCanonicalWitness_object numParams span paramOffset
    inputs objects (VarIdEncoding.encode key) hobservable]

/-- Finite readback returns exactly, and only, the selected encoded object
span carried by a canonical witness. -/
theorem finite_readback_seedCanonicalWitness [OfNat F 0]
    (numParams span paramOffset : Nat) (inputs objects : List F)
    (hlength : objects.length = span) :
    (List.ofFn fun i : Fin span =>
      seedCanonicalWitness numParams span paramOffset inputs objects
        (numParams + i.val)) = objects := by
  subst span
  apply List.ext_get
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    rw [List.get_ofFn]
    change seedCanonicalWitness numParams objects.length paramOffset inputs objects
      (numParams + i) = objects.get ⟨i, hj⟩
    rw [seedCanonicalWitness_object numParams objects.length paramOffset inputs objects
      i hi]
    rw [List.getElem?_eq_getElem hi]
    simp

/-- Canonical finite observables initialize exact source/target relation used
by object lowering. Parameters stay in place; object coordinates occupy
encoded witness block; ordinary SSA locals begin above block. -/
theorem canonical_initial_rel [Field F]
    (numParams computeParams span : Nat) (inputs objects : List F) :
    LowerStateRel numParams span (fun v => decide (v < numParams))
      StaticState.initial
      (TypedSourceSemantics.initialState numParams computeParams inputs objects)
      (seedCanonicalWitness numParams span (numParams - computeParams)
        inputs objects) := by
  constructor
  · intro v hv
    have hvlt : v < numParams := by simpa using hv
    simp [StaticState.initial, AliasEnv.empty, renameLocal, baseRename, hvlt,
      TypedSourceSemantics.initialState, seedCanonicalWitness]
  · funext v
    simp [StaticState.initial, TypedSourceSemantics.initialState,
      StructObject.ObjEnv.update]
  · rfl
  · intro key hkey
    change seedCanonicalWitness numParams span (numParams - computeParams)
      inputs objects (numParams + encodedMember key.1 key.2) =
        objects[encodedMember key.1 key.2]?.getD 0
    exact seedCanonicalWitness_object numParams span (numParams - computeParams)
      inputs objects (encodedMember key.1 key.2) hkey
  · intro sourceLocal targetLocal halias
    simp [StaticState.initial, AliasEnv.empty] at halias
  · intro sourceLocal targetLocal halias
    simp [StaticState.initial, AliasEnv.empty] at halias
  · intro v hv
    simp [hv]

/-- Selected certified constraint body has identical direct object-aware and
object-erased observations under canonical finite source data. -/
theorem lowerBody_canonical_iff [Field F]
    {n i numMembers : Nat}
    (fn : FuncDef SourceSet n i F .constraint numMembers)
    (computeParams : Nat) (inputs objects : List F) :
    let span := witnessSpan StaticState.initial.objects 0 fn.body
    let lowered := lowerBody fn.numParams span StaticState.initial fn.body
    (evalTargetBody lowered.1
      (seedCanonicalWitness fn.numParams span
        (fn.numParams - computeParams) inputs objects)).2 ↔
      (ObjectResidualSemantics.evalBody fn.body
        (TypedSourceSemantics.initialState fn.numParams computeParams
          inputs objects)).2 := by
  let span := witnessSpan StaticState.initial.objects 0 fn.body
  have hsim := lowerBody_simulation (numParams := fn.numParams) (span := span)
    fn.body (fun v => decide (v < fn.numParams)) StaticState.initial
    (TypedSourceSemantics.initialState fn.numParams computeParams inputs objects)
    (seedCanonicalWitness fn.numParams span (fn.numParams - computeParams)
      inputs objects)
    fn.wf_ssa fn.wf_caps (Nat.le_refl span)
    (canonical_initial_rel fn.numParams computeParams span inputs objects)
  exact hsim.1

theorem encodeTargetState_rel {n : Nat} {F : Type}
    (m : Module SourceSet n F) (source : SourceObservation n F) :
    StateRel m source (encodeTargetState m source) := by
  constructor
  · rfl
  · intro v hv
    simp [encodeTargetState, hv]
  · intro path member
    simp [encodeTargetState, witnessLocal, encodedMember,
      VarIdEncoding.decode_encode]

theorem decodeSourceState_rel {n : Nat} {F : Type}
    (m : Module SourceSet n F) (target : TargetObservation n F) :
    StateRel m (decodeSourceState m target) target := by
  constructor
  · rfl
  · intro v hv
    rfl
  · intro path member
    rfl

def targetStage (n : Nat) (F : Type) [Field F] : ModuleStage TargetSet n F where
  State := TargetObservation n F
  satisfies observation m :=
    evalFuncConstrain (CallSemantics.targetHandlers F) m
      (m.structs observation.1).constrain observation.2

/-- Elaboration semantics for the object-bearing stage, indexed by the
explicit source/target state relation. -/
noncomputable def sourceStage (n : Nat) (F : Type) [Field F] :
    ModuleStage SourceSet n F where
  State := SourceObservation n F
  satisfies source m := ∃ out target,
    lowerModule m = some out ∧ StateRel m source target ∧
      (targetStage n F).satisfies target out

/-- Certified partial StructObject head erasure. -/
noncomputable def structuralPass (n : Nat) (F : Type) [Field F] :
    EraseDialect StructObject.sig TargetSet (sourceStage n F) (targetStage n F) where
  lower m := match lowerModule m with
    | some out => .ok out
    | none => .error "StructObject erasure failed"
  stateRel m _ source target := StateRel m source target
  preservation := by
    intro m out source hlower hsatisfies
    rcases hsatisfies with ⟨semanticOut, target, hsemantic, hrel, hsat⟩
    cases herase : lowerModule m with
    | none => rw [herase] at hlower; cases hlower
    | some result =>
      rw [herase] at hlower
      have hresult : result = out := Except.ok.inj hlower
      have hsemanticResult : semanticOut = result := by
        rw [herase] at hsemantic
        exact (Option.some.inj hsemantic).symm
      subst out
      subst semanticOut
      exact ⟨target, hrel, hsat⟩
  reflection := by
    intro m out target hlower hsatisfies
    cases herase : lowerModule m with
    | none => rw [herase] at hlower; cases hlower
    | some result =>
      rw [herase] at hlower
      have hresult : result = out := Except.ok.inj hlower
      subst out
      let source := decodeSourceState m target
      have hrel : StateRel m source target := decodeSourceState_rel m target
      exact ⟨source, hrel, ⟨result, target, herase, hrel, hsatisfies⟩⟩

/-- Phase-11 Call erasure specialized to the exact source stage expected by
the Phase-12 object pass. -/
noncomputable def callPass (n : Nat) (F : Type) [Field F] :
    EraseDialect Call.sig SourceSet
      (CallErasure.expandedSourceStage
        (CallErasure.objectFeltConstrainSyntax (F := F)) (sourceStage n F))
      (sourceStage n F) :=
  CallErasure.structuralPass
    (CallErasure.objectFeltConstrainSyntax (F := F))
    (CallErasure.objectFeltConstrainRenameStable (F := F))
    (sourceStage n F)

/-- The explicit structural prefix pipeline `[Call, StructObject, ...]`. -/
noncomputable def callThenObjectPass (n : Nat) (F : Type) [Field F] :=
  (callPass n F).compose (structuralPass n F)

end Dialect.StructObjectPass
