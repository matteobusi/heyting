/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.DialectPass
import Heyting.Dialects.Call
import Heyting.Dialects.Felt
import Heyting.Dialects.ConstrainEq

/-!
# EraseCalls Pass (Phase 6)

Syntax-only lowering from the concrete source dialect set

```text
[Call, Felt, ConstrainEq]
```

into the call-free target set

```text
[Felt, ConstrainEq]
```

by hygienically inlining call targets. This file now contains executable,
well-founded inlining and certified function/module construction. Semantic
correctness is proved in `CallSemantics.lean`.

Why standalone rather than a generic `DialectPass`: the generic `FreshLowerOp`
handler has no module access, but call inlining must read the callee body from
the enclosing module. Until a module-aware pass abstraction is introduced,
`eraseBody` takes the module explicitly.

## Phase 6 status

- completed: freshen callee locals without capture
- completed: bind call arguments to callee parameters
- completed: bind callee returns with an explicit target definition
- completed: recursively erase nested calls without fuel
- completed: prove recursive compute/constrain simulation
- completed: certify erased `FuncDef` capability and SSA checks
- completed: expose a partial call-aware module wrapper and composition adapter
-/

namespace Dialect.CallPass

open Dialect

/-! ## Concrete source / target dialect sets -/

/-- Source set with `Call` at index 0, then `Felt`, then `ConstrainEq`. -/
abbrev SourceSet : DialectSet := [Call.sig, Felt.sig, ConstrainEq.sig]

/-- Target set: `Call` erased. -/
abbrev TargetSet : DialectSet := [Felt.sig, ConstrainEq.sig]

/-- `Call` index in `SourceSet`. -/
def callSourceIx : Fin SourceSet.length := ⟨0, by simp [SourceSet]⟩

/-- `Felt` index in `SourceSet`. -/
def feltSourceIx : Fin SourceSet.length := ⟨1, by simp [SourceSet]⟩

/-- `ConstrainEq` index in `SourceSet`. -/
def constrSourceIx : Fin SourceSet.length := ⟨2, by simp [SourceSet]⟩

/-- `Felt` index in `TargetSet`. -/
def feltTargetIx : Fin TargetSet.length := ⟨0, by simp [TargetSet]⟩

/-- `ConstrainEq` index in `TargetSet`. -/
def constrTargetIx : Fin TargetSet.length := ⟨1, by simp [TargetSet]⟩

/-- A source statement is a call iff its dialect index is `callSourceIx`. -/
def isCall {γ : OpCtx} {F : Type} (s : Stmt SourceSet γ F) : Bool :=
  match s with
  | .op d _ => d == callSourceIx

/-! ## Index reindexing helpers -/

/-- Translate a `Felt` op payload from the source set to a target statement. -/
def reindexFelt {γ : OpCtx} {F : Type} (op : Felt.Op γ F) : Stmt TargetSet γ F :=
  .op feltTargetIx op

/-- Translate a `ConstrainEq` op payload from the source set to a target statement. -/
def reindexConstr {γ : OpCtx} {F : Type} (op : ConstrainEq.Op γ F) : Stmt TargetSet γ F :=
  .op constrTargetIx op

/-- Rebuild a felt op in another op context while renaming its locals. -/
def lowerFeltOp {γ γ' : OpCtx} {F : Type} (ρ : LocalVar → LocalVar) :
    Felt.Op γ F → Felt.Op γ' F
  | .add d a b => .add (ρ d) (ρ a) (ρ b)
  | .sub d a b => .sub (ρ d) (ρ a) (ρ b)
  | .mul d a b => .mul (ρ d) (ρ a) (ρ b)
  | .div d a b => .div (ρ d) (ρ a) (ρ b)
  | .neg d a   => .neg (ρ d) (ρ a)
  | .inv d a   => .inv (ρ d) (ρ a)
  | .const d c => .const (ρ d) c

/-- Embed a renamed felt op into the call-free target set. -/
def lowerFeltInto {γ γ' : OpCtx} {F : Type} (ρ : LocalVar → LocalVar)
    (op : Felt.Op γ F) : Stmt TargetSet γ' F :=
  .op feltTargetIx (lowerFeltOp ρ op)

@[simp] theorem lowerFeltOp_destVar {γ γ' : OpCtx} {F : Type}
    (ρ : LocalVar → LocalVar) (op : Felt.Op γ F) :
    Felt.destVar (lowerFeltOp (γ' := γ') ρ op) = ρ (Felt.destVar op) := by
  cases op <;> rfl

@[simp] theorem lowerFeltOp_reads {γ γ' : OpCtx} {F : Type}
    (ρ : LocalVar → LocalVar) (op : Felt.Op γ F) :
    Felt.reads (lowerFeltOp (γ' := γ') ρ op) = (Felt.reads op).map ρ := by
  cases op <;> rfl

/-- Rebuild a constrain-equality op in another context while renaming locals. -/
def lowerConstrOp {γ γ' : OpCtx} {F : Type} (ρ : LocalVar → LocalVar) :
    ConstrainEq.Op γ F → ConstrainEq.Op γ' F
  | .eq a b => .eq (ρ a) (ρ b)

/-- Embed a renamed constrain-equality op into the call-free target set. -/
def lowerConstrInto {γ γ' : OpCtx} {F : Type} (ρ : LocalVar → LocalVar)
    (op : ConstrainEq.Op γ F) : Stmt TargetSet γ' F :=
  .op constrTargetIx (lowerConstrOp ρ op)

/-! ## Fresh-offset utilities -/

/-- Fresh variable offset for inlining a callee body: one past the current bound. -/
def freshOffset (next : LocalVar) (calleeBody : List (Stmt SourceSet γ F)) : LocalVar :=
  max next (maxVarBody calleeBody)

/-- Rename a local `v` into the fresh space starting at `base`. -/
def shiftLocal (base : LocalVar) (v : LocalVar) : LocalVar :=
  base + v

/-- Which function body a call selects in the current evaluation context. -/
inductive BodyKind where
  | compute
  | constrain
  deriving Repr, DecidableEq

/-- Locals known defined after executing a body from an initial defined set. -/
def definedLocalsAfter {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (init : LocalVar → Bool) :
    List (Stmt Δ ⟨n, i, numMembers⟩ F) → LocalVar → Bool
  | [] => init
  | stmt :: rest =>
    let next := match stmt.dest with
      | some d => fun v => init v || v == d
      | none => init
    definedLocalsAfter next rest

/-- One SSA step exposes read-definedness and the correctly extended tail set. -/
theorem isSSA_cons_parts {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (init : LocalVar → Bool)
    (stmt : Stmt Δ ⟨n, i, numMembers⟩ F)
    (rest : List (Stmt Δ ⟨n, i, numMembers⟩ F))
    (hssa : isSSA init (stmt :: rest) = true) :
    stmt.reads.all init = true ∧
      isSSA
        (match stmt.dest with
          | some d => fun v => init v || v == d
          | none => init)
        rest = true := by
  simp only [isSSA, Bool.and_eq_true] at hssa
  cases hdest : stmt.dest with
  | none => simpa [hdest] using hssa
  | some d =>
    rw [hdest] at hssa
    simp only [Bool.and_eq_true] at hssa
    exact ⟨hssa.1, hssa.2.2⟩

@[simp] theorem definedLocalsAfter_cons {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (init : LocalVar → Bool)
    (stmt : Stmt Δ ⟨n, i, numMembers⟩ F)
    (rest : List (Stmt Δ ⟨n, i, numMembers⟩ F)) :
    definedLocalsAfter init (stmt :: rest) =
      definedLocalsAfter
        (match stmt.dest with
          | some d => fun v => init v || v == d
          | none => init)
        rest := by
  rfl

/-- A call destination is supported only when the callee declares a return
that is defined by parameters or its SSA body.
-/
def computeReturnSupported {n i numMembers : Nat} {F : Type}
    (fn : FuncDef SourceSet n i F .witness numMembers)
    (dest : Option LocalVar) : Bool :=
  match dest with
  | none => true
  | some _ =>
    match fn.returnVar with
    | none => false
    | some r => definedLocalsAfter (fun v => decide (v < fn.numParams)) fn.body r

theorem definedLocalsAfter_of_initial {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (body : List (Stmt Δ ⟨n, i, numMembers⟩ F))
    (init : LocalVar → Bool) {v : LocalVar} (hv : init v = true) :
    definedLocalsAfter init body v = true := by
  induction body generalizing init with
  | nil => exact hv
  | cons stmt rest ih =>
    apply ih
    cases hdest : stmt.dest with
    | none => exact hv
    | some d => simp [hv]

theorem definedLocalsAfter_of_dest {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (body : List (Stmt Δ ⟨n, i, numMembers⟩ F))
    (init : LocalVar → Bool) {stmt : Stmt Δ ⟨n, i, numMembers⟩ F}
    {d : LocalVar} (hmem : stmt ∈ body) (hdest : stmt.dest = some d) :
    definedLocalsAfter init body d = true := by
  induction body generalizing init with
  | nil => simp at hmem
  | cons head rest ih =>
    rcases List.mem_cons.mp hmem with hEq | hrest
    · subst stmt
      simp only [definedLocalsAfter]
      apply definedLocalsAfter_of_initial
      rw [hdest]
      simp
    · simp only [definedLocalsAfter]
      exact ih _ hrest

theorem computeReturnSupported_some {n i numMembers : Nat} {F : Type}
    (fn : FuncDef SourceSet n i F .witness numMembers) (d : LocalVar)
    (h : computeReturnSupported fn (some d) = true) :
    ∃ r, fn.returnVar = some r ∧
      definedLocalsAfter (fun v => decide (v < fn.numParams)) fn.body r = true := by
  simp only [computeReturnSupported] at h
  cases hr : fn.returnVar with
  | none => simp [hr] at h
  | some r =>
    exact ⟨r, rfl, by simpa [hr] using h⟩

theorem cap_le_of_capsLE {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} {body : List (Stmt Δ ⟨n, i, numMembers⟩ F)}
    (hcap : capsLE kind body = true) {stmt : Stmt Δ ⟨n, i, numMembers⟩ F}
    (hmem : stmt ∈ body) : stmt.cap ≤ kind := by
  apply of_decide_eq_true
  exact (List.all_eq_true.mp hcap) stmt hmem

/-- Constraint-only operations cannot occur in a well-formed compute body. -/
theorem witness_body_no_constrainEq {n i numMembers : Nat} {F : Type}
    (fn : FuncDef SourceSet n i F .witness numMembers)
    (op : ConstrainEq.Op ⟨n, i, numMembers⟩ F)
    (hmem : (Stmt.op constrSourceIx op :
      Stmt SourceSet ⟨n, i, numMembers⟩ F) ∈ fn.body) : False := by
  have hle := cap_le_of_capsLE fn.wf_caps hmem
  change ConstrainEq.cap op ≤ Capability.witness at hle
  change Capability.constraint = Capability.pure ∨
    Capability.constraint = Capability.witness at hle
  rcases hle with h | h <;> cases h

/-- Strict local-variable bound including parameters and an optional return variable. -/
def funcVarBound {Δ : DialectSet} {n i numMembers : Nat} {F : Type} {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers) : LocalVar :=
  max fn.numParams
    (max (maxVarBody fn.body) (Option.getD (fn.returnVar.map (fun v => v + 1)) 0))

theorem numParams_le_funcVarBound {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers) :
    fn.numParams ≤ funcVarBound fn :=
  Nat.le_max_left _ _

theorem maxVarBody_le_funcVarBound {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers) :
    maxVarBody fn.body ≤ funcVarBound fn := by
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem returnVar_lt_funcVarBound {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers) {r : LocalVar}
    (hr : fn.returnVar = some r) : r < funcVarBound fn := by
  simp only [funcVarBound, hr, Option.map_some, Option.getD_some]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self r)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem funcBody_freshAbove {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers) :
    bodyFreshAbove (funcVarBound fn) fn.body := by
  exact bodyFreshAbove_mono (bodyFreshAbove_maxVarBody fn.body)
    (maxVarBody_le_funcVarBound fn)

theorem funcBody_var_lt {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    {stmt : Stmt Δ ⟨n, i, numMembers⟩ F} (hmem : stmt ∈ fn.body)
    {v : LocalVar} (hv : v ∈ stmt.vars) : v < funcVarBound fn :=
  funcBody_freshAbove fn stmt hmem v hv

/-- A call's renamed arguments lie below the caller's fresh counter. -/
theorem callArg_renamed_lt_next {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef SourceSet n i F kind numMembers)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (hbelow : ∀ v, v < funcVarBound fn → rename v < next)
    (dest : Option LocalVar) (target : Fin i) (sel : Nat) (args : List LocalVar)
    (hmem : (Stmt.op callSourceIx (.call dest target sel args) :
      Stmt SourceSet ⟨n, i, numMembers⟩ F) ∈ fn.body)
    (k : Fin args.length) : rename (args.get k) < next := by
  apply hbelow (args.get k)
  apply funcBody_var_lt fn hmem
  change args.get k ∈ dest.toList ++ args
  simp

/-- Map callee parameters to caller arguments and callee locals into fresh space. -/
def inlineVar (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (numParams base : LocalVar) (hargs : args.length = numParams) :
    LocalVar → LocalVar :=
  fun v =>
    if hparam : v < numParams then
      callerRename (args.get ⟨v, by simpa [hargs] using hparam⟩)
    else
      shiftLocal base v

@[simp] theorem inlineVar_param (callerRename : LocalVar → LocalVar)
    (args : List LocalVar) (numParams base v : LocalVar)
    (hargs : args.length = numParams) (hv : v < numParams) :
    inlineVar callerRename args numParams base hargs v =
      callerRename (args.get ⟨v, by simpa [hargs] using hv⟩) := by
  simp [inlineVar, hv]

@[simp] theorem inlineVar_local (callerRename : LocalVar → LocalVar)
    (args : List LocalVar) (numParams base v : LocalVar)
    (hargs : args.length = numParams) (hv : numParams ≤ v) :
    inlineVar callerRename args numParams base hargs v = shiftLocal base v := by
  simp [inlineVar, Nat.not_lt_of_ge hv]

/-- Every bounded callee variable remains below its reserved inlining range.

Parameter images need the caller-side freshness invariant; non-parameters are
shifted into the reserved block directly.
-/
theorem inlineVar_lt_reserved {Δ : DialectSet} {n i numMembers : Nat} {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base v : LocalVar) (hargs : args.length = fn.numParams)
    (hparams : ∀ k (hk : k < fn.numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base)
    (hv : v < funcVarBound fn) :
    inlineVar callerRename args fn.numParams base hargs v <
      base + funcVarBound fn := by
  by_cases hparam : v < fn.numParams
  · rw [inlineVar_param callerRename args fn.numParams base v hargs hparam]
    exact Nat.lt_of_lt_of_le (hparams v hparam) (Nat.le_add_right base _)
  · rw [inlineVar_local callerRename args fn.numParams base v hargs
      (Nat.le_of_not_gt hparam)]
    exact Nat.add_lt_add_left hv base

/-- A renamed return variable cannot alias a counter beyond its reserved block. -/
theorem inlineVar_return_ne_of_reserved_le {n i numMembers : Nat}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base next r : LocalVar) (hargs : args.length = fn.numParams)
    (hparams : ∀ k (hk : k < fn.numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base)
    (hr : fn.returnVar = some r) (hnext : base + funcVarBound fn ≤ next) :
    inlineVar callerRename args fn.numParams base hargs r ≠ next := by
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
    (inlineVar_lt_reserved fn callerRename args base r hargs hparams
      (returnVar_lt_funcVarBound fn hr)) hnext)

/-- A non-parameter destination stays distinct from every other renamed local,
even when multiple parameters alias the same caller argument.
-/
theorem inlineVar_local_separate
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (numParams base d : LocalVar) (hargs : args.length = numParams)
    (hparams : ∀ k (hk : k < numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base)
    (hd : numParams ≤ d) :
    ∀ v, v ≠ d →
      inlineVar callerRename args numParams base hargs v ≠
        inlineVar callerRename args numParams base hargs d := by
  intro v hv
  rw [inlineVar_local callerRename args numParams base d hargs hd]
  by_cases hvParam : v < numParams
  · rw [inlineVar_param callerRename args numParams base v hargs hvParam]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hparams v hvParam)
      (Nat.le_add_right base d))
  · rw [inlineVar_local callerRename args numParams base v hargs
      (Nat.le_of_not_gt hvParam)]
    intro heq
    exact hv (Nat.add_left_cancel heq)

/-- SSA bodies never assign to parameter locals, including in body tails where
the defined-set predicate also contains earlier destinations.
-/
theorem isSSA_dest_ge_numParams {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (numParams : Nat)
    (body : List (Stmt Δ ⟨n, i, numMembers⟩ F))
    (hssa : isSSA (fun v => decide (v < numParams)) body = true)
    {stmt : Stmt Δ ⟨n, i, numMembers⟩ F} {d : LocalVar}
    (hmem : stmt ∈ body) (hdest : stmt.dest = some d) :
    numParams ≤ d := by
  have aux : ∀ (xs : List (Stmt Δ ⟨n, i, numMembers⟩ F))
      (init : LocalVar → Bool),
      (∀ v, v < numParams → init v = true) →
      isSSA init xs = true →
      ∀ {s : Stmt Δ ⟨n, i, numMembers⟩ F} {x : LocalVar},
        s ∈ xs → s.dest = some x → numParams ≤ x := by
    intro xs
    induction xs with
    | nil =>
      intro _ _ _ s _ hs _
      simp at hs
    | cons head rest ih =>
      intro init hparams hbody s x hs hdest
      simp only [isSSA] at hbody
      cases hheadDest : head.dest with
      | none =>
        rw [hheadDest] at hbody
        simp only [Bool.and_eq_true] at hbody
        rcases List.mem_cons.mp hs with hEq | hrest
        · subst s
          rw [hheadDest] at hdest
          contradiction
        · exact ih init hparams hbody.2 hrest hdest
      | some headDest =>
        rw [hheadDest] at hbody
        simp only [Bool.and_eq_true] at hbody
        have hheadFresh : init headDest = false := by
          simpa using hbody.2.1
        rcases List.mem_cons.mp hs with hEq | hrest
        · subst s
          have heq : headDest = x := Option.some.inj (hheadDest.symm.trans hdest)
          subst x
          exact Nat.le_of_not_gt (fun hlt => by
            have hdefined := hparams headDest hlt
            rw [hdefined] at hheadFresh
            contradiction)
        · apply ih (fun v => init v || v == headDest)
            (fun v hv => by simp [hparams v hv]) hbody.2.2 hrest hdest
  exact aux body (fun v => decide (v < numParams)) (by
    intro v hv
    simp [hv]) hssa hmem hdest

/-- SSA supplies destination separation required by renamed local semantics. -/
theorem inlineVar_stmt_dest_separate {n i numMembers : Nat}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    (hparams : ∀ k (hk : k < fn.numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base)
    {stmt : Stmt Δ ⟨n, i, numMembers⟩ F} {d : LocalVar}
    (hmem : stmt ∈ fn.body) (hdest : stmt.dest = some d) :
    ∀ v, v ≠ d →
      inlineVar callerRename args fn.numParams base hargs v ≠
        inlineVar callerRename args fn.numParams base hargs d :=
  inlineVar_local_separate callerRename args fn.numParams base d hargs hparams
    (isSSA_dest_ge_numParams fn.numParams fn.body fn.wf_ssa hmem hdest)

/-- Every renamed callee destination lies in its reserved local range, above
the caller storage protected by `base`. -/
theorem inlineVar_stmt_dest_ge_base {n i numMembers : Nat}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    {stmt : Stmt Δ ⟨n, i, numMembers⟩ F} {d : LocalVar}
    (hmem : stmt ∈ fn.body) (hdest : stmt.dest = some d) :
    base ≤ inlineVar callerRename args fn.numParams base hargs d := by
  rw [inlineVar_local callerRename args fn.numParams base d hargs
    (isSSA_dest_ge_numParams fn.numParams fn.body fn.wf_ssa hmem hdest)]
  exact Nat.le_add_right base d

/-- Every renamed body destination stays above a caller-storage floor. -/
def RenameFrameInvariant {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers)
    (rename : LocalVar → LocalVar) (floor : LocalVar) : Prop :=
  ∀ (stmt : Stmt Δ ⟨n, i, numMembers⟩ F), stmt ∈ fn.body →
    ∀ d, stmt.dest = some d → floor ≤ rename d

theorem renameFrameInvariant_zero {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    (rename : LocalVar → LocalVar) :
    RenameFrameInvariant fn rename 0 := by
  intro _ _ d _
  exact Nat.zero_le (rename d)

theorem renameFrameInvariant_inlineVar {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams) :
    RenameFrameInvariant fn
      (inlineVar callerRename args fn.numParams base hargs) base := by
  intro stmt hmem d hdest
  exact inlineVar_stmt_dest_ge_base fn callerRename args base hargs hmem hdest

theorem RenameFrameInvariant.mono {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} {fn : FuncDef Δ n i F kind numMembers}
    {rename : LocalVar → LocalVar} {small large : LocalVar}
    (h : RenameFrameInvariant fn rename large) (hle : small ≤ large) :
    RenameFrameInvariant fn rename small := by
  intro stmt hmem d hdest
  exact Nat.le_trans hle (h stmt hmem d hdest)

/-- Renaming contract threaded by recursive inlining: all function locals map
below `next`, and every SSA destination remains separated from other locals.
-/
def RenameInvariant {Δ : DialectSet} {n i numMembers : Nat} {F : Type} {kind : Capability}
    (fn : FuncDef Δ n i F kind numMembers)
    (rename : LocalVar → LocalVar) (next : LocalVar) : Prop :=
  (∀ v, v < funcVarBound fn → rename v < next) ∧
  (∀ (stmt : Stmt Δ ⟨n, i, numMembers⟩ F), stmt ∈ fn.body →
    ∀ d, stmt.dest = some d →
      ∀ v, v ≠ d → rename v ≠ rename d)

/-- Body-local form of `RenameInvariant`, suitable for recursive suffix
induction where no enclosing `FuncDef` remains in the motive. -/
def BodyRenameInvariant {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    (body : List (Stmt Δ ⟨n, i, numMembers⟩ F))
    (rename : LocalVar → LocalVar) (next : LocalVar) : Prop :=
  (∀ stmt ∈ body, ∀ v ∈ stmt.vars, rename v < next) ∧
  (∀ stmt ∈ body, ∀ d, stmt.dest = some d →
    ∀ v, v ≠ d → rename v ≠ rename d)

theorem RenameInvariant.body {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} {fn : FuncDef Δ n i F kind numMembers}
    {rename : LocalVar → LocalVar} {next : LocalVar}
    (h : RenameInvariant fn rename next) :
    BodyRenameInvariant fn.body rename next := by
  constructor
  · intro stmt hmem v hv
    exact h.1 v (funcBody_var_lt fn hmem hv)
  · exact h.2

theorem BodyRenameInvariant.tail {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {head : Stmt Δ ⟨n, i, numMembers⟩ F}
    {tail : List (Stmt Δ ⟨n, i, numMembers⟩ F)}
    {rename : LocalVar → LocalVar} {next : LocalVar}
    (h : BodyRenameInvariant (head :: tail) rename next) :
    BodyRenameInvariant tail rename next := by
  constructor <;> intro stmt hmem
  · exact h.1 stmt (by simp [hmem])
  · exact h.2 stmt (by simp [hmem])

theorem BodyRenameInvariant.mono {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {body : List (Stmt Δ ⟨n, i, numMembers⟩ F)}
    {rename : LocalVar → LocalVar} {next next' : LocalVar}
    (h : BodyRenameInvariant body rename next) (hle : next ≤ next') :
    BodyRenameInvariant body rename next' := by
  exact ⟨fun stmt hmem v hv => Nat.lt_of_lt_of_le (h.1 stmt hmem v hv) hle,
    h.2⟩

theorem renameInvariant_id {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers) :
    RenameInvariant fn id (funcVarBound fn) := by
  constructor
  · intro v hv
    exact hv
  · intro _ _ d _ v hv
    exact hv

theorem renameInvariant_inlineVar {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef Δ n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    (hparams : ∀ k (hk : k < fn.numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base) :
    RenameInvariant fn (inlineVar callerRename args fn.numParams base hargs)
      (base + funcVarBound fn) := by
  constructor
  · intro v hv
    exact inlineVar_lt_reserved fn callerRename args base v hargs hparams hv
  · intro stmt hmem d hdest
    exact inlineVar_stmt_dest_separate fn callerRename args base hargs hparams
      hmem hdest

theorem RenameInvariant.mono {Δ : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} {fn : FuncDef Δ n i F kind numMembers}
    {rename : LocalVar → LocalVar} {next next' : LocalVar}
    (h : RenameInvariant fn rename next) (hle : next ≤ next') :
    RenameInvariant fn rename next' := by
  exact ⟨fun v hv => Nat.lt_of_lt_of_le (h.1 v hv) hle, h.2⟩

theorem RenameInvariant.callArg_lt {n i numMembers : Nat} {F : Type}
    {kind : Capability} {fn : FuncDef SourceSet n i F kind numMembers}
    {rename : LocalVar → LocalVar} {next : LocalVar}
    (hinv : RenameInvariant fn rename next)
    (dest : Option LocalVar) (target : Fin i) (sel : Nat) (args : List LocalVar)
    (hmem : (Stmt.op callSourceIx (.call dest target sel args) :
      Stmt SourceSet ⟨n, i, numMembers⟩ F) ∈ fn.body)
    (k : Fin args.length) : rename (args.get k) < next :=
  callArg_renamed_lt_next fn rename next hinv.1 dest target sel args hmem k

/-- Explicitly copy an optional callee return into an optional caller destination.

The copy is encoded as `zero := 0; dest := return + zero`. This also handles
functions returning one of their parameters, where renaming alone would not
produce a statement defining `dest`.
-/
def emitReturnCopy {γ : OpCtx} [Zero F] (dest returnVar : Option LocalVar)
    (calleeRename callerRename : LocalVar → LocalVar) (next : LocalVar) :
    List (Stmt TargetSet γ F) × LocalVar :=
  match dest, returnVar with
  | some d, some r =>
    let zeroVar := next
    ([.op feltTargetIx (.const zeroVar 0),
      .op feltTargetIx (.add (callerRename d) (calleeRename r) zeroVar)], next + 1)
  | _, _ => ([], next)

theorem emitReturnCopy_next_mono {γ : OpCtx} {F : Type} [Zero F]
    (dest returnVar : Option LocalVar)
    (calleeRename callerRename : LocalVar → LocalVar) (next : LocalVar) :
    next ≤ (emitReturnCopy (γ := γ) (F := F) dest returnVar
      calleeRename callerRename next).2 := by
  cases dest <;> cases returnVar <;> simp [emitReturnCopy]

/-! ## Recursive body lowering -/

/--
Lower a source body into the call-free target set, threading a fresh counter.

`current` identifies the body being expanded; `caller` identifies the output
context. `rename` maps current-body locals into caller locals. Calls recursively
expand strictly earlier bodies and therefore terminate without fuel.

Lowering returns `none` for unsupported selectors, arity mismatches, a
constraint call with a destination, or a compute destination whose callee has
no return value. These conditions become the call-well-formedness obligations
for the module correctness theorem.
-/
def eraseBodyInto {n callerMembers currentMembers : Nat} [Zero F]
    (m : Module SourceSet n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) :
    Option (List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar) :=
  match stmts with
  | [] => some ([], next)
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ =>
      match p with
      | .call dest target sel args =>
        if Call.selectorSupported sel then
          let targetIndex := Call.moduleTarget target current.isLt
          let callee := Call.targetStructAt m current target
          match kind with
          | .compute =>
            let fn := callee.compute
            if hargs : args.length = fn.numParams then
              if computeReturnSupported fn dest then
                let base := next
                let calleeRename := inlineVar rename args fn.numParams base hargs
                let reserved := base + funcVarBound fn
                match eraseBodyInto m caller targetIndex .compute calleeRename reserved fn.body with
                | none => none
                | some (calleeBody, afterCallee) =>
                  let copy := emitReturnCopy dest fn.returnVar calleeRename rename afterCallee
                  match eraseBodyInto m caller current kind rename copy.2 rest with
                  | none => none
                  | some (tail, afterTail) =>
                    some (calleeBody ++ copy.1 ++ tail, afterTail)
              else
                none
            else
              none
          | .constrain =>
            match dest with
            | none =>
              let fn := callee.constrain
              if hargs : args.length = fn.numParams then
                let base := next
                let calleeRename := inlineVar rename args fn.numParams base hargs
                let reserved := base + funcVarBound fn
                match eraseBodyInto m caller targetIndex .constrain calleeRename
                    reserved fn.body with
                | none => none
                | some (calleeBody, afterCallee) =>
                  match eraseBodyInto m caller current kind rename afterCallee rest with
                  | none => none
                  | some (tail, afterTail) => some (calleeBody ++ tail, afterTail)
              else
                none
            | some _ => none
        else
          none
    | ⟨1, _⟩, _ =>
      match eraseBodyInto m caller current kind rename next rest with
      | none => none
      | some (tail, afterTail) => some (lowerFeltInto rename p :: tail, afterTail)
    | ⟨2, _⟩, _ =>
      match eraseBodyInto m caller current kind rename next rest with
      | none => none
      | some (tail, afterTail) => some (lowerConstrInto rename p :: tail, afterTail)
termination_by (current.val, stmts.length)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      simp_wf
    | apply Prod.Lex.left
      simp [Call.moduleTarget, target.isLt]

set_option linter.flexible false in
/-- Successful recursive erasure never moves the fresh counter backwards. -/
theorem eraseBodyInto_next_mono {n callerMembers currentMembers : Nat} [Zero F]
    (m : Module SourceSet n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (h : eraseBodyInto m caller current kind rename next stmts = some result) :
    next ≤ result.2 := by
  fun_induction eraseBodyInto generalizing result <;> simp_all <;>
    aesop (config := { warnOnNonterminal := false })
  all_goals
    calc
      _ ≤ _ + _ := Nat.le_add_right _ _
      _ ≤ _ := by assumption
      _ ≤ _ := by
        first
        | assumption
        | exact Nat.le_trans (emitReturnCopy_next_mono _ _ _ _ _) (by assumption)

/-! ## Function / module wrappers -/

/-- Lower one compute body in its own output context. -/
def eraseComputeFunc {n : Nat} [Zero F] (m : Module SourceSet n F) (i : Fin n) :
    Option (List (Stmt TargetSet
      ⟨n, i.val, (m.structs i).members.length⟩ F) × LocalVar) :=
  let fn := (m.structs i).compute
  eraseBodyInto m i i .compute id (funcVarBound fn) fn.body

/-- Lower one constrain body in its own output context. -/
def eraseConstrainFunc {n : Nat} [Zero F] (m : Module SourceSet n F) (i : Fin n) :
    Option (List (Stmt TargetSet
      ⟨n, i.val, (m.structs i).members.length⟩ F) × LocalVar) :=
  let fn := (m.structs i).constrain
  eraseBodyInto m i i .constrain id (funcVarBound fn) fn.body

/-- Lower both bodies of one struct, failing on malformed calls. -/
def eraseStruct {n : Nat} [Zero F] (m : Module SourceSet n F) (i : Fin n) :
    Option
      (List (Stmt TargetSet ⟨n, i.val, (m.structs i).members.length⟩ F) ×
       List (Stmt TargetSet ⟨n, i.val, (m.structs i).members.length⟩ F)) := do
  let compute ← eraseComputeFunc m i
  let constrain ← eraseConstrainFunc m i
  pure (compute.1, constrain.1)

/-- Package an erased body as a target `FuncDef` only after its executable
well-formedness checks have produced kernel-visible proofs. -/
def certifyErasedFunc {n i numMembers : Nat} {kind : Capability} [Zero F]
    (fn : FuncDef SourceSet n i F kind numMembers)
    (body : List (Stmt TargetSet ⟨n, i, numMembers⟩ F)) :
    Option (FuncDef TargetSet n i F kind numMembers) :=
  if hcaps : capsLE kind body = true then
    if hssa : isSSA (fun v => decide (v < fn.numParams)) body = true then
      some {
        numParams := fn.numParams
        body := body
        returnVar := fn.returnVar
        wf_caps := hcaps
        wf_ssa := hssa
      }
    else none
  else none

/-- Erase and certify one witness function. -/
def eraseComputeDef {n : Nat} [Zero F] (m : Module SourceSet n F) (i : Fin n) :
    Option (FuncDef TargetSet n i.val F .witness (m.structs i).members.length) := do
  let result ← eraseComputeFunc m i
  certifyErasedFunc (m.structs i).compute result.1

/-- Erase and certify one constraint function. -/
def eraseConstrainDef {n : Nat} [Zero F] (m : Module SourceSet n F) (i : Fin n) :
    Option (FuncDef TargetSet n i.val F .constraint (m.structs i).members.length) := do
  let result ← eraseConstrainFunc m i
  certifyErasedFunc (m.structs i).constrain result.1

set_option linter.flexible false in
/-- A certified constraint function retains the body returned by raw erasure. -/
theorem eraseConstrainDef_body {n : Nat} [Zero F] (m : Module SourceSet n F)
    (i : Fin n)
    (out : FuncDef TargetSet n i.val F .constraint (m.structs i).members.length)
    (h : eraseConstrainDef m i = some out) :
    ∃ result, eraseConstrainFunc m i = some result ∧ out.body = result.1 := by
  cases herase : eraseConstrainFunc m i with
  | none => simp [eraseConstrainDef, herase] at h
  | some result =>
    by_cases hcaps : capsLE Capability.constraint result.1 = true
    · by_cases hssa : isSSA
          (fun v => decide (v < (m.structs i).constrain.numParams))
          result.1 = true
      · simp [eraseConstrainDef, herase, certifyErasedFunc, hcaps, hssa] at h
        subst out
        exact ⟨result, rfl, rfl⟩
      · simp [eraseConstrainDef, herase, certifyErasedFunc, hcaps, hssa] at h
    · simp [eraseConstrainDef, herase, certifyErasedFunc, hcaps] at h

/-- Erase one struct and retain the original metadata. -/
def eraseStructDef {n : Nat} [Zero F] (m : Module SourceSet n F) (i : Fin n) :
    Option (StructDef TargetSet n i F) := do
  let compute ← eraseComputeDef m i
  let constrain ← eraseConstrainDef m i
  pure {
    name := (m.structs i).name
    members := (m.structs i).members
    compute := compute
    constrain := constrain
  }

/-- Erase a complete module when every struct erases and certifies.

This is intentionally partial: source `Module` currently guarantees SSA and
capabilities, but does not yet intrinsically encode call selector, arity, or
call-kind validity. -/
noncomputable def eraseModule {n : Nat} [Zero F] (m : Module SourceSet n F) :
    Option (Module TargetSet n F) := by
  classical
  exact if h : ∀ i, ∃ s, eraseStructDef m i = some s then
    some { structs := fun i => Classical.choose (h i) }
  else none

/-- A successful module erasure exposes the certified result selected for each
source struct. -/
theorem eraseModule_struct {n : Nat} [Zero F] (m : Module SourceSet n F)
    (out : Module TargetSet n F) (h : eraseModule m = some out) (i : Fin n) :
    eraseStructDef m i = some (out.structs i) := by
  classical
  unfold eraseModule at h
  split at h
  next hall =>
    simp only [Option.some.injEq] at h
    subst out
    exact Classical.choose_spec (hall i)
  next => simp at h

/-- A successful module erasure exposes each raw erased constraint body. -/
theorem eraseModule_constrain_body {n : Nat} [Zero F]
    (m : Module SourceSet n F) (out : Module TargetSet n F)
    (h : eraseModule m = some out) (i : Fin n) :
    ∃ (result : List (Stmt TargetSet
          ⟨n, i.val, (m.structs i).members.length⟩ F) × LocalVar)
      (compute : FuncDef TargetSet n i.val F .witness
          (m.structs i).members.length)
      (constrain : FuncDef TargetSet n i.val F .constraint
          (m.structs i).members.length),
      eraseConstrainFunc m i = some result ∧
      out.structs i = {
        name := (m.structs i).name
        members := (m.structs i).members
        compute := compute
        constrain := constrain
      } ∧
      constrain.body = result.1 := by
  have hs := eraseModule_struct m out h i
  cases hcompute : eraseComputeDef m i with
  | none => simp [eraseStructDef, hcompute] at hs
  | some compute =>
    cases hconstrain : eraseConstrainDef m i with
    | none => simp [eraseStructDef, hcompute, hconstrain] at hs
    | some constrain =>
      simp [eraseStructDef, hcompute, hconstrain] at hs
      obtain ⟨result, herase, hbody⟩ :=
        eraseConstrainDef_body m i constrain hconstrain
      exact ⟨result, compute, constrain, herase, hs.symm, hbody⟩

end Dialect.CallPass
