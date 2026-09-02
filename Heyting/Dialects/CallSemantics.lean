/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.CallPass
import Heyting.Core.StructuralPass

/-!
# Call-Aware Semantics for the Concrete Source Set

The generic `DialectSem` interface models local operations. Calls need the
enclosing handler family recursively, so their semantics live here at the
concrete module layer. Recursion is well founded because every call target is
strictly earlier than its enclosing struct.
-/

namespace Dialect.CallSemantics

open Dialect
open CallPass

variable {F : Type} [Field F]

/-! ## Call-free target semantics -/

/-- Generic handler family for the call-free target set. -/
abbrev targetHandlers (F : Type) [Field F] : HandlerFamily TargetSet F :=
  fun d =>
    match d, d.isLt with
    | ⟨0, _⟩, _ => by simpa [TargetSet] using Felt.sem F TargetSet
    | ⟨1, _⟩, _ => by simpa [TargetSet] using ConstrainEq.sem F TargetSet

/-- Execute a call-free target compute body. -/
def evalTargetComputeBody {γ : OpCtx}
    (stmts : List (Stmt TargetSet γ F)) (env : LocalVar → F) :
    Option (LocalVar → F) :=
  match stmts with
  | [] => some env
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ => evalTargetComputeBody rest (Felt.applyOp p env)
    | ⟨1, _⟩, _ => evalTargetComputeBody rest env

/-- Execute a call-free target constrain body. -/
def evalTargetConstrainBody {γ : OpCtx}
    (stmts : List (Stmt TargetSet γ F)) (env : LocalVar → F) : Prop :=
  match stmts with
  | [] => True
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ => evalTargetConstrainBody rest (Felt.applyOp p env)
    | ⟨1, _⟩, _ =>
      match p with
      | .eq src1 src2 =>
        env src1 = env src2 ∧ evalTargetConstrainBody rest env

/-- Final environment after executing a call-free target constrain body. -/
def evalTargetConstrainEnv {γ : OpCtx}
    (stmts : List (Stmt TargetSet γ F)) (env : LocalVar → F) :
    LocalVar → F :=
  match stmts with
  | [] => env
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ => evalTargetConstrainEnv rest (Felt.applyOp p env)
    | ⟨1, _⟩, _ => evalTargetConstrainEnv rest env

/-- Compute and constrain-state target evaluators thread the same environment. -/
theorem evalTargetComputeBody_eq_constrainEnv {γ : OpCtx}
    (stmts : List (Stmt TargetSet γ F)) (env : LocalVar → F) :
    evalTargetComputeBody stmts env = some (evalTargetConstrainEnv stmts env) := by
  induction stmts generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simpa [evalTargetComputeBody, evalTargetConstrainEnv] using
          ih (Felt.applyOp p env)
      · cases p
        simpa [evalTargetComputeBody, evalTargetConstrainEnv] using ih env

/-- The executable target evaluator agrees with generic dialect compute semantics. -/
theorem evalTargetComputeBody_eq_generic {n : Nat} {γ : OpCtx}
    (ctx : SemCtx TargetSet n F) (stmts : List (Stmt TargetSet γ F))
    (env : LocalVar → F) :
    evalTargetComputeBody stmts env =
      Dialect.evalComputeBody (targetHandlers F) ctx stmts env := by
  induction stmts generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simp [evalTargetComputeBody, Dialect.evalComputeBody,
          Dialect.evalComputeStep, targetHandlers, Felt.sem, ih]
      · cases p
        simp [evalTargetComputeBody, Dialect.evalComputeBody,
          Dialect.evalComputeStep, targetHandlers, ConstrainEq.sem, ih]

/-- The executable target evaluator agrees with generic dialect constrain semantics. -/
theorem evalTargetConstrainBody_iff_generic {n : Nat} {γ : OpCtx}
    (ctx : SemCtx TargetSet n F) (stmts : List (Stmt TargetSet γ F))
    (env : LocalVar → F) :
    evalTargetConstrainBody stmts env ↔
      Dialect.evalConstrainBody (targetHandlers F) ctx stmts env := by
  induction stmts generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simp [evalTargetConstrainBody, Dialect.evalConstrainBody,
          Dialect.evalConstrainStep, targetHandlers, Felt.sem, ih]
      · cases p
        simp [evalTargetConstrainBody, Dialect.evalConstrainBody,
          Dialect.evalConstrainStep, targetHandlers, ConstrainEq.sem, ih]

/-- Executable target constrain-state threading agrees with generic semantics. -/
theorem evalTargetConstrainEnv_eq_generic {n : Nat} {γ : OpCtx}
    (ctx : SemCtx TargetSet n F) (stmts : List (Stmt TargetSet γ F))
    (env : LocalVar → F) :
    evalTargetConstrainEnv stmts env =
      Dialect.evalConstrainEnv (targetHandlers F) ctx stmts env := by
  induction stmts generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simp [evalTargetConstrainEnv, Dialect.evalConstrainEnv,
          Dialect.evalConstrainStep, targetHandlers, Felt.sem, ih]
      · cases p
        simp [evalTargetConstrainEnv, Dialect.evalConstrainEnv,
          Dialect.evalConstrainStep, targetHandlers, ConstrainEq.sem, ih]

/-- Target compute execution composes over concatenated lowered fragments. -/
theorem evalTargetComputeBody_append {γ : OpCtx}
    (l₁ l₂ : List (Stmt TargetSet γ F)) (env : LocalVar → F) :
    evalTargetComputeBody (l₁ ++ l₂) env =
      (evalTargetComputeBody l₁ env).bind (evalTargetComputeBody l₂) := by
  induction l₁ generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simp [evalTargetComputeBody, ih]
      · cases p
        simp [evalTargetComputeBody, ih]

/-- Call-free target compute execution is total. -/
theorem evalTargetComputeBody_total {γ : OpCtx}
    (stmts : List (Stmt TargetSet γ F)) (env : LocalVar → F) :
    ∃ out, evalTargetComputeBody stmts env = some out := by
  induction stmts generalizing env with
  | nil => exact ⟨env, rfl⟩
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · exact ih (Felt.applyOp p env)
      · cases p
        exact ih env

/-- Every statement destination lies at or above `floor`. -/
def DestinationsAbove {Δ : DialectSet} {γ : OpCtx} {F : Type}
    (floor : LocalVar) (stmts : List (Stmt Δ γ F)) : Prop :=
  ∀ stmt ∈ stmts, ∀ d, stmt.dest = some d → floor ≤ d

omit [Field F] in
theorem DestinationsAbove.tail {Δ : DialectSet} {γ : OpCtx} {F : Type}
    {floor : LocalVar} {head : Stmt Δ γ F} {tail : List (Stmt Δ γ F)}
    (h : DestinationsAbove floor (head :: tail)) :
    DestinationsAbove floor tail := by
  intro stmt hmem d hdest
  exact h stmt (by simp [hmem]) d hdest

/-- Target compute execution preserves every local below all destinations. -/
theorem evalTargetComputeBody_frame_below {γ : OpCtx}
    (stmts : List (Stmt TargetSet γ F)) (floor v : LocalVar)
    (env : LocalVar → F) (habove : DestinationsAbove floor stmts)
    (hv : v < floor) :
    (evalTargetComputeBody stmts env).map (fun out => out v) = some (env v) := by
  induction stmts generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · have hdest : floor ≤ Felt.destVar p := by
          apply habove (.op ⟨0, hd⟩ p) (by simp) (Felt.destVar p)
          exact Felt.dest_eq p
        have hne : v ≠ Felt.destVar p :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hdest)
        rw [evalTargetComputeBody]
        rw [ih (Felt.applyOp p env) (habove.tail)]
        rw [Felt.applyOp_at_other _ _ _ hne]
      · cases p
        rw [evalTargetComputeBody]
        exact ih env habove.tail

omit [Field F] in
theorem destinationsAbove_append {Δ : DialectSet} {γ : OpCtx} {F : Type}
    {floor : LocalVar} {left right : List (Stmt Δ γ F)}
    (hleft : DestinationsAbove floor left)
    (hright : DestinationsAbove floor right) :
    DestinationsAbove floor (left ++ right) := by
  intro stmt hmem d hdest
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft stmt hmem d hdest
  · exact hright stmt hmem d hdest

omit [Field F] in
theorem destinationsAbove_lowerFeltInto {γ γ' : OpCtx}
    {floor : LocalVar} (rename : LocalVar → LocalVar) (op : Felt.Op γ F)
    (hdest : floor ≤ rename (Felt.destVar op)) :
    DestinationsAbove floor [lowerFeltInto (γ' := γ') rename op] := by
  intro stmt hmem d hstmtDest
  simp only [List.mem_singleton] at hmem
  subst stmt
  change Felt.dest (lowerFeltOp (γ' := γ') rename op) = some d at hstmtDest
  rw [Felt.dest_eq] at hstmtDest
  have hdestEq : d = rename (Felt.destVar op) := by
    have h := Option.some.inj hstmtDest
    rw [lowerFeltOp_destVar] at h
    exact h.symm
  simpa [hdestEq] using hdest

omit [Field F] in
theorem destinationsAbove_lowerConstrInto {γ γ' : OpCtx}
    {floor : LocalVar} (rename : LocalVar → LocalVar)
    (op : ConstrainEq.Op γ F) :
    DestinationsAbove floor [lowerConstrInto (γ' := γ') rename op] := by
  intro stmt hmem d hstmtDest
  simp only [List.mem_singleton] at hmem
  subst stmt
  cases op with
  | eq a b =>
    change none = some d at hstmtDest
    contradiction

omit [Field F] in
theorem destinationsAbove_emitReturnCopy {γ : OpCtx} [Zero F]
    {floor next : LocalVar} (dest returnVar : Option LocalVar)
    (calleeRename callerRename : LocalVar → LocalVar)
    (hnext : floor ≤ next)
    (hdest : ∀ d, dest = some d → floor ≤ callerRename d) :
    DestinationsAbove floor
      (emitReturnCopy (γ := γ) (F := F) dest returnVar
        calleeRename callerRename next).1 := by
  cases dest with
  | none => simp [DestinationsAbove, emitReturnCopy]
  | some d =>
    cases returnVar with
    | none => simp [DestinationsAbove, emitReturnCopy]
    | some r =>
      intro stmt hmem out hstmtDest
      simp only [emitReturnCopy, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · change some next = some out at hstmtDest
        simpa [Option.some.inj hstmtDest] using hnext
      · change some (callerRename d) = some out at hstmtDest
        simpa [Option.some.inj hstmtDest] using hdest d rfl

set_option linter.flexible false in
/-- Recursive erasure preserves a destination floor supplied by the current
renaming. This is the syntactic frame invariant used by call simulation. -/
theorem eraseBodyInto_destinationsAbove
    {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next floor : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (hnext : floor ≤ next)
    (hframe : ∀ stmt ∈ stmts, ∀ d, stmt.dest = some d → floor ≤ rename d)
    (herase : eraseBodyInto m caller current kind rename next stmts = some result) :
    DestinationsAbove floor result.1 := by
  fun_induction eraseBodyInto generalizing floor result <;> simp_all
  all_goals
    aesop (config := { warnOnNonterminal := false })
  · simp [DestinationsAbove]
  · have hcalleeFrame : ∀ stmt ∈ fn.body, ∀ d, stmt.dest = some d →
        floor ≤ inlineVar rename args fn.numParams next h_1 d := by
      intro stmt hmem d hdest
      exact Nat.le_trans hnext
        (inlineVar_stmt_dest_ge_base fn rename args next h_1 hmem hdest)
    have hcalleeAbove : DestinationsAbove floor tail :=
      ih2 floor (Nat.le_trans hnext (Nat.le_add_right next _)) hcalleeFrame
    have hafter : floor ≤ afterTail := by
      exact Nat.le_trans (Nat.le_trans hnext (Nat.le_add_right next _))
        (eraseBodyInto_next_mono m caller (Call.moduleTarget target current_1.isLt)
          .compute (inlineVar rename args fn.numParams next h_1)
          (next + funcVarBound fn) fn.body (tail, afterTail) x)
    have hcopyAbove := destinationsAbove_emitReturnCopy
      (F := F) (γ := ⟨n, caller.val, callerMembers⟩)
      dest fn.returnVar (inlineVar rename args fn.numParams next h_1) rename
      hafter (fun d hd => by
        subst dest
        exact left d rfl)
    have htailAbove : DestinationsAbove floor tail_1 :=
      ih1 floor (Nat.le_trans hafter
        (emitReturnCopy_next_mono dest fn.returnVar
          (inlineVar rename args fn.numParams next h_1) rename afterTail)) right
    exact destinationsAbove_append hcalleeAbove
      (destinationsAbove_append hcopyAbove htailAbove)
  · have hcalleeFrame : ∀ stmt ∈ fn.body, ∀ d, stmt.dest = some d →
        floor ≤ inlineVar rename args fn.numParams next h_1 d := by
      intro stmt hmem d hdest
      exact Nat.le_trans hnext
        (inlineVar_stmt_dest_ge_base fn rename args next h_1 hmem hdest)
    have hcalleeAbove : DestinationsAbove floor tail :=
      ih2 floor (Nat.le_trans hnext (Nat.le_add_right next _)) hcalleeFrame
    have hafter : floor ≤ afterTail := by
      exact Nat.le_trans (Nat.le_trans hnext (Nat.le_add_right next _))
        (eraseBodyInto_next_mono m caller (Call.moduleTarget target current_1.isLt)
          .constrain (inlineVar rename args fn.numParams next h_1)
          (next + funcVarBound fn) fn.body (tail, afterTail) x)
    exact destinationsAbove_append hcalleeAbove (ih1 floor hafter right)
  · change DestinationsAbove floor ([lowerFeltInto rename p] ++ tail)
    apply destinationsAbove_append
    · apply destinationsAbove_lowerFeltInto
      apply left (Felt.destVar p)
      exact Felt.dest_eq p
    · exact ih1 floor hnext right
  · change DestinationsAbove floor ([lowerConstrInto rename p] ++ tail)
    exact destinationsAbove_append (destinationsAbove_lowerConstrInto rename p)
      (ih1 floor hnext right)

/-- Erased target execution preserves storage below the supplied frame floor. -/
theorem eraseBodyInto_target_frame_below
    {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next floor : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (hnext : floor ≤ next)
    (hframe : ∀ stmt ∈ stmts, ∀ d, stmt.dest = some d → floor ≤ rename d)
    (herase : eraseBodyInto m caller current kind rename next stmts = some result)
    (env : LocalVar → F) {v : LocalVar} (hv : v < floor) :
    (evalTargetComputeBody result.1 env).map (fun out ↦ out v) = some (env v) := by
  apply evalTargetComputeBody_frame_below result.1 floor v env
  · exact eraseBodyInto_destinationsAbove m caller current kind rename next floor
      stmts result hnext hframe herase
  · exact hv

/-- Inlined callee execution cannot overwrite caller locals below its base. -/
theorem eraseFuncBodyInto_inlineVar_target_frame
    {n callerMembers currentMembers : Nat} {cap : Capability}
    (m : Module SourceSet n F) (caller current : Fin n) (kind : BodyKind)
    (fn : FuncDef SourceSet n current.val F cap currentMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (herase : eraseBodyInto m caller current kind
      (inlineVar callerRename args fn.numParams base hargs)
      (base + funcVarBound fn) fn.body = some result)
    (env : LocalVar → F) {v : LocalVar} (hv : v < base) :
    (evalTargetComputeBody result.1 env).map (fun out ↦ out v) = some (env v) := by
  apply eraseBodyInto_target_frame_below m caller current kind
    (inlineVar callerRename args fn.numParams base hargs)
    (base + funcVarBound fn) base fn.body result
  · exact Nat.le_add_right base _
  · exact renameFrameInvariant_inlineVar fn callerRename args base hargs
  · exact herase
  · exact hv

/-- Target constraint truth splits across concatenated lowered fragments. -/
theorem evalTargetConstrainBody_append {γ : OpCtx}
    (l₁ l₂ : List (Stmt TargetSet γ F))
    (env : LocalVar → F) :
    evalTargetConstrainBody (l₁ ++ l₂) env ↔
      evalTargetConstrainBody l₁ env ∧
      evalTargetConstrainBody l₂ (evalTargetConstrainEnv l₁ env) := by
  induction l₁ generalizing env with
  | nil => simp [evalTargetConstrainBody, evalTargetConstrainEnv]
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simpa [evalTargetConstrainBody, evalTargetConstrainEnv] using
          ih (Felt.applyOp p env)
      · cases p with
        | eq a b =>
          simp [evalTargetConstrainBody, evalTargetConstrainEnv, ih, and_assoc]

/-- Target constraint-state threading composes over concatenated fragments. -/
theorem evalTargetConstrainEnv_append {γ : OpCtx}
    (l₁ l₂ : List (Stmt TargetSet γ F)) (env : LocalVar → F) :
    evalTargetConstrainEnv (l₁ ++ l₂) env =
      evalTargetConstrainEnv l₂ (evalTargetConstrainEnv l₁ env) := by
  induction l₁ generalizing env with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | op d p =>
      rcases d with ⟨d, hd⟩
      have hd' : d = 0 ∨ d = 1 := by
        simp [TargetSet] at hd
        omega
      rcases hd' with rfl | rfl
      · simp [evalTargetConstrainEnv, ih]
      · cases p
        simp [evalTargetConstrainEnv, ih]

/-! ## Inlining simulation primitives -/

/-- Renaming a felt op preserves the value computed from agreeing reads. -/
theorem evalVal_lowerFeltOp {γ γ' : OpCtx} (rename : LocalVar → LocalVar)
    (op : Felt.Op γ F) (source target : LocalVar → F)
    (hreads : ∀ v ∈ Felt.reads op, target (rename v) = source v) :
    Felt.evalVal (lowerFeltOp (γ' := γ') rename op) target =
      Felt.evalVal op source := by
  cases op with
  | add _ a b | sub _ a b | mul _ a b | div _ a b =>
    simp only [lowerFeltOp, Felt.evalVal]
    rw [hreads a (by simp [Felt.reads]), hreads b (by simp [Felt.reads])]
  | neg _ a | inv _ a =>
    simp only [lowerFeltOp, Felt.evalVal]
    rw [hreads a (by simp [Felt.reads])]
  | const _ _ => rfl

omit [Field F] in
/-- Renamed equality constraints preserve truth under environment agreement. -/
theorem lowerConstrOp_holds_iff {γ γ' : OpCtx}
    (rename : LocalVar → LocalVar) (op : ConstrainEq.Op γ F)
    (source target : LocalVar → F)
    (hagrees : ∀ v ∈ ConstrainEq.reads op, target (rename v) = source v) :
    (match lowerConstrOp (γ' := γ') rename op with
      | .eq a b => target a = target b) ↔
    (match op with | .eq a b => source a = source b) := by
  cases op with
  | eq a b =>
    simp only [lowerConstrOp]
    rw [hagrees a (by simp [ConstrainEq.reads]),
      hagrees b (by simp [ConstrainEq.reads])]

/-- Source and target environments agree through `rename` below `bound`. -/
def EnvAgreesBelow (rename : LocalVar → LocalVar) (bound : LocalVar)
    (source target : LocalVar → F) : Prop :=
  ∀ v, v < bound → target (rename v) = source v

/-- Source and target environments agree on the current SSA-defined set. -/
def EnvAgreesOn (defined : LocalVar → Bool) (rename : LocalVar → LocalVar)
    (source target : LocalVar → F) : Prop :=
  ∀ v, defined v = true → target (rename v) = source v

/-- Executing an erased inlined callee preserves caller environment agreement
for every protected caller local mapped below the callee base. -/
theorem eraseFuncBodyInto_inlineVar_preserves_caller_agreement
    {n callerMembers currentMembers : Nat} {cap : Capability}
    (m : Module SourceSet n F) (caller current : Fin n) (kind : BodyKind)
    (fn : FuncDef SourceSet n current.val F cap currentMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (herase : eraseBodyInto m caller current kind
      (inlineVar callerRename args fn.numParams base hargs)
      (base + funcVarBound fn) fn.body = some result)
    (defined : LocalVar → Bool) (source target : LocalVar → F)
    (hbelow : ∀ v, defined v = true → callerRename v < base)
    (hagrees : EnvAgreesOn defined callerRename source target) :
    ∃ out,
      evalTargetComputeBody result.1 target = some out ∧
      EnvAgreesOn defined callerRename source out := by
  obtain ⟨out, hout⟩ := evalTargetComputeBody_total result.1 target
  refine ⟨out, hout, ?_⟩
  intro v hv
  have hframe := eraseFuncBodyInto_inlineVar_target_frame
    m caller current kind fn callerRename args base hargs result herase target
    (hbelow v hv)
  rw [hout] at hframe
  exact (Option.some.inj hframe).trans (hagrees v hv)

omit [Field F] in
theorem EnvAgreesBelow.mono {rename : LocalVar → LocalVar}
    {small large : LocalVar} {source target : LocalVar → F}
    (h : EnvAgreesBelow rename large source target) (hle : small ≤ large) :
    EnvAgreesBelow rename small source target := by
  intro v hv
  exact h v (Nat.lt_of_lt_of_le hv hle)

/-- Parameter substitution establishes initial callee/caller agreement. -/
theorem envAgreesBelow_bindArgs_inlineVar
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (numParams base : LocalVar) (hargs : args.length = numParams)
    (source target : LocalVar → F)
    (hcaller : ∀ a ∈ args, target (callerRename a) = source a) :
    EnvAgreesBelow
      (inlineVar callerRename args numParams base hargs)
      numParams (Call.bindArgs source args 0) target := by
  intro v hv
  rw [inlineVar_param callerRename args numParams base v hargs hv]
  rw [Call.bindArgs_lt source args 0 (by simpa [hargs] using hv)]
  exact hcaller _ (List.get_mem args ⟨v, by simpa [hargs] using hv⟩)

/-- Parameter substitution establishes agreement on the initial SSA set. -/
theorem envAgreesOn_bindArgs_inlineVar
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (numParams base : LocalVar) (hargs : args.length = numParams)
    (source target : LocalVar → F)
    (hcaller : ∀ a ∈ args, target (callerRename a) = source a) :
    EnvAgreesOn (fun v => decide (v < numParams))
      (inlineVar callerRename args numParams base hargs)
      (Call.bindArgs source args 0) target := by
  intro v hv
  apply envAgreesBelow_bindArgs_inlineVar callerRename args numParams base hargs
    source target hcaller v
  simpa using hv

/-- SSA-defined call arguments suffice to initialize callee agreement. -/
theorem envAgreesOn_bindArgs_inlineVar_of_all
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (numParams base : LocalVar) (hargs : args.length = numParams)
    (defined : LocalVar → Bool) (source target : LocalVar → F)
    (hargsDefined : args.all defined = true)
    (hcaller : EnvAgreesOn defined callerRename source target) :
    EnvAgreesOn (fun v => decide (v < numParams))
      (inlineVar callerRename args numParams base hargs)
      (Call.bindArgs source args 0) target := by
  apply envAgreesOn_bindArgs_inlineVar callerRename args numParams base hargs
  intro a ha
  exact hcaller a ((List.all_eq_true.mp hargsDefined) a ha)

omit [Field F] in
/-- Renamed return binding extends caller agreement to the call destination. -/
theorem bindReturn_rename_agreesOn
    (defined : LocalVar → Bool) (rename : LocalVar → LocalVar)
    (d : LocalVar) (sourceReturn targetReturn : F)
    (source target : LocalVar → F)
    (hagrees : EnvAgreesOn defined rename source target)
    (hreturn : targetReturn = sourceReturn)
    (hseparate : ∀ v, v ≠ d → rename v ≠ rename d) :
    EnvAgreesOn (fun v => defined v || v == d) rename
      (Call.bindReturn (some d) (some sourceReturn) source)
      (Call.bindReturn (some (rename d)) (some targetReturn) target) := by
  intro v hvDefined
  simp only [Bool.or_eq_true, beq_iff_eq] at hvDefined
  by_cases hvDest : v = d
  · subst v
    simp [Call.bindReturn, hreturn]
  · simp [Call.bindReturn, hvDest, hseparate v hvDest,
      hagrees v (hvDefined.resolve_right hvDest)]

omit [Field F] in
/-- Successful return checking makes the declared return observable through
the final environment-agreement invariant.
-/
theorem computeReturnSupported_value_agree {n i numMembers : Nat}
    (fn : FuncDef SourceSet n i F .witness numMembers) (d : LocalVar)
    (rename : LocalVar → LocalVar) (source target : LocalVar → F)
    (hsupported : computeReturnSupported fn (some d) = true)
    (hagrees : EnvAgreesOn
      (definedLocalsAfter (fun v => decide (v < fn.numParams)) fn.body)
      rename source target) :
    ∃ r, fn.returnVar = some r ∧ target (rename r) = source r := by
  obtain ⟨r, hr, hdefined⟩ := computeReturnSupported_some fn d hsupported
  exact ⟨r, hr, hagrees r hdefined⟩

/-- One renamed felt step preserves environment agreement when its destination
remains distinct from every other represented source local. SSA plus reserved
callee storage will discharge this separation premise in the body theorem.
-/
theorem applyOp_lowerFeltOp_agrees {γ γ' : OpCtx}
    (rename : LocalVar → LocalVar) (op : Felt.Op γ F)
    (source target : LocalVar → F)
    (hagrees : ∀ v, target (rename v) = source v)
    (hseparate : ∀ v, v ≠ Felt.destVar op →
      rename v ≠ rename (Felt.destVar op)) :
    ∀ v,
      Felt.applyOp (lowerFeltOp (γ' := γ') rename op) target (rename v) =
        Felt.applyOp op source v := by
  intro v
  by_cases hv : v = Felt.destVar op
  · subst v
    have hdest : rename (Felt.destVar op) =
        Felt.destVar (lowerFeltOp (γ' := γ') rename op) := by
      symm
      exact lowerFeltOp_destVar rename op
    rw [hdest, Felt.applyOp_at_dest, Felt.applyOp_at_dest]
    exact evalVal_lowerFeltOp rename op source target
      (fun x _ => hagrees x)
  · have hsep : rename v ≠
        Felt.destVar (lowerFeltOp (γ' := γ') rename op) := by
      simpa using hseparate v hv
    rw [Felt.applyOp_at_other _ _ _ hsep,
      Felt.applyOp_at_other _ _ _ hv]
    exact hagrees v

/-- One renamed felt step extends agreement from the current SSA set to its
new destination.
-/
theorem applyOp_lowerFeltOp_agreesOn {γ γ' : OpCtx}
    (defined : LocalVar → Bool) (rename : LocalVar → LocalVar)
    (op : Felt.Op γ F) (source target : LocalVar → F)
    (hreads : (Felt.reads op).all defined = true)
    (hagrees : EnvAgreesOn defined rename source target)
    (hseparate : ∀ v, v ≠ Felt.destVar op →
      rename v ≠ rename (Felt.destVar op)) :
    EnvAgreesOn (fun v => defined v || v == Felt.destVar op) rename
      (Felt.applyOp op source)
      (Felt.applyOp (lowerFeltOp (γ' := γ') rename op) target) := by
  have hreadAgree : ∀ v ∈ Felt.reads op, target (rename v) = source v := by
    intro v hv
    exact hagrees v ((List.all_eq_true.mp hreads) v hv)
  intro v hvDefined
  simp only [Bool.or_eq_true, beq_iff_eq] at hvDefined
  by_cases hvDest : v = Felt.destVar op
  · subst v
    have hdest : rename (Felt.destVar op) =
        Felt.destVar (lowerFeltOp (γ' := γ') rename op) := by
      symm
      exact lowerFeltOp_destVar rename op
    rw [hdest, Felt.applyOp_at_dest, Felt.applyOp_at_dest]
    exact evalVal_lowerFeltOp rename op source target hreadAgree
  · have hsep : rename v ≠
        Felt.destVar (lowerFeltOp (γ' := γ') rename op) := by
      simpa using hseparate v hvDest
    rw [Felt.applyOp_at_other _ _ _ hsep,
      Felt.applyOp_at_other _ _ _ hvDest]
    exact hagrees v (hvDefined.resolve_right hvDest)

/-- Combined local simulation rule for a felt statement inside an SSA callee. -/
theorem applyOp_lowerFeltOp_inlineVar_agrees {n i numMembers : Nat}
    {kind : Capability} (fn : FuncDef SourceSet n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    (hparams : ∀ k (hk : k < fn.numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base)
    (op : Felt.Op ⟨n, i, numMembers⟩ F)
    (hmem : (Stmt.op feltSourceIx op :
      Stmt SourceSet ⟨n, i, numMembers⟩ F) ∈ fn.body)
    (source target : LocalVar → F)
    (hagrees : ∀ v,
      target (inlineVar callerRename args fn.numParams base hargs v) = source v) :
    ∀ v,
      Felt.applyOp
          (lowerFeltOp (γ' := ⟨n, i, numMembers⟩)
            (inlineVar callerRename args fn.numParams base hargs) op)
          target (inlineVar callerRename args fn.numParams base hargs v) =
        Felt.applyOp op source v := by
  apply applyOp_lowerFeltOp_agrees
  · exact hagrees
  · apply inlineVar_stmt_dest_separate fn callerRename args base hargs hparams hmem
    change Felt.sig.dest op = some (Felt.destVar op)
    exact Felt.dest_eq op

/-- SSA-aware local Felt rule used by recursive body simulation. -/
theorem applyOp_lowerFeltOp_inlineVar_agreesOn {n i numMembers : Nat}
    {kind : Capability} (fn : FuncDef SourceSet n i F kind numMembers)
    (callerRename : LocalVar → LocalVar) (args : List LocalVar)
    (base : LocalVar) (hargs : args.length = fn.numParams)
    (hparams : ∀ k (hk : k < fn.numParams),
      callerRename (args.get ⟨k, by simpa [hargs] using hk⟩) < base)
    (defined : LocalVar → Bool) (op : Felt.Op ⟨n, i, numMembers⟩ F)
    (hmem : (Stmt.op feltSourceIx op :
      Stmt SourceSet ⟨n, i, numMembers⟩ F) ∈ fn.body)
    (source target : LocalVar → F)
    (hreads : (Felt.reads op).all defined = true)
    (hagrees : EnvAgreesOn defined
      (inlineVar callerRename args fn.numParams base hargs) source target) :
    EnvAgreesOn (fun v => defined v || v == Felt.destVar op)
      (inlineVar callerRename args fn.numParams base hargs)
      (Felt.applyOp op source)
      (Felt.applyOp
        (lowerFeltOp (γ' := ⟨n, i, numMembers⟩)
          (inlineVar callerRename args fn.numParams base hargs) op)
        target) := by
  apply applyOp_lowerFeltOp_agreesOn defined
  · exact hreads
  · exact hagrees
  · apply inlineVar_stmt_dest_separate fn callerRename args base hargs hparams hmem
    change Felt.sig.dest op = some (Felt.destVar op)
    exact Felt.dest_eq op

/-- Executing one lowered felt statement performs its renamed field update. -/
@[simp] theorem evalTargetComputeBody_lowerFeltInto {γ γ' : OpCtx}
    (rename : LocalVar → LocalVar) (op : Felt.Op γ F)
    (env : LocalVar → F) :
    evalTargetComputeBody [lowerFeltInto (γ' := γ') rename op] env =
      some (Felt.applyOp (lowerFeltOp (γ' := γ') rename op) env) := by
  change some (Felt.applyOp (lowerFeltOp (γ' := γ') rename op) env) = _
  rfl

/-- Executing one lowered felt constraint statement threads its field update. -/
@[simp] theorem evalTargetConstrainEnv_lowerFeltInto {γ γ' : OpCtx}
    (rename : LocalVar → LocalVar) (op : Felt.Op γ F)
    (env : LocalVar → F) :
    evalTargetConstrainEnv [lowerFeltInto (γ' := γ') rename op] env =
      Felt.applyOp (lowerFeltOp (γ' := γ') rename op) env := by
  change Felt.applyOp (lowerFeltOp (γ' := γ') rename op) env = _
  rfl

/-- Executing one lowered equality emits exactly its source equality. -/
theorem evalTargetConstrainBody_lowerConstrInto_iff {γ γ' : OpCtx}
    (rename : LocalVar → LocalVar) (op : ConstrainEq.Op γ F)
    (source target : LocalVar → F)
    (hagrees : ∀ v ∈ ConstrainEq.reads op, target (rename v) = source v) :
    evalTargetConstrainBody [lowerConstrInto (γ' := γ') rename op] target ↔
      (match op with | .eq a b => source a = source b) := by
  change (match lowerConstrOp (γ' := γ') rename op with
    | .eq a b => target a = target b) ∧ True ↔ _
  simpa using lowerConstrOp_holds_iff rename op source target hagrees

/-- Lowered equality statements leave constraint state unchanged. -/
@[simp] theorem evalTargetConstrainEnv_lowerConstrInto {γ γ' : OpCtx}
    (rename : LocalVar → LocalVar) (op : ConstrainEq.Op γ F)
    (env : LocalVar → F) :
    evalTargetConstrainEnv [lowerConstrInto (γ' := γ') rename op] env = env := by
  cases op
  rfl

/-- Explicit return-copy code agrees with source return binding on old locals. -/
theorem evalTargetComputeBody_emitReturnCopy_some_below {γ : OpCtx}
    (d r : LocalVar) (calleeRename callerRename : LocalVar → LocalVar)
    (next : LocalVar) (env : LocalVar → F) (v : LocalVar)
    (hv : v < next) (hrNext : calleeRename r ≠ next) :
    (evalTargetComputeBody
      (emitReturnCopy (γ := γ) (F := F) (some d) (some r)
        calleeRename callerRename next).1 env).map (fun out => out v) =
      some (Call.bindReturn (some (callerRename d))
        (some (env (calleeRename r))) env v) := by
  change (some (Felt.applyOp (.add (callerRename d) (calleeRename r) next)
    (Felt.applyOp (.const next 0) env))).map (fun out => out v) = _
  have hvNext : v ≠ next := Nat.ne_of_lt hv
  by_cases hvDest : v = callerRename d
  · subst v
    simp [Felt.applyOp, Felt.evalVal, Felt.destVar, Call.bindReturn, hrNext]
  · simp [Felt.applyOp, Felt.destVar, Call.bindReturn, hvDest, hvNext]

/-- Return-copy execution produces an environment matching renamed return
binding on every pre-existing local.
-/
theorem evalTargetComputeBody_emitReturnCopy_some_agrees_below {γ : OpCtx}
    (d r : LocalVar) (calleeRename callerRename : LocalVar → LocalVar)
    (next : LocalVar) (env : LocalVar → F)
    (hrNext : calleeRename r ≠ next) :
    ∃ out,
      evalTargetComputeBody
        (emitReturnCopy (γ := γ) (F := F) (some d) (some r)
          calleeRename callerRename next).1 env = some out ∧
      ∀ v, v < next →
        out v = Call.bindReturn (some (callerRename d))
          (some (env (calleeRename r))) env v := by
  let out := Felt.applyOp (.add (γ := γ) (callerRename d) (calleeRename r) next)
    (Felt.applyOp (.const (γ := γ) next 0) env)
  refine ⟨out, ?_, ?_⟩
  · change some out = some out
    rfl
  · intro v hv
    have h := evalTargetComputeBody_emitReturnCopy_some_below (γ := γ)
      d r calleeRename callerRename next env v hv hrNext
    change (some out).map (fun result => result v) = some _ at h
    exact Option.some.inj h

/-- Executed return-copy code extends source/target agreement to the caller
destination while preserving every previously defined caller local.
-/
theorem evalTargetComputeBody_emitReturnCopy_agreesOn {γ : OpCtx}
    (defined : LocalVar → Bool)
    (d r : LocalVar) (calleeRename callerRename : LocalVar → LocalVar)
    (next : LocalVar) (source target : LocalVar → F)
    (sourceReturn : F)
    (hagrees : EnvAgreesOn defined callerRename source target)
    (hreturn : target (calleeRename r) = sourceReturn)
    (hdefinedBelow : ∀ v, defined v = true → callerRename v < next)
    (hdBelow : callerRename d < next)
    (hseparate : ∀ v, v ≠ d → callerRename v ≠ callerRename d)
    (hrNext : calleeRename r ≠ next) :
    ∃ out,
      evalTargetComputeBody
        (emitReturnCopy (γ := γ) (F := F) (some d) (some r)
          calleeRename callerRename next).1 target = some out ∧
      EnvAgreesOn (fun v => defined v || v == d) callerRename
        (Call.bindReturn (some d) (some sourceReturn) source) out := by
  obtain ⟨out, hout, hcopy⟩ :=
    evalTargetComputeBody_emitReturnCopy_some_agrees_below (γ := γ)
      d r calleeRename callerRename next target hrNext
  refine ⟨out, hout, ?_⟩
  have hbound := bindReturn_rename_agreesOn defined callerRename d
    sourceReturn (target (calleeRename r)) source target hagrees hreturn hseparate
  intro v hv
  have hvCases : defined v = true ∨ v = d := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using hv
  rw [hcopy (callerRename v) (by
    rcases hvCases with hOld | rfl
    · exact hdefinedBelow v hOld
    · exact hdBelow)]
  exact hbound v hv

/-- Execute a concrete source-set compute body, including calls to earlier structs. -/
def evalComputeBody {n numMembers : Nat} (m : Module SourceSet n F) (i : Fin n)
    (stmts : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) : Option (LocalVar → F) :=
  match stmts with
  | [] => some env
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ =>
      match p with
      | .call dest target sel args =>
        if Call.selectorSupported sel then
          let callee := Call.targetStructAt m i target
          let result :=
            (evalComputeBody m (Call.moduleTarget target i.isLt) callee.compute.body
              (Call.bindArgs env args 0)).map
              (fun calleeEnv => readReturn callee.compute.returnVar calleeEnv)
          (Call.computeStep dest result env).bind (evalComputeBody m i rest)
        else
          none
    | ⟨1, _⟩, _ =>
      (some (Felt.applyOp p env)).bind (evalComputeBody m i rest)
    | ⟨2, _⟩, _ =>
      (some env).bind (evalComputeBody m i rest)
termination_by (i.val, stmts.length)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      simp_wf
    | apply Prod.Lex.left
      simp [Call.moduleTarget, target.isLt]

/-- Execute a concrete source-set constrain body, including calls to earlier structs. -/
def evalConstrainBody {n numMembers : Nat} (m : Module SourceSet n F) (i : Fin n)
    (stmts : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) : Prop :=
  match stmts with
  | [] => True
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ =>
      match p with
      | .call _ target sel args =>
        if Call.selectorSupported sel then
          let callee := Call.targetStructAt m i target
          evalConstrainBody m (Call.moduleTarget target i.isLt) callee.constrain.body
            (Call.bindArgs env args 0) ∧
          evalConstrainBody m i rest env
        else
          False
    | ⟨1, _⟩, _ =>
      evalConstrainBody m i rest (Felt.applyOp p env)
    | ⟨2, _⟩, _ =>
      match p with
      | .eq src1 src2 =>
        env src1 = env src2 ∧ evalConstrainBody m i rest env
termination_by (i.val, stmts.length)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      simp_wf
    | apply Prod.Lex.left
      simp [Call.moduleTarget, target.isLt]

/-- Final caller-visible source environment for constrain execution.

Constraint calls do not expose callee locals, so they are frame-preserving;
Felt operations are the only source statements that update this state.
-/
def evalSourceConstrainEnv {n numMembers : Nat} (i : Fin n)
    (stmts : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) : LocalVar → F :=
  match stmts with
  | [] => env
  | .op d p :: rest =>
    match d, d.isLt with
    | ⟨0, _⟩, _ => evalSourceConstrainEnv i rest env
    | ⟨1, _⟩, _ => evalSourceConstrainEnv i rest (Felt.applyOp p env)
    | ⟨2, _⟩, _ => evalSourceConstrainEnv i rest env

/-! ## Concrete source equation lemmas -/

@[simp] theorem evalComputeBody_felt_cons {n numMembers : Nat}
    (m : Module SourceSet n F) (i : Fin n)
    (op : Felt.Op ⟨n, i.val, numMembers⟩ F)
    (rest : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) :
    evalComputeBody m i (.op feltSourceIx op :: rest) env =
      evalComputeBody m i rest (Felt.applyOp op env) := by
  rw [evalComputeBody.eq_def]
  rfl

theorem evalComputeBody_call_cons {n numMembers : Nat}
    (m : Module SourceSet n F) (i : Fin n)
    (dest : Option LocalVar) (target : Fin i.val) (sel : Nat)
    (args : List LocalVar)
    (rest : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) (hsel : Call.selectorSupported sel = true) :
    evalComputeBody m i (.op callSourceIx (.call dest target sel args) :: rest) env =
      let callee := Call.targetStructAt m i target
      let result :=
        (evalComputeBody m (Call.moduleTarget target i.isLt) callee.compute.body
          (Call.bindArgs env args 0)).map
          (fun calleeEnv => readReturn callee.compute.returnVar calleeEnv)
      (Call.computeStep dest result env).bind (evalComputeBody m i rest) := by
  rw [evalComputeBody.eq_def]
  change (if Call.selectorSupported sel then
    (Call.computeStep dest
      ((evalComputeBody m (Call.moduleTarget target i.isLt)
        (Call.targetStructAt m i target).compute.body
        (Call.bindArgs env args 0)).map
        (fun calleeEnv => readReturn
          (Call.targetStructAt m i target).compute.returnVar calleeEnv)) env).bind
      (evalComputeBody m i rest)
    else none) = _
  rw [if_pos hsel]

@[simp] theorem evalComputeBody_constr_cons {n numMembers : Nat}
    (m : Module SourceSet n F) (i : Fin n)
    (op : ConstrainEq.Op ⟨n, i.val, numMembers⟩ F)
    (rest : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) :
    evalComputeBody m i (.op constrSourceIx op :: rest) env =
      evalComputeBody m i rest env := by
  rw [evalComputeBody.eq_def]
  rfl

@[simp] theorem evalConstrainBody_felt_cons {n numMembers : Nat}
    (m : Module SourceSet n F) (i : Fin n)
    (op : Felt.Op ⟨n, i.val, numMembers⟩ F)
    (rest : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) :
    evalConstrainBody m i (.op feltSourceIx op :: rest) env ↔
      evalConstrainBody m i rest (Felt.applyOp op env) := by
  rw [evalConstrainBody.eq_def]
  rfl

theorem evalConstrainBody_call_cons {n numMembers : Nat}
    (m : Module SourceSet n F) (i : Fin n)
    (target : Fin i.val) (sel : Nat) (args : List LocalVar)
    (rest : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) (hsel : Call.selectorSupported sel = true) :
    evalConstrainBody m i (.op callSourceIx (.call none target sel args) :: rest) env ↔
      let callee := Call.targetStructAt m i target
      evalConstrainBody m (Call.moduleTarget target i.isLt) callee.constrain.body
          (Call.bindArgs env args 0) ∧
        evalConstrainBody m i rest env := by
  rw [evalConstrainBody.eq_def]
  change (if Call.selectorSupported sel then
    evalConstrainBody m (Call.moduleTarget target i.isLt)
        (Call.targetStructAt m i target).constrain.body
        (Call.bindArgs env args 0) ∧
      evalConstrainBody m i rest env
    else False) ↔ _
  rw [if_pos hsel]

@[simp] theorem evalConstrainBody_constr_cons {n numMembers : Nat}
    (m : Module SourceSet n F) (i : Fin n)
    (a b : LocalVar)
    (rest : List (Stmt SourceSet ⟨n, i.val, numMembers⟩ F))
    (env : LocalVar → F) :
    evalConstrainBody m i (.op constrSourceIx (.eq a b) :: rest) env ↔
      env a = env b ∧ evalConstrainBody m i rest env := by
  rw [evalConstrainBody.eq_def]
  rfl

set_option linter.flexible false in
/-- Successful compute erasure certifies that source compute execution is total. -/
theorem eraseBodyInto_compute_source_total {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (herase : eraseBodyInto m caller current .compute rename next stmts = some result)
    (env : LocalVar → F) :
    ∃ out, evalComputeBody m current stmts env = some out := by
  let motive := fun (currentMembers : Nat) (current : Fin n) (kind : BodyKind)
      (rename : LocalVar → LocalVar) (next : LocalVar)
      (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) =>
    match kind with
    | .compute => ∀ (result :
        List (Stmt TargetSet ⟨n, caller.val, callerMembers⟩ F) × LocalVar),
        eraseBodyInto m caller current .compute rename next stmts = some result →
        ∀ env, ∃ out, evalComputeBody m current stmts env = some out
    | .constrain => True
  revert result env
  change motive currentMembers current .compute rename next stmts
  apply eraseBodyInto.induct (callerMembers := callerMembers) (m := m)
    (caller := caller) (motive := motive) (currentMembers := currentMembers)
    (current := current) (kind := .compute)
  · intro _ current kind _ _
    cases kind <;> simp [motive, eraseBodyInto, evalComputeBody]
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturn hcalleeNone _ result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturn, hcalleeNone] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturn calleeBody afterCallee hcallee htailNone _ _ result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturn, hcallee, htailNone] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturn calleeBody afterCallee hcallee tail afterTail htail ihCallee ihTail
      result _ env
    rcases ihCallee (calleeBody, afterCallee) hcallee
        (Call.bindArgs env args 0) with ⟨calleeEnv, hcalleeEval⟩
    let returnEnv := Call.bindReturn dest
      (readReturn (Call.targetStructAt m current target).compute.returnVar calleeEnv) env
    rcases ihTail (tail, afterTail) htail returnEnv with ⟨out, htailEval⟩
    refine ⟨out, ?_⟩
    rw [evalComputeBody.eq_def]
    change (if Call.selectorSupported sel then
      (Call.computeStep dest
        ((evalComputeBody m (Call.moduleTarget target current.isLt)
          (Call.targetStructAt m current target).compute.body
          (Call.bindArgs env args 0)).map
          (fun calleeEnv => readReturn
            (Call.targetStructAt m current target).compute.returnVar calleeEnv)) env).bind
        (evalComputeBody m current rest)
      else none) = some out
    rw [if_pos hsel]
    rw [hcalleeEval]
    simpa [Call.computeStep, returnEnv] using htailEval
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturnFalse result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturnFalse] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargsFalse
      result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargsFalse] at herase
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · simp only [motive]
    intros _ current kind rename next rest isLt _ dest target sel args hselFalse
    cases kind
    · intro result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [hselFalse] at herase
    · trivial
  · simp only [motive]
    intros _ current kind rename next rest isLt _ htailNone op ih
    cases kind
    · intro result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [htailNone] at herase
    · trivial
  · simp only [motive]
    intros currentMembers' current kind rename next rest isLt _ tail afterTail htail op ih
    cases kind
    · intro result _ env
      rcases ih (tail, afterTail) htail (Felt.applyOp op env) with ⟨out, hout⟩
      refine ⟨out, ?_⟩
      rw [evalComputeBody.eq_def]
      exact hout
    · trivial
  · simp only [motive]
    intros _ current kind rename next rest isLt _ htailNone op ih
    cases kind
    · intro result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [htailNone] at herase
    · trivial
  · simp only [motive]
    intros currentMembers' current kind rename next rest isLt _ tail afterTail htail op ih
    cases kind
    · intro result _ env
      rcases ih (tail, afterTail) htail env with ⟨out, hout⟩
      refine ⟨out, ?_⟩
      rw [evalComputeBody.eq_def]
      exact hout
    · trivial

/-- Successful top-level compute erasure implies total source execution. -/
theorem eraseComputeFunc_source_total {n : Nat} (m : Module SourceSet n F)
    (i : Fin n)
    (result : List (Stmt TargetSet
      ⟨n, i.val, (m.structs i).members.length⟩ F) × LocalVar)
    (herase : eraseComputeFunc m i = some result) (env : LocalVar → F) :
    ∃ out, evalComputeBody m i (m.structs i).compute.body env = some out := by
  exact eraseBodyInto_compute_source_total m i i id
    (funcVarBound (m.structs i).compute) (m.structs i).compute.body result
    (by simpa [eraseComputeFunc] using herase) env

/-- Semantic relation established by successful compute erasure. -/
def ComputeErasureSimulation {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) : Prop :=
  ∀ (defined : LocalVar → Bool), isSSA defined stmts = true →
    BodyRenameInvariant stmts rename next →
    (∀ v, defined v = true → rename v < next) →
    ∀ (result : List (Stmt TargetSet
        ⟨n, caller.val, callerMembers⟩ F) × LocalVar),
      eraseBodyInto m caller current .compute rename next stmts = some result →
      ∀ source target, EnvAgreesOn defined rename source target →
        ∃ sourceOut targetOut,
          evalComputeBody m current stmts source = some sourceOut ∧
          evalTargetComputeBody result.1 target = some targetOut ∧
          EnvAgreesOn (definedLocalsAfter defined stmts) rename sourceOut targetOut

set_option linter.flexible false in
/-- Recursive compute erasure preserves all SSA-defined source values. -/
theorem eraseBodyInto_compute_simulation {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) :
    ComputeErasureSimulation (callerMembers := callerMembers)
      m caller current rename next stmts := by
  let motive := fun (currentMembers : Nat) (current : Fin n) (kind : BodyKind)
      (rename : LocalVar → LocalVar) (next : LocalVar)
      (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) =>
    match kind with
    | .compute => ComputeErasureSimulation (callerMembers := callerMembers)
        m caller current rename next stmts
    | .constrain => True
  change motive currentMembers current .compute rename next stmts
  apply eraseBodyInto.induct (callerMembers := callerMembers) (m := m)
    (caller := caller) (motive := motive) (currentMembers := currentMembers)
    (current := current) (kind := .compute)
  · intro _ current kind rename next
    cases kind
    · intro defined _ _ _ result herase source target hagrees
      simp [eraseBodyInto] at herase
      subst result
      exact ⟨source, target, by rw [evalComputeBody.eq_def], rfl,
        by simpa [definedLocalsAfter] using hagrees⟩
    · trivial
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturn hcalleeNone _ defined hssa hren hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturn, hcalleeNone] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturn calleeBody afterCallee hcallee htailNone _ _ defined hssa hren
      hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturn, hcallee, htailNone] at herase
  · simp only [motive]
    intros currentMembers' current rename next rest isLt _ dest target sel args hsel hargs
      hreturn calleeBody afterCallee hcallee tail afterTail htail ihCallee ihTail
      defined hssa hren hbelow result herase source targetEnv hagrees
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturn, hcallee, htail] at herase
    subst result
    let fn := (Call.targetStructAt m current target).compute
    let calleeRename := inlineVar rename args fn.numParams next hargs
    have hparts := isSSA_cons_parts defined
      (.op ⟨0, isLt⟩ (.call dest target sel args)) rest hssa
    have hargsDefined : args.all defined = true := by
      simpa [Stmt.reads, Call.reads] using hparts.1
    have hparamsBelow : ∀ k (hk : k < fn.numParams),
        rename (args.get ⟨k, by simpa [hargs] using hk⟩) < next := by
      intro k hk
      apply hbelow
      exact (List.all_eq_true.mp hargsDefined) _
        (List.get_mem args ⟨k, by simpa [hargs] using hk⟩)
    have hcalleeRen : BodyRenameInvariant fn.body calleeRename
        (next + funcVarBound fn) :=
      (renameInvariant_inlineVar fn rename args next hargs hparamsBelow).body
    have hcalleeBelow : ∀ v, decide (v < fn.numParams) = true →
        calleeRename v < next + funcVarBound fn := by
      intro v hv
      have hvlt : v < fn.numParams := by simpa using hv
      exact (renameInvariant_inlineVar fn rename args next hargs hparamsBelow).1 v
        (Nat.lt_of_lt_of_le hvlt (numParams_le_funcVarBound fn))
    have hcalleeInitial : EnvAgreesOn (fun v => decide (v < fn.numParams))
        calleeRename (Call.bindArgs source args 0) targetEnv :=
      envAgreesOn_bindArgs_inlineVar_of_all rename args fn.numParams next hargs
        defined source targetEnv hargsDefined hagrees
    rcases ihCallee (fun v => decide (v < fn.numParams)) fn.wf_ssa
        hcalleeRen hcalleeBelow (calleeBody, afterCallee) hcallee
        (Call.bindArgs source args 0) targetEnv hcalleeInitial with
      ⟨calleeSource, calleeTarget, hsourceCallee, htargetCallee, hagreeCallee⟩
    have hreservedAfter : next + funcVarBound fn ≤ afterCallee :=
      eraseBodyInto_next_mono m caller (Call.moduleTarget target current.isLt)
        .compute calleeRename (next + funcVarBound fn) fn.body
        (calleeBody, afterCallee) hcallee
    have hnextAfter : next ≤ afterCallee :=
      Nat.le_trans (Nat.le_add_right next _) hreservedAfter
    have hcallerAfter : EnvAgreesOn defined rename source calleeTarget := by
      intro v hv
      have hframe := eraseFuncBodyInto_inlineVar_target_frame
        m caller (Call.moduleTarget target current.isLt) .compute fn rename args next
        hargs (calleeBody, afterCallee) hcallee targetEnv (hbelow v hv)
      rw [htargetCallee] at hframe
      exact (Option.some.inj hframe).trans (hagrees v hv)
    have hstmtDest : (Stmt.op ⟨0, isLt⟩ (.call dest target sel args) :
        Stmt SourceSet ⟨n, current.val, currentMembers'⟩ F).dest = dest := rfl
    cases dest with
    | none =>
      rw [hstmtDest] at hparts
      have htailRen := hren.tail.mono hnextAfter
      have htailBelow : ∀ v, defined v = true → rename v < afterCallee := by
        intro v hv
        exact Nat.lt_of_lt_of_le (hbelow v hv) hnextAfter
      rcases ihTail defined hparts.2 htailRen htailBelow (tail, afterTail)
          (by simpa [fn, emitReturnCopy] using htail) source calleeTarget
          hcallerAfter with
        ⟨sourceOut, targetOut, hsourceTail, htargetTail, houtAgree⟩
      refine ⟨sourceOut, targetOut, ?_, ?_, ?_⟩
      · rw [evalComputeBody.eq_def]
        change (if Call.selectorSupported sel then
          (Call.computeStep none
            ((evalComputeBody m (Call.moduleTarget target current.isLt)
              (Call.targetStructAt m current target).compute.body
              (Call.bindArgs source args 0)).map
              (fun calleeEnv => readReturn
                (Call.targetStructAt m current target).compute.returnVar calleeEnv))
              source).bind (evalComputeBody m current rest)
          else none) = some sourceOut
        rw [if_pos hsel, hsourceCallee]
        simpa [Call.computeStep, fn] using hsourceTail
      · rw [evalTargetComputeBody_append, htargetCallee]
        simpa [fn, emitReturnCopy] using htargetTail
      · rw [definedLocalsAfter_cons, hstmtDest]
        exact houtAgree
    | some d =>
      rw [hstmtDest] at hparts
      obtain ⟨r, hr, hreturnAgree⟩ :=
        computeReturnSupported_value_agree fn d calleeRename calleeSource
          calleeTarget hreturn hagreeCallee
      have hdestBelowNext : rename d < next := by
        apply hren.1 (.op ⟨0, isLt⟩ (.call (some d) target sel args)) (by simp) d
        rw [Stmt.vars, hstmtDest]
        simp
      have hreturnFresh : calleeRename r ≠ afterCallee :=
        inlineVar_return_ne_of_reserved_le fn rename args next afterCallee r hargs
          hparamsBelow hr hreservedAfter
      obtain ⟨copyTarget, hcopyEval, hcopyAgree⟩ :=
        evalTargetComputeBody_emitReturnCopy_agreesOn
          (γ := ⟨n, caller.val, callerMembers⟩) defined d r calleeRename rename
          afterCallee source calleeTarget (calleeSource r) hcallerAfter
          hreturnAgree
          (fun v hv => Nat.lt_of_lt_of_le (hbelow v hv) hnextAfter)
          (Nat.lt_of_lt_of_le hdestBelowNext hnextAfter)
          (hren.2 (.op ⟨0, isLt⟩ (.call (some d) target sel args)) (by simp)
            d rfl)
          hreturnFresh
      let defined' := fun v => defined v || v == d
      have hcopyNext : next ≤
          (emitReturnCopy (γ := ⟨n, caller.val, callerMembers⟩)
            (F := F) (some d) fn.returnVar calleeRename rename afterCallee).2 :=
        Nat.le_trans hnextAfter (emitReturnCopy_next_mono _ _ _ _ _)
      have htailRen : BodyRenameInvariant rest rename
          (emitReturnCopy (γ := ⟨n, caller.val, callerMembers⟩)
            (F := F) (some d) fn.returnVar calleeRename rename afterCallee).2 :=
        hren.tail.mono hcopyNext
      have htailBelow : ∀ v, defined' v = true → rename v <
          (emitReturnCopy (γ := ⟨n, caller.val, callerMembers⟩)
            (F := F) (some d) fn.returnVar calleeRename rename afterCallee).2 := by
        intro v hv
        simp only [defined', Bool.or_eq_true, beq_iff_eq] at hv
        rcases hv with hv | rfl
        · exact Nat.lt_of_lt_of_le (hbelow v hv) hcopyNext
        · exact Nat.lt_of_lt_of_le hdestBelowNext hcopyNext
      rcases ihTail defined' hparts.2 htailRen htailBelow (tail, afterTail)
          htail (Call.bindReturn (some d) (some (calleeSource r)) source)
          copyTarget (by simpa [defined', fn, hr] using hcopyAgree) with
        ⟨sourceOut, targetOut, hsourceTail, htargetTail, houtAgree⟩
      refine ⟨sourceOut, targetOut, ?_, ?_, ?_⟩
      · rw [evalComputeBody.eq_def]
        change (if Call.selectorSupported sel then
          (Call.computeStep (some d)
            ((evalComputeBody m (Call.moduleTarget target current.isLt)
              (Call.targetStructAt m current target).compute.body
              (Call.bindArgs source args 0)).map
              (fun calleeEnv => readReturn
                (Call.targetStructAt m current target).compute.returnVar calleeEnv))
              source).bind (evalComputeBody m current rest)
          else none) = some sourceOut
        rw [if_pos hsel, hsourceCallee]
        simpa [Call.computeStep, fn, hr] using hsourceTail
      · rw [evalTargetComputeBody_append, htargetCallee]
        simp only [Option.bind_some]
        rw [evalTargetComputeBody_append]
        rw [show (emitReturnCopy (γ := ⟨n, caller.val, callerMembers⟩)
          (F := F) (some d) fn.returnVar calleeRename rename afterCallee).1 =
            (emitReturnCopy (γ := ⟨n, caller.val, callerMembers⟩)
              (F := F) (some d) (some r) calleeRename rename afterCallee).1 by
              simp [hr]]
        rw [hcopyEval]
        exact htargetTail
      · rw [definedLocalsAfter_cons, hstmtDest]
        exact houtAgree
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargs
      hreturnFalse defined hssa hren hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hreturnFalse] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ dest target sel args hsel hargsFalse
      defined hssa hren hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargsFalse] at herase
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · simp only [motive]
    intros _ current kind rename next rest isLt _ dest target sel args hselFalse
    cases kind
    · intro defined hssa hren hbelow result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [hselFalse] at herase
    · trivial
  · simp only [motive]
    intros _ current kind rename next rest isLt _ htailNone op ih
    cases kind
    · intro defined hssa hren hbelow result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [htailNone] at herase
    · trivial
  · simp only [motive]
    intros currentMembers' current kind rename next rest isLt _ tail afterTail htail op ih
    cases kind
    · intro defined hssa hren hbelow result herase source targetEnv hagrees
      rw [eraseBodyInto.eq_def] at herase
      simp [htail] at herase
      subst result
      have hparts := isSSA_cons_parts defined (.op ⟨1, isLt⟩ op) rest hssa
      have hstmtDest : (Stmt.op ⟨1, isLt⟩ op :
          Stmt SourceSet ⟨n, current.val, currentMembers'⟩ F).dest =
          some (Felt.destVar op) := Felt.dest_eq op
      rw [hstmtDest] at hparts
      have htailSSA : isSSA (fun v => defined v || v == Felt.destVar op) rest =
          true := by
        exact hparts.2
      have hstepAgree : EnvAgreesOn
          (fun v => defined v || v == Felt.destVar op) rename
          (Felt.applyOp op source)
          (Felt.applyOp
            (lowerFeltOp (γ' := ⟨n, caller.val, callerMembers⟩) rename op)
            targetEnv) := by
        apply applyOp_lowerFeltOp_agreesOn
          (γ' := ⟨n, caller.val, callerMembers⟩)
          defined rename op source targetEnv
        · exact hparts.1
        · exact hagrees
        · apply hren.2 (.op ⟨1, isLt⟩ op) (by simp) (Felt.destVar op)
          exact Felt.dest_eq op
      have hdestBelow : rename (Felt.destVar op) < next := by
        apply hren.1 (.op ⟨1, isLt⟩ op) (by simp) (Felt.destVar op)
        rw [Stmt.vars, hstmtDest]
        simp
      have hbelow' : ∀ v, (defined v || v == Felt.destVar op) = true →
          rename v < next := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        rcases hv with hv | rfl
        · exact hbelow v hv
        · exact hdestBelow
      rcases ih (fun v => defined v || v == Felt.destVar op) htailSSA
          hren.tail hbelow' (tail, afterTail) htail
          (Felt.applyOp op source)
          (Felt.applyOp
            (lowerFeltOp (γ' := ⟨n, caller.val, callerMembers⟩) rename op)
            targetEnv) hstepAgree with
        ⟨sourceOut, targetOut, hsource, htarget, houtAgree⟩
      refine ⟨sourceOut, targetOut, ?_, ?_, ?_⟩
      · rw [evalComputeBody.eq_def]
        exact hsource
      · rw [evalTargetComputeBody.eq_def]
        exact htarget
      · rw [definedLocalsAfter_cons, hstmtDest]
        exact houtAgree
    · trivial
  · simp only [motive]
    intros _ current kind rename next rest isLt _ htailNone op ih
    cases kind
    · intro defined hssa hren hbelow result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [htailNone] at herase
    · trivial
  · simp only [motive]
    intros _ current kind rename next rest isLt _ tail afterTail htail op ih
    cases kind
    · intro defined hssa hren hbelow result herase source targetEnv hagrees
      rw [eraseBodyInto.eq_def] at herase
      simp [htail] at herase
      subst result
      have hparts := isSSA_cons_parts defined (.op ⟨2, isLt⟩ op) rest hssa
      rcases ih defined hparts.2 hren.tail hbelow (tail, afterTail) htail
          source targetEnv hagrees with
        ⟨sourceOut, targetOut, hsource, htarget, houtAgree⟩
      refine ⟨sourceOut, targetOut, ?_, ?_, ?_⟩
      · rw [evalComputeBody.eq_def]
        exact hsource
      · rw [evalTargetComputeBody.eq_def]
        exact htarget
      · simpa [definedLocalsAfter] using houtAgree
    · trivial

/-- Top-level compute-function erasure preserves its complete defined result. -/
theorem eraseComputeFunc_simulation {n : Nat} (m : Module SourceSet n F)
    (i : Fin n)
    (result : List (Stmt TargetSet
      ⟨n, i.val, (m.structs i).members.length⟩ F) × LocalVar)
    (herase : eraseComputeFunc m i = some result)
    (source target : LocalVar → F)
    (hagrees : EnvAgreesOn
      (fun v => decide (v < (m.structs i).compute.numParams)) id source target) :
    ∃ sourceOut targetOut,
      evalComputeBody m i (m.structs i).compute.body source = some sourceOut ∧
      evalTargetComputeBody result.1 target = some targetOut ∧
      EnvAgreesOn
        (definedLocalsAfter
          (fun v => decide (v < (m.structs i).compute.numParams))
          (m.structs i).compute.body)
        id sourceOut targetOut := by
  let fn := (m.structs i).compute
  apply eraseBodyInto_compute_simulation m i i id (funcVarBound fn) fn.body
    (fun v => decide (v < fn.numParams)) fn.wf_ssa
    (renameInvariant_id fn).body
  · intro v hv
    have hvlt : v < fn.numParams := by simpa using hv
    exact Nat.lt_of_lt_of_le hvlt (numParams_le_funcVarBound fn)
  · simpa [eraseComputeFunc, fn] using herase
  · simpa [fn] using hagrees

/-- Semantic relation established by successful constrain erasure. -/
def ConstrainErasureSimulation {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) : Prop :=
  ∀ (defined : LocalVar → Bool), isSSA defined stmts = true →
    BodyRenameInvariant stmts rename next →
    (∀ v, defined v = true → rename v < next) →
    ∀ (result : List (Stmt TargetSet
        ⟨n, caller.val, callerMembers⟩ F) × LocalVar),
      eraseBodyInto m caller current .constrain rename next stmts = some result →
      ∀ source target, EnvAgreesOn defined rename source target →
        (evalTargetConstrainBody result.1 target ↔
          evalConstrainBody m current stmts source) ∧
        EnvAgreesOn (definedLocalsAfter defined stmts) rename
          (evalSourceConstrainEnv current stmts source)
          (evalTargetConstrainEnv result.1 target)

set_option linter.flexible false in
/-- Recursive constrain erasure preserves truth and final defined values. -/
theorem eraseBodyInto_constrain_simulation {n callerMembers currentMembers : Nat}
    (m : Module SourceSet n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) :
    ConstrainErasureSimulation (callerMembers := callerMembers)
      m caller current rename next stmts := by
  let motive := fun (currentMembers : Nat) (current : Fin n) (kind : BodyKind)
      (rename : LocalVar → LocalVar) (next : LocalVar)
      (stmts : List (Stmt SourceSet ⟨n, current.val, currentMembers⟩ F)) =>
    match kind with
    | .compute => True
    | .constrain => ConstrainErasureSimulation (callerMembers := callerMembers)
        m caller current rename next stmts
  change motive currentMembers current .constrain rename next stmts
  apply eraseBodyInto.induct (callerMembers := callerMembers) (m := m)
    (caller := caller) (motive := motive) (currentMembers := currentMembers)
    (current := current) (kind := .constrain)
  · intro _ current kind rename next
    cases kind
    · trivial
    · intro defined _ _ _ result herase source target hagrees
      simp [eraseBodyInto] at herase
      subst result
      constructor
      · rw [evalTargetConstrainBody.eq_def, evalConstrainBody.eq_def]
      · simpa [definedLocalsAfter, evalSourceConstrainEnv,
          evalTargetConstrainEnv] using hagrees
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · (simp only [motive]; aesop)
  · simp only [motive]
    intros _ current rename next rest isLt _ target sel args hsel hargs
      hcalleeNone _ defined hssa hren hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hcalleeNone] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ target sel args hsel hargs
      calleeBody afterCallee hcallee htailNone _ _ defined hssa hren hbelow
      result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hcallee, htailNone] at herase
  · simp only [motive]
    intros currentMembers' current rename next rest isLt _ target sel args hsel hargs
      calleeBody afterCallee hcallee tail afterTail htail ihCallee ihTail
      defined hssa hren hbelow result herase source targetEnv hagrees
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargs, hcallee, htail] at herase
    subst result
    let fn := (Call.targetStructAt m current target).constrain
    let calleeRename := inlineVar rename args fn.numParams next hargs
    have hparts := isSSA_cons_parts defined
      (.op ⟨0, isLt⟩ (.call none target sel args)) rest hssa
    have hargsDefined : args.all defined = true := by
      simpa [Stmt.reads, Call.reads] using hparts.1
    have hparamsBelow : ∀ k (hk : k < fn.numParams),
        rename (args.get ⟨k, by simpa [hargs] using hk⟩) < next := by
      intro k hk
      apply hbelow
      exact (List.all_eq_true.mp hargsDefined) _
        (List.get_mem args ⟨k, by simpa [hargs] using hk⟩)
    have hcalleeRen : BodyRenameInvariant fn.body calleeRename
        (next + funcVarBound fn) :=
      (renameInvariant_inlineVar fn rename args next hargs hparamsBelow).body
    have hcalleeBelow : ∀ v, decide (v < fn.numParams) = true →
        calleeRename v < next + funcVarBound fn := by
      intro v hv
      have hvlt : v < fn.numParams := by simpa using hv
      exact (renameInvariant_inlineVar fn rename args next hargs hparamsBelow).1 v
        (Nat.lt_of_lt_of_le hvlt (numParams_le_funcVarBound fn))
    have hcalleeInitial : EnvAgreesOn (fun v => decide (v < fn.numParams))
        calleeRename (Call.bindArgs source args 0) targetEnv :=
      envAgreesOn_bindArgs_inlineVar_of_all rename args fn.numParams next hargs
        defined source targetEnv hargsDefined hagrees
    rcases ihCallee (fun v => decide (v < fn.numParams)) fn.wf_ssa
        hcalleeRen hcalleeBelow (calleeBody, afterCallee) hcallee
        (Call.bindArgs source args 0) targetEnv hcalleeInitial with
      ⟨htruthCallee, _hagreeCallee⟩
    have hreservedAfter : next + funcVarBound fn ≤ afterCallee :=
      eraseBodyInto_next_mono m caller (Call.moduleTarget target current.isLt)
        .constrain calleeRename (next + funcVarBound fn) fn.body
        (calleeBody, afterCallee) hcallee
    have hnextAfter : next ≤ afterCallee :=
      Nat.le_trans (Nat.le_add_right next _) hreservedAfter
    have hcallerAfter : EnvAgreesOn defined rename source
        (evalTargetConstrainEnv calleeBody targetEnv) := by
      intro v hv
      have hframe := eraseFuncBodyInto_inlineVar_target_frame
        m caller (Call.moduleTarget target current.isLt) .constrain fn rename args next
        hargs (calleeBody, afterCallee) hcallee targetEnv (hbelow v hv)
      rw [evalTargetComputeBody_eq_constrainEnv calleeBody targetEnv] at hframe
      exact (Option.some.inj hframe).trans (hagrees v hv)
    have hstmtDest : (Stmt.op ⟨0, isLt⟩ (.call none target sel args) :
        Stmt SourceSet ⟨n, current.val, currentMembers'⟩ F).dest = none := rfl
    rw [hstmtDest] at hparts
    have htailRen := hren.tail.mono hnextAfter
    have htailBelow : ∀ v, defined v = true → rename v < afterCallee := by
      intro v hv
      exact Nat.lt_of_lt_of_le (hbelow v hv) hnextAfter
    rcases ihTail defined hparts.2 htailRen htailBelow (tail, afterTail) htail
        source (evalTargetConstrainEnv calleeBody targetEnv) hcallerAfter with
      ⟨htruthTail, hagreeTail⟩
    constructor
    · rw [evalTargetConstrainBody_append, evalConstrainBody.eq_def]
      simp only [hsel, if_true]
      exact and_congr htruthCallee htruthTail
    · rw [definedLocalsAfter_cons, hstmtDest, evalSourceConstrainEnv,
        evalTargetConstrainEnv_append]
      exact hagreeTail
  · simp only [motive]
    intros _ current rename next rest isLt _ target sel args hsel hargsFalse
      defined hssa hren hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel, hargsFalse] at herase
  · simp only [motive]
    intros _ current rename next rest isLt _ target sel args hsel r
      defined hssa hren hbelow result herase
    rw [eraseBodyInto.eq_def] at herase
    simp [hsel] at herase
  · simp only [motive]
    intros _ current kind rename next rest isLt _ dest target sel args hselFalse
    cases kind
    · trivial
    · intro defined hssa hren hbelow result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [hselFalse] at herase
  · simp only [motive]
    intros _ current kind rename next rest isLt _ htailNone op ih
    cases kind
    · trivial
    · intro defined hssa hren hbelow result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [htailNone] at herase
  · simp only [motive]
    intros currentMembers' current kind rename next rest isLt _ tail afterTail htail op ih
    cases kind
    · trivial
    · intro defined hssa hren hbelow result herase source targetEnv hagrees
      rw [eraseBodyInto.eq_def] at herase
      simp [htail] at herase
      subst result
      have hparts := isSSA_cons_parts defined (.op ⟨1, isLt⟩ op) rest hssa
      have hstmtDest : (Stmt.op ⟨1, isLt⟩ op :
          Stmt SourceSet ⟨n, current.val, currentMembers'⟩ F).dest =
          some (Felt.destVar op) := Felt.dest_eq op
      rw [hstmtDest] at hparts
      have hstepAgree : EnvAgreesOn
          (fun v => defined v || v == Felt.destVar op) rename
          (Felt.applyOp op source)
          (Felt.applyOp
            (lowerFeltOp (γ' := ⟨n, caller.val, callerMembers⟩) rename op)
            targetEnv) := by
        apply applyOp_lowerFeltOp_agreesOn
          (γ' := ⟨n, caller.val, callerMembers⟩)
          defined rename op source targetEnv
        · exact hparts.1
        · exact hagrees
        · apply hren.2 (.op ⟨1, isLt⟩ op) (by simp) (Felt.destVar op)
          exact hstmtDest
      have hdestBelow : rename (Felt.destVar op) < next := by
        apply hren.1 (.op ⟨1, isLt⟩ op) (by simp) (Felt.destVar op)
        rw [Stmt.vars, hstmtDest]
        simp
      have hbelow' : ∀ v, (defined v || v == Felt.destVar op) = true →
          rename v < next := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        rcases hv with hv | rfl
        · exact hbelow v hv
        · exact hdestBelow
      rcases ih (fun v => defined v || v == Felt.destVar op) hparts.2
          hren.tail hbelow' (tail, afterTail) htail
          (Felt.applyOp op source)
          (Felt.applyOp
            (lowerFeltOp (γ' := ⟨n, caller.val, callerMembers⟩) rename op)
            targetEnv) hstepAgree with ⟨htruth, houtAgree⟩
      constructor
      · rw [evalTargetConstrainBody.eq_def, evalConstrainBody.eq_def]
        exact htruth
      · rw [definedLocalsAfter_cons, hstmtDest,
          evalSourceConstrainEnv, evalTargetConstrainEnv.eq_def]
        exact houtAgree
  · simp only [motive]
    intros _ current kind rename next rest isLt _ htailNone op ih
    cases kind
    · trivial
    · intro defined hssa hren hbelow result herase
      rw [eraseBodyInto.eq_def] at herase
      simp [htailNone] at herase
  · simp only [motive]
    intros currentMembers' current kind rename next rest isLt _ tail afterTail htail op ih
    cases kind
    · trivial
    · intro defined hssa hren hbelow result herase source targetEnv hagrees
      rw [eraseBodyInto.eq_def] at herase
      simp [htail] at herase
      subst result
      cases op with
      | eq a b =>
        have hparts := isSSA_cons_parts defined
          (.op ⟨2, isLt⟩ (.eq a b)) rest hssa
        have hreadA : targetEnv (rename a) = source a := by
          apply hagrees a
          apply (List.all_eq_true.mp hparts.1) a
          change a ∈ [a, b]
          simp
        have hreadB : targetEnv (rename b) = source b := by
          apply hagrees b
          apply (List.all_eq_true.mp hparts.1) b
          change b ∈ [a, b]
          simp
        rcases ih defined hparts.2 hren.tail hbelow (tail, afterTail) htail
            source targetEnv hagrees with ⟨htruth, houtAgree⟩
        constructor
        · rw [evalTargetConstrainBody.eq_def, evalConstrainBody.eq_def]
          constructor
          · rintro ⟨heq, htailTruth⟩
            exact ⟨by simpa [hreadA, hreadB] using heq, htruth.mp htailTruth⟩
          · rintro ⟨heq, htailTruth⟩
            exact ⟨by simpa [hreadA, hreadB] using heq, htruth.mpr htailTruth⟩
        · simpa [definedLocalsAfter, evalSourceConstrainEnv,
            evalTargetConstrainEnv] using houtAgree

/-- Top-level constrain-function erasure preserves truth and final defined values. -/
theorem eraseConstrainFunc_simulation {n : Nat} (m : Module SourceSet n F)
    (i : Fin n)
    (result : List (Stmt TargetSet
      ⟨n, i.val, (m.structs i).members.length⟩ F) × LocalVar)
    (herase : eraseConstrainFunc m i = some result)
    (source target : LocalVar → F)
    (hagrees : EnvAgreesOn
      (fun v => decide (v < (m.structs i).constrain.numParams)) id source target) :
    (evalTargetConstrainBody result.1 target ↔
      evalConstrainBody m i (m.structs i).constrain.body source) ∧
    EnvAgreesOn
      (definedLocalsAfter
        (fun v => decide (v < (m.structs i).constrain.numParams))
        (m.structs i).constrain.body)
      id
      (evalSourceConstrainEnv i (m.structs i).constrain.body source)
      (evalTargetConstrainEnv result.1 target) := by
  let fn := (m.structs i).constrain
  apply eraseBodyInto_constrain_simulation m i i id (funcVarBound fn) fn.body
    (fun v => decide (v < fn.numParams)) fn.wf_ssa
    (renameInvariant_id fn).body
  · intro v hv
    have hvlt : v < fn.numParams := by simpa using hv
    exact Nat.lt_of_lt_of_le hvlt (numParams_le_funcVarBound fn)
  · simpa [eraseConstrainFunc, fn] using herase
  · simpa [fn] using hagrees

/-- A successfully certified module erasure preserves and reflects the
call-aware constraint semantics at every entry point. -/
theorem eraseModule_constrain_iff {n : Nat} (m : Module SourceSet n F)
    (out : Module TargetSet n F) (herase : eraseModule m = some out)
    (entry : Fin n) (env : LocalVar → F) :
    evalFuncConstrain (targetHandlers F) out (out.structs entry).constrain env ↔
      evalConstrainBody m entry (m.structs entry).constrain.body env := by
  obtain ⟨result, compute, constrain, hfunc, hstruct, hbody⟩ :=
    eraseModule_constrain_body m out herase entry
  have hagrees : EnvAgreesOn
      (fun v => decide (v < (m.structs entry).constrain.numParams))
      id env env := by
    intro v _
    rfl
  have hsim := (eraseConstrainFunc_simulation m entry result hfunc env env hagrees).1
  rw [hstruct]
  change Dialect.evalConstrainBody (targetHandlers F) (semCtx out)
    constrain.body env ↔ _
  rw [hbody]
  exact (evalTargetConstrainBody_iff_generic (semCtx out) result.1 env).symm.trans hsim

/-- Composition-facing wrapper for the partial, call-aware front pass.

Unlike `ModuleConstraintPass`, this boundary records successful erasure
explicitly and uses recursive source semantics rather than pretending calls are
module-local dialect handlers. -/
structure CallModuleConstraintPass (Δ' : DialectSet) (F : Type) [Field F] where
  handlers' : HandlerFamily Δ' F
  lowerModule : {n : Nat} → Module SourceSet n F → Option (Module Δ' n F)
  constrain_iff : ∀ {n : Nat} (m : Module SourceSet n F)
    (out : Module Δ' n F), lowerModule m = some out →
    ∀ (entry : Fin n) (env : LocalVar → F),
      evalFuncConstrain handlers' out (out.structs entry).constrain env ↔
        evalConstrainBody m entry (m.structs entry).constrain.body env

/-- Certified Phase-6 call-erasure wrapper. -/
noncomputable def moduleConstraintPass : CallModuleConstraintPass TargetSet F where
  handlers' := targetHandlers F
  lowerModule := eraseModule
  constrain_iff := eraseModule_constrain_iff

/-! ## Structural-pass adapter -/

/-- A constraint observation chooses an entry point and its local environment. -/
abbrev ConstraintState (n : Nat) (F : Type) := Fin n × (LocalVar → F)

def sourceConstraintStage (n : Nat) (F : Type) [Field F] :
    ModuleStage SourceSet n F where
  State := ConstraintState n F
  satisfies state m :=
    evalConstrainBody m state.1 (m.structs state.1).constrain.body state.2

def targetConstraintStage (n : Nat) (F : Type) [Field F] :
    ModuleStage TargetSet n F where
  State := ConstraintState n F
  satisfies state m :=
    evalFuncConstrain (targetHandlers F) m (m.structs state.1).constrain state.2

/-- The existing leaf correctness theorem exposed through the explicit
structural composition API.  Partiality is exactly successful call erasure;
the entry/environment state is unchanged. -/
noncomputable def structuralConstraintPass (n : Nat) (F : Type) [Field F] :
    EraseDialect Call.sig TargetSet
      (sourceConstraintStage n F) (targetConstraintStage n F) where
  lower m := match eraseModule m with
    | some out => .ok out
    | none => .error "call erasure failed"
  stateRel _ _ sourceState targetState := sourceState = targetState
  preservation := by
    intro m out sourceState hlower hsatisfies
    cases herase : eraseModule m with
    | none => rw [herase] at hlower; cases hlower
    | some result =>
      rw [herase] at hlower
      have hout : result = out := Except.ok.inj hlower
      subst out
      exact ⟨sourceState, rfl,
        (eraseModule_constrain_iff m result herase sourceState.1 sourceState.2).mpr
          hsatisfies⟩
  reflection := by
    intro m out targetState hlower hsatisfies
    cases herase : eraseModule m with
    | none => rw [herase] at hlower; cases hlower
    | some result =>
      rw [herase] at hlower
      have hout : result = out := Except.ok.inj hlower
      subst out
      exact ⟨targetState, rfl,
        (eraseModule_constrain_iff m result herase targetState.1 targetState.2).mp
          hsatisfies⟩

namespace CallModuleConstraintPass

set_option linter.flexible false in
/-- Compose call erasure with an ordinary total module-constraint pass. -/
def compose {Δ₁ Δ₂ : DialectSet}
    (p₁ : CallModuleConstraintPass Δ₁ F)
    (p₂ : ModuleConstraintPass Δ₁ Δ₂ F)
    (hmid : p₁.handlers' = p₂.handlers) :
    CallModuleConstraintPass Δ₂ F where
  handlers' := p₂.handlers'
  lowerModule := fun m => (p₁.lowerModule m).map p₂.lowerModule
  constrain_iff := by
    intro n m out hlower entry env
    cases h₁ : p₁.lowerModule m with
    | none => simp [h₁] at hlower
    | some mid =>
      simp [h₁] at hlower
      subst out
      have hp₁ := p₁.constrain_iff m mid h₁ entry env
      rw [hmid] at hp₁
      exact (p₂.constrain_iff mid entry env).trans hp₁

end CallModuleConstraintPass

/-- Evaluate a struct's witness function and expose its optional return value. -/
def evalComputeFunc {n : Nat} (m : Module SourceSet n F) (i : Fin n)
    (args : List F) : Option (Option F) :=
  let fn := (m.structs i).compute
  (evalComputeBody m i fn.body (bindParams args 0)).map
    (fun env => readReturn fn.returnVar env)

/-- Evaluate a struct's constraint function from positional call arguments. -/
def evalConstrainFunc {n : Nat} (m : Module SourceSet n F) (i : Fin n)
    (args : List F) : Prop :=
  let fn := (m.structs i).constrain
  evalConstrainBody m i fn.body (bindParams args 0)

/-- Call-aware satisfaction for one concrete source-set struct. -/
def satisfiesStruct {n : Nat} (m : Module SourceSet n F) (i : Fin n)
    (input : FuncInput F) (default : F) : Prop :=
  ∃ env, evalComputeBody m i (m.structs i).compute.body
      (bindParams input.args default) = some env ∧
    evalConstrainBody m i (m.structs i).constrain.body env

/-- Call-aware satisfaction for a source-set module entry point. -/
def satisfiesModuleAt {n : Nat} (m : Module SourceSet n F) (entry : Fin n)
    (input : FuncInput F) (default : F) : Prop :=
  satisfiesStruct m entry input default

end Dialect.CallSemantics
