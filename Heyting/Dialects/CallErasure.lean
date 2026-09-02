/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.CallPass
import Heyting.Dialects.StructObject
import Heyting.Core.StructuralPass

/-!
# Residual-polymorphic call erasure

This is the module-aware structural implementation of

```text
[Call] ++ residual → residual
```

The recursive inliner knows only the `Call` head.  Transport of a residual
payload between the callee and caller operation contexts, and the small piece
of syntax used to bind a returned value, are supplied explicitly by
`ResidualSyntax`.  They are pass values, not type-class-selected effects.

The older `[Call, Felt, ConstrainEq]` development remains in `CallPass`; its
semantic theorem is the first certified specialization.  This file supplies
the generic syntax path used by the object-aware frontend.
-/

namespace Dialect.CallErasure

open Dialect

/-! ## Static call-state protocol -/

/-- State operations needed by call semantics.  One pass chooses one concrete
`State`; this is deliberately not a heterogeneous effect list or a typeclass.
The laws expose argument binding and the caller-local frame used by semantic
simulation. -/
structure CallProtocol (State F : Type) where
  readLocal : State → LocalVar → F
  initCallee : State → List LocalVar → F → State
  mergeReturn : State → State → Option LocalVar → Option LocalVar → State
  read_init_param : ∀ (caller : State) (args : List LocalVar) (default : F)
    (k : Fin args.length),
    readLocal (initCallee caller args default) k.val = readLocal caller (args.get k)
  read_merge_return : ∀ (caller callee : State) (dest ret : LocalVar),
    readLocal (mergeReturn caller callee (some dest) (some ret)) dest =
      readLocal callee ret
  read_merge_frame : ∀ (caller callee : State)
    (dest ret : Option LocalVar) (v : LocalVar), dest ≠ some v →
    readLocal (mergeReturn caller callee dest ret) v = readLocal caller v

/-- Call protocol for the original field-local semantics. -/
def localProtocol (F : Type) : CallProtocol (LocalVar → F) F where
  readLocal env v := env v
  initCallee caller args default := Call.bindArgs caller args default
  mergeReturn caller callee dest ret :=
    Call.bindReturn dest (ret.map callee) caller
  read_init_param := by intro caller args default k; simp
  read_merge_return := by intro caller callee dest ret; simp
  read_merge_frame := by
    intro caller callee dest ret v h
    exact Call.bindReturn_frame dest (ret.map callee) caller v h

private def bindObjectArgs (caller : StructObject.State F)
    (args : List LocalVar) (default : F) : StructObject.State F where
  values := Call.bindArgs caller.values args default
  objects := fun v =>
    if h : v < args.length then caller.objects (args.get ⟨v, h⟩) else []
  witness := caller.witness
  nextPath := caller.nextPath

private def mergeObjectReturn (caller callee : StructObject.State F)
    (dest ret : Option LocalVar) : StructObject.State F where
  values := Call.bindReturn dest (ret.map callee.values) caller.values
  objects := match dest, ret with
    | some d, some r => StructObject.ObjEnv.update caller.objects d (callee.objects r)
    | _, _ => caller.objects
  witness := callee.witness
  nextPath := callee.nextPath

/-- Object-aware calls bind both field locals and object paths.  Witness and
allocation state flow through the callee, while ordinary caller locals obey
the same return/frame discipline as the leaf protocol. -/
def objectProtocol (F : Type) : CallProtocol (StructObject.State F) F where
  readLocal state v := state.values v
  initCallee := bindObjectArgs
  mergeReturn := mergeObjectReturn
  read_init_param := by intro caller args default k; simp [bindObjectArgs]
  read_merge_return := by intro caller callee dest ret; simp [mergeObjectReturn]
  read_merge_frame := by
    intro caller callee dest ret v h
    simp only [mergeObjectReturn]
    exact Call.bindReturn_frame dest (ret.map callee.values) caller.values v h

@[simp] theorem objectProtocol_init_path (caller : StructObject.State F)
    (args : List LocalVar) (default : F) (k : Fin args.length) :
    ((objectProtocol F).initCallee caller args default).objects k.val =
      caller.objects (args.get k) := by
  simp [objectProtocol, bindObjectArgs, k.isLt]

@[simp] theorem objectProtocol_merge_witness (caller callee : StructObject.State F)
    (dest ret : Option LocalVar) :
    ((objectProtocol F).mergeReturn caller callee dest ret).witness = callee.witness := rfl

@[simp] theorem objectProtocol_merge_nextPath (caller callee : StructObject.State F)
    (dest ret : Option LocalVar) :
    ((objectProtocol F).mergeReturn caller callee dest ret).nextPath = callee.nextPath := rfl

abbrev Source (residual : DialectSet) : DialectSet := Call.sig :: residual

def callIx (residual : DialectSet) : Fin (Source residual).length :=
  ⟨0, by simp [Source]⟩

/-- Explicit syntax support required by call inlining.  `recontextualize`
transports a residual operation from a callee body to the caller body.  It may
reject an operation whose context-indexed payload cannot be represented in the
target context.  `emitReturn` binds a callee return local to a caller
destination and returns the next fresh local. -/
structure ResidualSyntax (residual : DialectSet) (F : Type) where
  recontextualize : ∀ {sourceCtx targetCtx : OpCtx}
    (d : Fin residual.length),
    (residual.get d).Op sourceCtx F →
      Option ((residual.get d).Op targetCtx F)
  emitReturn : ∀ {ctx : OpCtx}, Option LocalVar → Option LocalVar →
    (LocalVar → LocalVar) → (LocalVar → LocalVar) → LocalVar →
    Option (List (Stmt residual ctx F) × LocalVar)

namespace ResidualSyntax

/-- Static transport certificate used by SSA, capability, and semantic frame
proofs.  Combined with `OpSig.mapVars` laws, it says residual lowering changes
only the operation context and local names. -/
structure RenameStable {residual : DialectSet} {F : Type}
    (config : ResidualSyntax residual F) : Prop where
  dest : ∀ {sourceCtx targetCtx : OpCtx} (d : Fin residual.length)
    (op : (residual.get d).Op sourceCtx F)
    (out : (residual.get d).Op targetCtx F),
    config.recontextualize d op = some out →
      (residual.get d).dest out = (residual.get d).dest op
  reads : ∀ {sourceCtx targetCtx : OpCtx} (d : Fin residual.length)
    (op : (residual.get d).Op sourceCtx F)
    (out : (residual.get d).Op targetCtx F),
    config.recontextualize d op = some out →
      (residual.get d).reads out = (residual.get d).reads op
  cap : ∀ {sourceCtx targetCtx : OpCtx} (d : Fin residual.length)
    (op : (residual.get d).Op sourceCtx F)
    (out : (residual.get d).Op targetCtx F),
    config.recontextualize d op = some out →
      (residual.get d).cap out = (residual.get d).cap op

end ResidualSyntax

/-- A residual statement viewed after removing the `Call` head index. -/
def lowerResidualStmt {residual : DialectSet} {F : Type}
    (config : ResidualSyntax residual F)
    {sourceCtx targetCtx : OpCtx} (rename : LocalVar → LocalVar)
    (d : Fin residual.length) (payload : (residual.get d).Op sourceCtx F) :
    Option (Stmt residual targetCtx F) := do
  let transported ← config.recontextualize d payload
  pure (.op d ((residual.get d).mapVars rename transported))

/-- Locals known defined after a generic source body. -/
def definedLocalsAfter {residual : DialectSet} {n i numMembers : Nat} {F : Type}
    (init : LocalVar → Bool) :
    List (Stmt (Source residual) ⟨n, i, numMembers⟩ F) → LocalVar → Bool
  | [] => init
  | stmt :: rest =>
    let next := match stmt.dest with
      | some d => fun v => init v || v == d
      | none => init
    definedLocalsAfter next rest

def computeReturnSupported {residual : DialectSet} {n i numMembers : Nat}
    {F : Type} (fn : FuncDef (Source residual) n i F .witness numMembers)
    (dest : Option LocalVar) : Bool :=
  match dest with
  | none => true
  | some _ =>
    match fn.returnVar with
    | none => false
    | some r => definedLocalsAfter (fun v => decide (v < fn.numParams)) fn.body r

/-- Strict upper bound covering parameters, body variables, and return. -/
def funcVarBound {residual : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability}
    (fn : FuncDef (Source residual) n i F kind numMembers) : LocalVar :=
  max fn.numParams
    (max (maxVarBody fn.body) (Option.getD (fn.returnVar.map (fun v => v + 1)) 0))

abbrev BodyKind := CallPass.BodyKind

/-- Recursively inline a body.  Termination follows the static topological
call index; the tail recursion decreases the statement list. -/
def eraseBodyInto {residual : DialectSet} (config : ResidualSyntax residual F)
    {n callerMembers currentMembers : Nat}
    (m : Module (Source residual) n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt (Source residual) ⟨n, current.val, currentMembers⟩ F)) :
    Option (List (Stmt residual ⟨n, caller.val, callerMembers⟩ F) × LocalVar) :=
  match stmts with
  | [] => some ([], next)
  | .op d payload :: rest =>
    match d with
    | ⟨0, _⟩ =>
      match payload with
      | .call dest target selector args =>
        if Call.selectorSupported selector then
          let targetIndex := Call.moduleTarget target current.isLt
          let callee := Call.targetStructAt m current target
          match kind with
          | .compute =>
            let fn := callee.compute
            if hargs : args.length = fn.numParams then
              if computeReturnSupported fn dest then
                let base := next
                let calleeRename := CallPass.inlineVar rename args fn.numParams base hargs
                let reserved := base + funcVarBound fn
                match eraseBodyInto config m caller targetIndex .compute calleeRename
                    reserved fn.body with
                | none => none
                | some (calleeBody, afterCallee) =>
                  match config.emitReturn dest fn.returnVar calleeRename rename afterCallee with
                  | none => none
                  | some (copy, afterCopy) =>
                    match eraseBodyInto config m caller current kind rename afterCopy rest with
                    | none => none
                    | some (tail, afterTail) =>
                      some (calleeBody ++ copy ++ tail, afterTail)
              else none
            else none
          | .constrain =>
            match dest with
            | some _ => none
            | none =>
              let fn := callee.constrain
              if hargs : args.length = fn.numParams then
                let base := next
                let calleeRename := CallPass.inlineVar rename args fn.numParams base hargs
                let reserved := base + funcVarBound fn
                match eraseBodyInto config m caller targetIndex .constrain calleeRename
                    reserved fn.body with
                | none => none
                | some (calleeBody, afterCallee) =>
                  match eraseBodyInto config m caller current kind rename afterCallee rest with
                  | none => none
                  | some (tail, afterTail) => some (calleeBody ++ tail, afterTail)
              else none
        else none
    | ⟨index + 1, hindex⟩ =>
      let residualIx : Fin residual.length := ⟨index, by simpa [Source] using hindex⟩
      match lowerResidualStmt config rename residualIx payload with
      | none => none
      | some lowered =>
        match eraseBodyInto config m caller current kind rename next rest with
        | none => none
        | some (tail, afterTail) => some (lowered :: tail, afterTail)
termination_by (current.val, stmts.length)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      simp_wf
    | apply Prod.Lex.left
      simp [Call.moduleTarget, target.isLt]

/-! ## Constraint-layout invariants -/

def DestinationsAbove {residual : DialectSet} {ctx : OpCtx} {F : Type}
    (floor : LocalVar) (body : List (Stmt residual ctx F)) : Prop :=
  ∀ stmt ∈ body, ∀ dest, stmt.dest = some dest → floor ≤ dest

theorem destinationsAbove_append {residual : DialectSet} {ctx : OpCtx} {F : Type}
    {floor : LocalVar} {left right : List (Stmt residual ctx F)}
    (hleft : DestinationsAbove floor left)
    (hright : DestinationsAbove floor right) :
    DestinationsAbove floor (left ++ right) := by
  intro stmt hmem dest hdest
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft stmt hmem dest hdest
  · exact hright stmt hmem dest hdest

theorem lowerResidualStmt_dest {residual : DialectSet} {F : Type}
    (config : ResidualSyntax residual F)
    (stable : ResidualSyntax.RenameStable config)
    {sourceCtx targetCtx : OpCtx} (rename : LocalVar → LocalVar)
    (d : Fin residual.length) (payload : (residual.get d).Op sourceCtx F)
    (out : Stmt residual targetCtx F)
    (hlower : lowerResidualStmt config rename d payload = some out) :
    out.dest = ((residual.get d).dest payload).map rename := by
  unfold lowerResidualStmt at hlower
  cases htransport : config.recontextualize d payload with
  | none =>
    rw [htransport] at hlower
    simp at hlower
  | some transported =>
    rw [htransport] at hlower
    have hout := Option.some.inj hlower
    subst out
    change (residual.get d).dest ((residual.get d).mapVars rename transported) = _
    rw [OpSig.dest_mapVars]
    exact congrArg (Option.map rename) (stable.dest d payload transported htransport)

theorem lowerResidualStmt_dest_ge {residual : DialectSet} {F : Type}
    (config : ResidualSyntax residual F)
    (stable : ResidualSyntax.RenameStable config)
    {sourceCtx targetCtx : OpCtx} (rename : LocalVar → LocalVar)
    (d : Fin residual.length) (payload : (residual.get d).Op sourceCtx F)
    (floor : LocalVar) (out : Stmt residual targetCtx F)
    (hsource : ∀ sourceDest, (residual.get d).dest payload = some sourceDest →
      floor ≤ rename sourceDest)
    (hlower : lowerResidualStmt config rename d payload = some out)
    (dest : LocalVar) (hdest : out.dest = some dest) :
    floor ≤ dest := by
  rw [lowerResidualStmt_dest config stable rename d payload out hlower] at hdest
  cases hpayloadDest : (residual.get d).dest payload with
  | none =>
    rw [hpayloadDest] at hdest
    contradiction
  | some sourceDest =>
    simp only [hpayloadDest, Option.map_some, Option.some.injEq] at hdest
    subst dest
    exact hsource sourceDest hpayloadDest

/-
/-- Successful constraint expansion never moves its fresh counter backwards. -/
theorem eraseBodyInto_constrain_next_mono {residual : DialectSet}
    (config : ResidualSyntax residual F) {n callerMembers currentMembers : Nat}
    (m : Module (Source residual) n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt (Source residual)
      ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt residual ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (herase : eraseBodyInto config m caller current .constrain rename next stmts =
      some result) :
    next ≤ result.2 :=
  match stmts with
  | [] => by
      rw [eraseBodyInto.eq_def] at herase
      simpa using congrArg Prod.snd (Option.some.inj herase)
  | .op d payload :: rest => by
      rcases d with ⟨index, hindex⟩
      cases index with
      | zero =>
        cases payload with
        | call dest target selector args =>
          rw [eraseBodyInto.eq_def] at herase
          by_cases hselector : Call.selectorSupported selector
          · simp only [hselector, if_true] at herase
            cases dest with
            | some dest => simp at herase
            | none =>
              let j := Call.moduleTarget target current.isLt
              let fn := (m.structs j).constrain
              by_cases hargs : args.length = fn.numParams
              · simp only [hargs, dif_pos] at herase
                let calleeRename := CallPass.inlineVar rename args fn.numParams next hargs
                let reserved := next + funcVarBound fn
                cases hcallee : eraseBodyInto config m caller j .constrain calleeRename
                    reserved fn.body with
                | none => simp [j, fn, calleeRename, reserved, hcallee] at herase
                | some calleeResult =>
                  simp only [j, fn, calleeRename, reserved, hcallee] at herase
                  cases htail : eraseBodyInto config m caller current .constrain rename
                      calleeResult.2 rest with
                  | none => simp [htail] at herase
                  | some tailResult =>
                    simp only [htail, Option.some.injEq] at herase
                    subst result
                    exact Nat.le_trans (Nat.le_add_right next _)
                      (Nat.le_trans
                        (eraseBodyInto_constrain_next_mono config m caller j calleeRename
                          reserved fn.body calleeResult hcallee)
                        (eraseBodyInto_constrain_next_mono config m caller current rename
                          calleeResult.2 rest tailResult htail))
              · simp [j, fn, hargs] at herase
          · simp [hselector] at herase
      | succ residualIndex =>
        rw [eraseBodyInto.eq_def] at herase
        let residualIx : Fin residual.length := ⟨residualIndex, by
          simpa [Source] using hindex⟩
        cases hlower : lowerResidualStmt config rename residualIx payload with
        | none => simp [residualIx, hlower] at herase
        | some lowered =>
          simp only [residualIx, hlower] at herase
          cases htail : eraseBodyInto config m caller current .constrain rename next rest with
          | none => simp [htail] at herase
          | some tailResult =>
            simp only [htail, Option.some.injEq] at herase
            subst result
            exact eraseBodyInto_constrain_next_mono config m caller current rename next
              rest tailResult htail
termination_by (current.val, stmts.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp

/-- Successful constraint expansion writes only above a protected caller floor. -/
theorem eraseBodyInto_constrain_destinationsAbove {residual : DialectSet}
    (config : ResidualSyntax residual F)
    (stable : ResidualSyntax.RenameStable config)
    {n callerMembers currentMembers : Nat}
    (m : Module (Source residual) n F) (caller current : Fin n)
    (rename : LocalVar → LocalVar) (next floor : LocalVar)
    (stmts : List (Stmt (Source residual)
      ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt residual ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (hnext : floor ≤ next)
    (hframe : ∀ stmt ∈ stmts, ∀ dest, stmt.dest = some dest → floor ≤ rename dest)
    (herase : eraseBodyInto config m caller current .constrain rename next stmts =
      some result) :
    DestinationsAbove floor result.1 :=
  match stmts with
  | [] => by
      rw [eraseBodyInto.eq_def] at herase
      have hresult := Option.some.inj herase
      subst result
      simp [DestinationsAbove]
  | .op d payload :: rest => by
      rcases d with ⟨index, hindex⟩
      cases index with
      | zero =>
        cases payload with
        | call dest target selector args =>
          rw [eraseBodyInto.eq_def] at herase
          by_cases hselector : Call.selectorSupported selector
          · simp only [hselector, if_true] at herase
            cases dest with
            | some dest => simp at herase
            | none =>
              let j := Call.moduleTarget target current.isLt
              let fn := (m.structs j).constrain
              by_cases hargs : args.length = fn.numParams
              · simp only [hargs, dif_pos] at herase
                let calleeRename := CallPass.inlineVar rename args fn.numParams next hargs
                let reserved := next + funcVarBound fn
                cases hcallee : eraseBodyInto config m caller j .constrain calleeRename
                    reserved fn.body with
                | none => simp [j, fn, calleeRename, reserved, hcallee] at herase
                | some calleeResult =>
                  simp only [j, fn, calleeRename, reserved, hcallee] at herase
                  cases htail : eraseBodyInto config m caller current .constrain rename
                      calleeResult.2 rest with
                  | none => simp [htail] at herase
                  | some tailResult =>
                    simp only [htail, Option.some.injEq] at herase
                    subst result
                    apply destinationsAbove_append
                    · apply eraseBodyInto_constrain_destinationsAbove config stable m caller j
                        calleeRename reserved floor fn.body calleeResult
                      · exact Nat.le_trans hnext (Nat.le_add_right next _)
                      · intro stmt hmem dest hdest
                        exact Nat.le_trans hnext
                          (CallPass.inlineVar_stmt_dest_ge_base fn rename args next hargs
                            hmem hdest)
                      · exact hcallee
                    · apply eraseBodyInto_constrain_destinationsAbove config stable m caller
                        current rename calleeResult.2 floor rest tailResult
                      · exact Nat.le_trans (Nat.le_trans hnext (Nat.le_add_right next _))
                          (eraseBodyInto_constrain_next_mono config m caller j calleeRename
                            reserved fn.body calleeResult hcallee)
                      · intro stmt hmem dest hdest
                        exact hframe stmt (by simp [hmem]) dest hdest
                      · exact htail
              · simp [j, fn, hargs] at herase
          · simp [hselector] at herase
      | succ residualIndex =>
        rw [eraseBodyInto.eq_def] at herase
        let residualIx : Fin residual.length := ⟨residualIndex, by
          simpa [Source] using hindex⟩
        cases hlower : lowerResidualStmt config rename residualIx payload with
        | none => simp [residualIx, hlower] at herase
        | some lowered =>
          simp only [residualIx, hlower] at herase
          cases htail : eraseBodyInto config m caller current .constrain rename next rest with
          | none => simp [htail] at herase
          | some tailResult =>
            simp only [htail, Option.some.injEq] at herase
            subst result
            intro stmt hmem dest hdest
            rcases List.mem_cons.mp hmem with rfl | hmem
            · rw [lowerResidualStmt_dest config stable rename residualIx payload lowered
                hlower] at hdest
              cases hpayloadDest : (residual.get residualIx).dest payload with
              | none => simp [hpayloadDest] at hdest
              | some sourceDest =>
                simp only [hpayloadDest, Option.map_some, Option.some.injEq] at hdest
                subst dest
                apply hframe (.op ⟨residualIndex + 1, hindex⟩ payload) (by simp)
                  sourceDest
                exact hpayloadDest
            · apply eraseBodyInto_constrain_destinationsAbove config stable m caller current
                rename next floor rest tailResult hnext
              · intro tailStmt htailMem tailDest htailDest
                exact hframe tailStmt (by simp [htailMem]) tailDest htailDest
              · exact htail
termination_by (current.val, stmts.length)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; exact target.isLt
  | apply Prod.Lex.right; simp
 -/

namespace ResidualSyntax

structure ReturnMonotone {residual : DialectSet} {F : Type}
    (config : ResidualSyntax residual F) : Prop where
  next_le : ∀ {ctx : OpCtx} (dest ret : Option LocalVar)
    (calleeRename callerRename : LocalVar → LocalVar) (next : LocalVar)
    (out : List (Stmt residual ctx F) × LocalVar),
    config.emitReturn dest ret calleeRename callerRename next = some out →
      next ≤ out.2

/-- Return lowering preserves a supplied caller-local destination floor. -/
structure ReturnFrame {residual : DialectSet} {F : Type}
    (config : ResidualSyntax residual F) : Prop where
  destinations : ∀ {ctx : OpCtx} (floor : LocalVar)
    (dest ret : Option LocalVar)
    (calleeRename callerRename : LocalVar → LocalVar) (next : LocalVar)
    (out : List (Stmt residual ctx F) × LocalVar),
    floor ≤ next →
    (∀ d, dest = some d → floor ≤ callerRename d) →
    config.emitReturn dest ret calleeRename callerRename next = some out →
    DestinationsAbove floor out.1

end ResidualSyntax

set_option linter.flexible false in
/-- Successful expansion never moves its fresh counter backwards. -/
theorem eraseBodyInto_next_mono {residual : DialectSet}
    (config : ResidualSyntax residual F)
    (hreturn : ResidualSyntax.ReturnMonotone config)
    {n callerMembers currentMembers : Nat}
    (m : Module (Source residual) n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next : LocalVar)
    (stmts : List (Stmt (Source residual) ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt residual ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (herase : eraseBodyInto config m caller current kind rename next stmts = some result) :
    next ≤ result.2 := by
  fun_induction eraseBodyInto generalizing result <;> simp_all
  all_goals
    aesop (config := { warnOnNonterminal := false })
  · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans ih2
      (Nat.le_trans (hreturn.next_le _ _ _ _ _ _ x_1) ih1))
  · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans ih2 ih1)

set_option linter.flexible false in
/-- Recursive erasure preserves any destination floor respected by current
renaming and return syntax. -/
theorem eraseBodyInto_destinationsAbove {residual : DialectSet}
    (config : ResidualSyntax residual F)
    (stable : ResidualSyntax.RenameStable config)
    (hmono : ResidualSyntax.ReturnMonotone config)
    (hreturn : ResidualSyntax.ReturnFrame config)
    {n callerMembers currentMembers : Nat}
    (m : Module (Source residual) n F) (caller current : Fin n) (kind : BodyKind)
    (rename : LocalVar → LocalVar) (next floor : LocalVar)
    (stmts : List (Stmt (Source residual) ⟨n, current.val, currentMembers⟩ F))
    (result : List (Stmt residual ⟨n, caller.val, callerMembers⟩ F) × LocalVar)
    (hnext : floor ≤ next)
    (hframe : ∀ stmt ∈ stmts, ∀ dest, stmt.dest = some dest → floor ≤ rename dest)
    (herase : eraseBodyInto config m caller current kind rename next stmts = some result) :
    DestinationsAbove floor result.1 := by
  fun_induction eraseBodyInto generalizing floor result <;> simp_all
  all_goals aesop (config := { warnOnNonterminal := false })
  · simp [DestinationsAbove]
  · have hcalleeFrame : ∀ stmt ∈ fn.body, ∀ d, stmt.dest = some d →
        floor ≤ CallPass.inlineVar rename args fn.numParams next h_1 d := by
      intro stmt hmem d hdest
      exact Nat.le_trans hnext
        (CallPass.inlineVar_stmt_dest_ge_base fn rename args next h_1 hmem hdest)
    have hcalleeAbove := ih2 floor
      (Nat.le_trans hnext (Nat.le_add_right next _)) hcalleeFrame
    have hafter := Nat.le_trans
      (Nat.le_trans hnext (Nat.le_add_right next _))
      (eraseBodyInto_next_mono config hmono m caller
        (Call.moduleTarget target current_1.isLt) .compute
        (CallPass.inlineVar rename args fn.numParams next h_1)
        (next + funcVarBound fn) fn.body (tail, afterTail) x)
    exact destinationsAbove_append hcalleeAbove
      (destinationsAbove_append
        (hreturn.destinations floor dest fn.returnVar
          (CallPass.inlineVar rename args fn.numParams next h_1) rename afterTail
          (tail_1, afterTail_1) hafter left x_1)
        (ih1 floor (Nat.le_trans hafter
          (hmono.next_le _ _ _ _ _ _ x_1)) right))
  · have hcalleeFrame : ∀ stmt ∈ fn.body, ∀ d, stmt.dest = some d →
        floor ≤ CallPass.inlineVar rename args fn.numParams next h_1 d := by
      intro stmt hmem d hdest
      exact Nat.le_trans hnext
        (CallPass.inlineVar_stmt_dest_ge_base fn rename args next h_1 hmem hdest)
    have hcalleeAbove := ih2 floor
      (Nat.le_trans hnext (Nat.le_add_right next _)) hcalleeFrame
    have hafter := Nat.le_trans
      (Nat.le_trans hnext (Nat.le_add_right next _))
      (eraseBodyInto_next_mono config hmono m caller
        (Call.moduleTarget target current_1.isLt) .constrain
        (CallPass.inlineVar rename args fn.numParams next h_1)
        (next + funcVarBound fn) fn.body (tail, afterTail) x)
    exact destinationsAbove_append hcalleeAbove (ih1 floor hafter right)
  · intro stmt hmem dest hdest
    rcases List.mem_cons.mp hmem with rfl | hmem
    · apply lowerResidualStmt_dest_ge config stable <;> assumption
    · exact ih1 floor hnext right stmt hmem dest hdest

def eraseComputeFunc {residual : DialectSet} (config : ResidualSyntax residual F)
    {n : Nat} (m : Module (Source residual) n F) (i : Fin n) :
    Option (List (Stmt residual ⟨n, i.val, (m.structs i).members.length⟩ F) ×
      LocalVar) :=
  let fn := (m.structs i).compute
  eraseBodyInto config m i i .compute id (funcVarBound fn) fn.body

def eraseConstrainFunc {residual : DialectSet} (config : ResidualSyntax residual F)
    {n : Nat} (m : Module (Source residual) n F) (i : Fin n) :
    Option (List (Stmt residual ⟨n, i.val, (m.structs i).members.length⟩ F) ×
      LocalVar) :=
  let fn := (m.structs i).constrain
  eraseBodyInto config m i i .constrain id (funcVarBound fn) fn.body

def certifyFunc {residual : DialectSet} {n i numMembers : Nat} {F : Type}
    {kind : Capability} (fn : FuncDef (Source residual) n i F kind numMembers)
    (body : List (Stmt residual ⟨n, i, numMembers⟩ F)) :
    Option (FuncDef residual n i F kind numMembers) :=
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

theorem certifyFunc_fields {residual : DialectSet} {n i numMembers : Nat}
    {F : Type} {kind : Capability}
    (fn : FuncDef (Source residual) n i F kind numMembers)
    (body : List (Stmt residual ⟨n, i, numMembers⟩ F))
    (out : FuncDef residual n i F kind numMembers)
    (hcertify : certifyFunc fn body = some out) :
    out.numParams = fn.numParams ∧ out.body = body ∧ out.returnVar = fn.returnVar := by
  unfold certifyFunc at hcertify
  split at hcertify <;> rename_i hcaps
  · split at hcertify <;> rename_i hssa
    · have hout := Option.some.inj hcertify
      subst out
      exact ⟨rfl, rfl, rfl⟩
    · simp at hcertify
  · simp at hcertify

def eraseStructDef {residual : DialectSet} (config : ResidualSyntax residual F)
    {n : Nat} (m : Module (Source residual) n F) (i : Fin n) :
    Option (StructDef residual n i F) := do
  let computeBody ← eraseComputeFunc config m i
  let constrainBody ← eraseConstrainFunc config m i
  let compute ← certifyFunc (m.structs i).compute computeBody.1
  let constrain ← certifyFunc (m.structs i).constrain constrainBody.1
  pure {
    name := (m.structs i).name
    members := (m.structs i).members
    compute := compute
    constrain := constrain
  }

noncomputable def eraseModule {residual : DialectSet}
    (config : ResidualSyntax residual F) {n : Nat}
    (m : Module (Source residual) n F) : Option (Module residual n F) := by
  classical
  exact if h : ∀ i, ∃ s, eraseStructDef config m i = some s then
    some { structs := fun i => Classical.choose (h i) }
  else none

/-- Successful module erasure exposes each selected structural erasure. -/
theorem eraseModule_struct {residual : DialectSet}
    (config : ResidualSyntax residual F) {n : Nat}
    (m : Module (Source residual) n F) (out : Module residual n F)
    (herase : eraseModule config m = some out) (i : Fin n) :
    eraseStructDef config m i = some (out.structs i) := by
  classical
  unfold eraseModule at herase
  split at herase
  next h =>
    have hout := Option.some.inj herase
    subst out
    exact Classical.choose_spec (h i)
  next h => simp at herase

/-! ## Concrete residual syntax values -/

private def recontextualizeFeltConstrain {sourceCtx targetCtx : OpCtx} :
    ∀ (d : Fin [Felt.sig, ConstrainEq.sig].length),
      ([Felt.sig, ConstrainEq.sig].get d).Op sourceCtx F →
        Option (([Felt.sig, ConstrainEq.sig].get d).Op targetCtx F)
  | ⟨0, _⟩, op => by
      cases op with
      | add d a b => exact some (.add d a b)
      | sub d a b => exact some (.sub d a b)
      | mul d a b => exact some (.mul d a b)
      | div d a b => exact some (.div d a b)
      | neg d a => exact some (.neg d a)
      | inv d a => exact some (.inv d a)
      | const d c => exact some (.const d c)
  | ⟨1, _⟩, op => by
      cases op with
      | eq a b => exact some (.eq a b)

def feltConstrainSyntax [Zero F] :
    ResidualSyntax [Felt.sig, ConstrainEq.sig] F where
  recontextualize := recontextualizeFeltConstrain
  emitReturn := fun {ctx} dest returnVar calleeRename callerRename next =>
    some (CallPass.emitReturnCopy (F := F) (γ := ctx) dest returnVar
      calleeRename callerRename next)

set_option linter.flexible false in
private theorem feltConstrainTransportMetadata [Zero F]
    {sourceCtx targetCtx : OpCtx} :
    ∀ (d : Fin [Felt.sig, ConstrainEq.sig].length)
      (op : ([Felt.sig, ConstrainEq.sig].get d).Op sourceCtx F)
      (out : ([Felt.sig, ConstrainEq.sig].get d).Op targetCtx F),
      (feltConstrainSyntax (F := F)).recontextualize d op = some out →
      ([Felt.sig, ConstrainEq.sig].get d).dest out =
          ([Felt.sig, ConstrainEq.sig].get d).dest op ∧
      ([Felt.sig, ConstrainEq.sig].get d).reads out =
          ([Felt.sig, ConstrainEq.sig].get d).reads op ∧
      ([Felt.sig, ConstrainEq.sig].get d).cap out =
          ([Felt.sig, ConstrainEq.sig].get d).cap op
  | ⟨0, _⟩, op, out, h => by
      cases op <;> simp [feltConstrainSyntax, recontextualizeFeltConstrain] at h <;>
        subst out <;> exact ⟨rfl, rfl, rfl⟩
  | ⟨1, _⟩, op, out, h => by
      cases op
      simp [feltConstrainSyntax, recontextualizeFeltConstrain] at h
      subst out
      exact ⟨rfl, rfl, rfl⟩

theorem feltConstrainRenameStable [Zero F] :
    ResidualSyntax.RenameStable (feltConstrainSyntax (F := F)) where
  dest d op out h := (feltConstrainTransportMetadata d op out h).1
  reads d op out h := (feltConstrainTransportMetadata d op out h).2.1
  cap d op out h := (feltConstrainTransportMetadata d op out h).2.2

def recontextualizeObjectFeltConstrain {sourceCtx targetCtx : OpCtx} :
    ∀ (d : Fin [StructObject.sig, Felt.sig, ConstrainEq.sig].length),
      ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).Op sourceCtx F →
        Option (([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).Op targetCtx F)
  | ⟨0, _⟩, op => by
      cases op with
      | newStruct dest => exact some (.newStruct dest)
      | readMember dest self member =>
        if h : member.val < targetCtx.numMembers then
          exact some (.readMember dest self ⟨member.val, h⟩)
        else exact none
      | writeMember self member src =>
        if h : member.val < targetCtx.numMembers then
          exact some (.writeMember self ⟨member.val, h⟩ src)
        else exact none
  | ⟨1, _⟩, op => by
      cases op with
      | add d a b => exact some (.add d a b)
      | sub d a b => exact some (.sub d a b)
      | mul d a b => exact some (.mul d a b)
      | div d a b => exact some (.div d a b)
      | neg d a => exact some (.neg d a)
      | inv d a => exact some (.inv d a)
      | const d c => exact some (.const d c)
  | ⟨2, _⟩, op => by
      cases op with
      | eq a b => exact some (.eq a b)

def objectFeltConstrainSyntax [Zero F] :
    ResidualSyntax [StructObject.sig, Felt.sig, ConstrainEq.sig] F where
  recontextualize := recontextualizeObjectFeltConstrain
  emitReturn := fun {ctx} dest returnVar calleeRename callerRename next =>
    match dest, returnVar with
    | some d, some r =>
      some ([.op ⟨1, by simp⟩ (.const next 0),
        .op ⟨1, by simp⟩ (.add (callerRename d) (calleeRename r) next)], next + 1)
    | _, _ => some ([], next)

set_option linter.flexible false in
private theorem objectFeltConstrainTransportMetadata [Zero F]
    {sourceCtx targetCtx : OpCtx} :
    ∀ (d : Fin [StructObject.sig, Felt.sig, ConstrainEq.sig].length)
      (op : ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).Op sourceCtx F)
      (out : ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).Op targetCtx F),
      (objectFeltConstrainSyntax (F := F)).recontextualize d op = some out →
      ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).dest out =
          ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).dest op ∧
      ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).reads out =
          ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).reads op ∧
      ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).cap out =
          ([StructObject.sig, Felt.sig, ConstrainEq.sig].get d).cap op
  | ⟨0, _⟩, op, out, h => by
      cases op <;>
        simp [objectFeltConstrainSyntax, recontextualizeObjectFeltConstrain] at h
      all_goals
        first
        | rcases h with ⟨_, hEq⟩
          subst out
          exact ⟨rfl, rfl, rfl⟩
        | subst out
          exact ⟨rfl, rfl, rfl⟩
  | ⟨1, _⟩, op, out, h => by
      cases op <;>
        simp [objectFeltConstrainSyntax, recontextualizeObjectFeltConstrain] at h <;>
        subst out <;> exact ⟨rfl, rfl, rfl⟩
  | ⟨2, _⟩, op, out, h => by
      cases op
      simp [objectFeltConstrainSyntax, recontextualizeObjectFeltConstrain] at h
      subst out
      exact ⟨rfl, rfl, rfl⟩

theorem objectFeltConstrainRenameStable [Zero F] :
    ResidualSyntax.RenameStable (objectFeltConstrainSyntax (F := F)) where
  dest d op out h := (objectFeltConstrainTransportMetadata d op out h).1
  reads d op out h := (objectFeltConstrainTransportMetadata d op out h).2.1
  cap d op out h := (objectFeltConstrainTransportMetadata d op out h).2.2

set_option linter.flexible false in
theorem objectFeltConstrainReturnMonotone [Zero F] :
    ResidualSyntax.ReturnMonotone (objectFeltConstrainSyntax (F := F)) := by
  constructor
  intro ctx dest ret calleeRename callerRename next out h
  cases dest <;> cases ret <;>
    simp [objectFeltConstrainSyntax] at h <;> subst out
  · exact Nat.le_refl next
  · exact Nat.le_refl next
  · exact Nat.le_refl next
  · exact Nat.le_add_right next 1

set_option linter.flexible false in
theorem objectFeltConstrainReturnFrame [Zero F] :
    ResidualSyntax.ReturnFrame (objectFeltConstrainSyntax (F := F)) := by
  constructor
  intro ctx floor dest ret calleeRename callerRename next out hnext hdest h
  cases dest <;> cases ret <;>
    simp [objectFeltConstrainSyntax] at h <;> subst out
  · simp [DestinationsAbove]
  · simp [DestinationsAbove]
  · simp [DestinationsAbove]
  · rename_i callerDest calleeRet
    intro stmt hmem d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · change some next = some d at hd
      simpa [Option.some.inj hd] using hnext
    · change some (callerRename callerDest) = some d at hd
      simpa [Option.some.inj hd] using hdest _ rfl

/-! ## Residual-polymorphic structural correctness -/

/-- Elaboration semantics for the structural Call dialect. A source module is
satisfied when successful Call expansion yields a residual module satisfied by
the same statically selected residual state. This leaves all residual meaning
to `target`; Call contributes only hygienic module expansion.

The direct field-local Call evaluator in `CallSemantics` is an independent
model and its existing preservation/reflection theorem validates this
elaboration semantics for the leaf specialization. -/
noncomputable def expandedSourceStage {residual : DialectSet}
    (config : ResidualSyntax residual F) {n : Nat}
    (target : ModuleStage residual n F) :
    ModuleStage (Source residual) n F where
  State := target.State
  satisfies state m := ∃ out,
    eraseModule config m = some out ∧ target.satisfies state out

/-- Every rename-stable residual syntax value induces a certified structural
Call erasure for any interpretation of the residual module. The proof is
fully parametric in that interpretation and in its concrete state type. -/
noncomputable def structuralPass {residual : DialectSet}
    (config : ResidualSyntax residual F)
    (_stable : ResidualSyntax.RenameStable config) {n : Nat}
    (target : ModuleStage residual n F) :
    EraseDialect Call.sig residual (expandedSourceStage config target) target where
  lower m := match eraseModule config m with
    | some out => .ok out
    | none => .error "call erasure failed"
  stateRel _ _ sourceState targetState := sourceState = targetState
  preservation := by
    intro m out sourceState hlower hsatisfies
    rcases hsatisfies with ⟨semanticOut, hsemantic, hsatisfies⟩
    cases herase : eraseModule config m with
    | none => rw [herase] at hlower; cases hlower
    | some result =>
      rw [herase] at hlower
      have hresult : result = out := Except.ok.inj hlower
      have hsemanticResult : semanticOut = result := by
        rw [herase] at hsemantic
        exact (Option.some.inj hsemantic).symm
      subst out
      subst semanticOut
      exact ⟨sourceState, rfl, hsatisfies⟩
  reflection := by
    intro m out targetState hlower hsatisfies
    cases herase : eraseModule config m with
    | none => rw [herase] at hlower; cases hlower
    | some result =>
      rw [herase] at hlower
      have hresult : result = out := Except.ok.inj hlower
      subst out
      exact ⟨targetState, rfl, ⟨result, herase, hsatisfies⟩⟩

end Dialect.CallErasure
