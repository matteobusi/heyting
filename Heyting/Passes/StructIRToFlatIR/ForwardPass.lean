/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Passes.StructIRToFlatIR.Readback

/-!
# StructIR → FlatIR: Forward Satisfaction and PresReflPass Instance

`BodySatCtx` packages the six invariants maintained through the body-level
forward proof. The `bodySatCtx_*_cons_satisfies` and
`materialize_compile_*_satisfies` family advance this context through each
instruction type.

`compileConstrainBody_instrVars_in_range` proves all compiled variable
references are in range — used by `bodySatCtx_call_callee_frame`.

Top-level theorems:
- `body_forward_satisfies` — BodySatCtx → FlatIR.satisfies
- `preservation_via_simulation` — StructIR sat → FlatIR sat
- `body_reflection_wt` — FlatIR sat → StructIR eval holds
- `CorrectPass` — the `PresReflPass` instance
-/
namespace StructIRToFlatIR

open StructIR
open StructIRToFlatIR.CompressTactics

variable {F : Type} [Field F] {n : Nat}

def BodySatCtx
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (_objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) : Prop :=
  StructIR.isSSA init stmts = true ∧
    (∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y)) ∧
    (∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos) ∧
    freshBase + StructIRFreshen.maxVarBody stmts < runFresh ∧
    localCeilConstrainBody m i runFresh stmts ≤ witnessBase ∧
    (∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh)

omit [Field F] in
lemma bodySatCtx.mk
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init stmts = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody stmts < runFresh)
    (hCeil : localCeilConstrainBody m i runFresh stmts ≤ witnessBase)
    (hInitBound : ∀ y, init y = true → StructIRFreshen.freshMap freshBase y < runFresh) :
    BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts :=
  ⟨hSSA, hAgree, hSlots, hFit, hCeil, hInitBound⟩

omit [Field F] in
lemma bodySatCtx.ssa
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    StructIR.isSSA init stmts = true := h.1

omit [Field F] in
lemma bodySatCtx.agree
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y) :=
    h.2.1

omit [Field F] in
lemma bodySatCtx.slots
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos := h.2.2.1

omit [Field F] in
lemma bodySatCtx.fit
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    freshBase + StructIRFreshen.maxVarBody stmts < runFresh := h.2.2.2.1

omit [Field F] in
lemma bodySatCtx.ceil
    {witnessBase : Nat} {m : Module n F} {i : Fin n}
    {init : Nat → Bool} {freshBase : Nat}
    {wt : FlatIR.Witness F} {ws : StructIR.Witness F}
    {env : LocalEnv F} {objEnv : ObjEnv} {runFresh : Nat}
    {stmts : List (ConstrainStmt n i F (m.structs i).members.length)}
    (h : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts) :
    localCeilConstrainBody m i runFresh stmts ≤ witnessBase := h.2.2.2.2.1

omit [Field F] in
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
    (env.update (StructIRFreshen.freshMap freshBase dest) val) objEnv runFresh rest
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact isSSA_tail_of_dest init stmt rest dest hSSA hd
  · have hDestFalse : init dest = false :=
      isSSA_dest_not_init init (stmt :: rest) stmt dest hSSA (by simp) hd
    exact witness_env_agree_after_write freshBase init wt env dest val hAgree hDestFalse
  · exact witness_slots_agree_after_head_write witnessBase m i freshBase runFresh dest wt ws
      stmt rest val hSlots hFit hCeilCons hd
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

omit [Field F] in
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
  refine bodySatCtx.mk witnessBase m i init freshBase wt ws env objEnv runFresh rest
    ?_ hAgree hSlots ?_ ?_ hInitBound
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

omit [Field F] in
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
  simp only [compileConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt,
    List.map_cons, List.mem_cons] at hmem
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
          env (StructIRFreshen.freshMap freshBase src1) +
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) +
             env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) +
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) +
              env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) +
          env (StructIRFreshen.freshMap freshBase src2))
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) +
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) +
              env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) +
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) +
              env (StructIRFreshen.freshMap freshBase src2)))
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
  simp only [compileConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt,
    List.map_cons, List.mem_cons] at hmem
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
          env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) -
             env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) -
              env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) -
          env (StructIRFreshen.freshMap freshBase src2))
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) -
              env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) -
              env (StructIRFreshen.freshMap freshBase src2)))
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
  simp only [compileConstrainBody, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) -
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) -
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
          env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc1' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) -
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) -
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) =
          env (StructIRFreshen.freshMap freshBase src1) := by
        simpa [StructIRFreshen.renameBody] using hSrc1
    have hSrc2' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) -
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) -
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src2) =
          env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hSrc2
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) -
              env (StructIRFreshen.freshMap freshBase src2)))
           objEnv runFresh
           (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
           (StructIRFreshen.freshMap freshBase dest)
         = env (StructIRFreshen.freshMap freshBase src1) -
             env (StructIRFreshen.freshMap freshBase src2) := hDest'
      _ = materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) -
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) -
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) -
          materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) -
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) -
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
          env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) *
             env (StructIRFreshen.freshMap freshBase src2)))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        env (StructIRFreshen.freshMap freshBase src1) *
          env (StructIRFreshen.freshMap freshBase src2))
    (hSrc1 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              env (StructIRFreshen.freshMap freshBase src2)))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src1))
    (hSrc2 :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              env (StructIRFreshen.freshMap freshBase src2)))
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
  simp only [compileConstrainBody, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) *
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) *
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
           env (StructIRFreshen.freshMap freshBase src1) *
             env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc1' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) *
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) *
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) =
          env (StructIRFreshen.freshMap freshBase src1) := by
        simpa [StructIRFreshen.renameBody] using hSrc1
    have hSrc2' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) *
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) *
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src2) =
          env (StructIRFreshen.freshMap freshBase src2) := by
        simpa [StructIRFreshen.renameBody] using hSrc2
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
           else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (env (StructIRFreshen.freshMap freshBase src1) *
              env (StructIRFreshen.freshMap freshBase src2)))
           objEnv runFresh
           (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
           (StructIRFreshen.freshMap freshBase dest)
         = env (StructIRFreshen.freshMap freshBase src1) *
             env (StructIRFreshen.freshMap freshBase src2) := hDest'
      _ = materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) *
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) *
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src1) *
          materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              env (StructIRFreshen.freshMap freshBase src1) *
                env (StructIRFreshen.freshMap freshBase src2)
             else wt v)
             (env.update (StructIRFreshen.freshMap freshBase dest)
               (env (StructIRFreshen.freshMap freshBase src1) *
                 env (StructIRFreshen.freshMap freshBase src2)))
             objEnv runFresh
             (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
  simp only [compileConstrainBody, List.mem_cons] at hmem
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
              objEnv runFresh
              (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
              objEnv runFresh
              (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
              objEnv runFresh
              (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
              objEnv runFresh
              (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
              (StructIRFreshen.freshMap freshBase src1) *
            (materializeConstrainBody witnessBase m i
                (fun v => if v = StructIRFreshen.freshMap freshBase dest then
                  env (StructIRFreshen.freshMap freshBase src1) *
                    (env (StructIRFreshen.freshMap freshBase src2))⁻¹
                 else wt v)
                (env.update (StructIRFreshen.freshMap freshBase dest)
                  (env (StructIRFreshen.freshMap freshBase src1) *
                    (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
                objEnv runFresh
              (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
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
  simp only [compileConstrainBody, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (-(env (StructIRFreshen.freshMap freshBase src))))
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
          -(env (StructIRFreshen.freshMap freshBase src)) := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (-(env (StructIRFreshen.freshMap freshBase src))))
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src) =
          env (StructIRFreshen.freshMap freshBase src) := by
        simpa [StructIRFreshen.renameBody] using hSrc
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            (-(env (StructIRFreshen.freshMap freshBase src))))
           objEnv runFresh
           (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
           (StructIRFreshen.freshMap freshBase dest)
         = -(env (StructIRFreshen.freshMap freshBase src)) := hDest'
      _ = -materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              -(env (StructIRFreshen.freshMap freshBase src)) else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              (-(env (StructIRFreshen.freshMap freshBase src))))
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src) := by rw [hSrc']
  · exact ih instr hmem

theorem materialize_compile_feltInv_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F) (objEnv : ObjEnv)
    (runFresh dest src : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1)
    (hDest :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase dest) =
        (env (StructIRFreshen.freshMap freshBase src))⁻¹)
    (hSrc :
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
          objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (StructIRFreshen.freshMap freshBase src) =
        env (StructIRFreshen.freshMap freshBase src)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltInv dest src :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltInv dest src :: rest))).1 := by
  simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
    materializeConstrainBody]
  intro instr hmem
  simp only [compileConstrainBody, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · have hDest' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase dest) =
          (env (StructIRFreshen.freshMap freshBase src))⁻¹ := by
        simpa [StructIRFreshen.renameBody] using hDest
    have hSrc' :
        materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src) =
          env (StructIRFreshen.freshMap freshBase src) := by
        simpa [StructIRFreshen.renameBody] using hSrc
    exact calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then
            (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest)
            ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
           objEnv runFresh
           (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
           (StructIRFreshen.freshMap freshBase dest)
         = (env (StructIRFreshen.freshMap freshBase src))⁻¹ := hDest'
      _ = (materializeConstrainBody witnessBase m i
            (fun v => if v = StructIRFreshen.freshMap freshBase dest then
              (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
            (env.update (StructIRFreshen.freshMap freshBase dest)
              ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
            objEnv runFresh
            (List.map (StructIRFreshen.renameStmt (StructIRFreshen.freshMap freshBase)) rest)
            (StructIRFreshen.freshMap freshBase src))⁻¹ := by rw [hSrc']
  · exact ih instr hmem

theorem materialize_step_feltInv_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA init (.feltInv dest src :: rest) = true)
    (hAgree : ∀ y, init y = true →
      wt (StructIRFreshen.freshMap freshBase y) = env (StructIRFreshen.freshMap freshBase y))
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltInv dest src :: rest) < runFresh)
    (_hCeilCons : localCeilConstrainBody m i runFresh (.feltInv dest src :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltInv dest src :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltInv dest src :: rest))).1 := by
  let stmt : ConstrainStmt n i F (m.structs i).members.length := .feltInv dest src
  have hd : stmt.dest = some dest := by rfl
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest ((env (StructIRFreshen.freshMap freshBase src))⁻¹)
    stmt rest hSSA hAgree hd hFit
  have hSrc := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src ((env (StructIRFreshen.freshMap freshBase src))⁻¹)
    stmt rest hSSA hAgree hd
    (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc_ne : src ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltInv_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src rest ih hDest (by simpa [hsrc_ne] using hSrc)

theorem bodySatCtx_feltInv_cons_satisfies
    (witnessBase : Nat) (m : Module n F) (i : Fin n)
    (init : Nat → Bool) (freshBase : Nat)
    (wt : FlatIR.Witness F) (ws : StructIR.Witness F)
    (env : LocalEnv F) (objEnv : ObjEnv) (runFresh : Nat)
    (dest src : Nat)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh
      (.feltInv dest src :: rest))
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          (env (StructIRFreshen.freshMap freshBase src))⁻¹ else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          ((env (StructIRFreshen.freshMap freshBase src))⁻¹))
        objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)).1) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltInv dest src :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.feltInv dest src :: rest))).1 := by
  exact materialize_step_feltInv_satisfies witnessBase m i init freshBase wt ws env objEnv runFresh
    dest src rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
     (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
       objEnv runFresh dest ((env (StructIRFreshen.freshMap freshBase src))⁻¹)
       (.feltInv dest src) rest hctx (by intro target args h; cases h) rfl))
    ih

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
  simp only [compileConstrainBody, List.mem_cons] at hmem
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
           wt (encodeWitnessVar witnessBase
                 (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
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
         wt (encodeWitnessVar witnessBase
               (objEnv (StructIRFreshen.freshMap freshBase self)) member.val))
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
           (encodeWitnessVar witnessBase
             (objEnv (StructIRFreshen.freshMap freshBase self)) member.val) =
          wt (encodeWitnessVar witnessBase
                (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest)))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.readMember dest self member :: rest))).1 := by
  rw [materializeConstrainBody_readMember_rename_eq]
  intro instr hmem
  simp only [compileConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt,
    List.map_cons, List.mem_cons] at hmem
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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.constrainEq src1 src2 :: rest) < runFresh)
    (_hCeil : localCeilConstrainBody m i runFresh (.constrainEq src1 src2 :: rest) ≤ witnessBase)
    (hEq :
      env (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src2))
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
  have hEq1 := materializeConstrainBody_head_readback witnessBase m i init wt env objEnv
    freshBase runFresh src1 (.constrainEq src1 src2) rest hSSA hAgree hFit
    (by simp [ConstrainStmt.reads])
  have hEq2 := materializeConstrainBody_head_readback witnessBase m i init wt env objEnv
    freshBase runFresh src2 (.constrainEq src1 src2) rest hSSA hAgree hFit
    (by simp [ConstrainStmt.reads])
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
              materializeConstrainBody_tail_readback_no_dest witnessBase m i init wt env objEnv
                freshBase runFresh src1 (.constrainEq src1 src2) rest hSSA hAgree rfl
                (isSSA_read_true_of_mem init (.constrainEq src1 src2) rest src1 hSSA
                  (by simp [ConstrainStmt.reads]))
                (freshMap_read_lt_runFresh_of_fit_cons freshBase runFresh src1
                  (.constrainEq src1 src2) rest hFit (by simp [ConstrainStmt.reads]))
      _ = env (StructIRFreshen.freshMap freshBase src2) := hEq
      _ = materializeConstrainBody witnessBase m i wt env objEnv runFresh
            (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
            (StructIRFreshen.freshMap freshBase src2) := by
            symm
            simpa [ConstrainStmt.dest] using
              materializeConstrainBody_tail_readback_no_dest witnessBase m i init wt env objEnv
                freshBase runFresh src2 (.constrainEq src1 src2) rest hSSA hAgree rfl
                (isSSA_read_true_of_mem init (.constrainEq src1 src2) rest src2 hSSA
                  (by simp [ConstrainStmt.reads]))
                (freshMap_read_lt_runFresh_of_fit_cons freshBase runFresh src2
                  (.constrainEq src1 src2) rest hFit (by simp [ConstrainStmt.reads]))
  exact materialize_compile_constrainEq_satisfies witnessBase m i freshBase wt env objEnv
    runFresh src1 src2 rest ih hTailEq

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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltAdd dest src1 src2 :: rest) < runFresh)
    (_hCeilCons :
      localCeilConstrainBody m i runFresh (.feltAdd dest src1 src2 :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) +
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) +
             env (StructIRFreshen.freshMap freshBase src2)))
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
  let val :=
    env (StructIRFreshen.freshMap freshBase src1) + env (StructIRFreshen.freshMap freshBase src2)
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest val stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src1 val
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src2 val
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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltSub dest src1 src2 :: rest) < runFresh)
    (_hCeilCons :
      localCeilConstrainBody m i runFresh (.feltSub dest src1 src2 :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) -
             env (StructIRFreshen.freshMap freshBase src2)))
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
  let val :=
    env (StructIRFreshen.freshMap freshBase src1) - env (StructIRFreshen.freshMap freshBase src2)
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest val stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src1 val
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src2 val
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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltMul dest src1 src2 :: rest) < runFresh)
    (_hCeilCons :
      localCeilConstrainBody m i runFresh (.feltMul dest src1 src2 :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) *
             env (StructIRFreshen.freshMap freshBase src2)))
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
  let val :=
    env (StructIRFreshen.freshMap freshBase src1) * env (StructIRFreshen.freshMap freshBase src2)
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest val stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src1 val
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src2 val
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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltNeg dest src :: rest) < runFresh)
    (_hCeilCons : localCeilConstrainBody m i runFresh (.feltNeg dest src :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
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
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest (-(env (StructIRFreshen.freshMap freshBase src)))
    stmt rest hSSA hAgree hd hFit
  have hSrc := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src (-(env (StructIRFreshen.freshMap freshBase src)))
    stmt rest hSSA hAgree hd
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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltConst dest c :: rest) < runFresh)
    (_hCeilCons : localCeilConstrainBody m i runFresh (.feltConst dest c :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
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
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest c stmt rest hSSA hAgree hd hFit
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
    (_hSlots : ∀ pos, wt (encodeWitnessPos witnessBase pos) = ws pos)
    (hFit : freshBase + StructIRFreshen.maxVarBody (.feltDiv dest src1 src2 :: rest) < runFresh)
    (_hCeilCons :
      localCeilConstrainBody m i runFresh (.feltDiv dest src1 src2 :: rest) ≤ witnessBase)
    (_hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (hSrc2Nz : env (StructIRFreshen.freshMap freshBase src2) ≠ 0)
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
  have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest
    (env (StructIRFreshen.freshMap freshBase src1) *
      (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    stmt rest hSSA hAgree hd hFit
  have hSrc1 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src1
    (env (StructIRFreshen.freshMap freshBase src1) *
      (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hSrc2 := materializeConstrainBody_head_read_after_write witnessBase m i init wt env
    objEnv freshBase runFresh dest src2
    (env (StructIRFreshen.freshMap freshBase src1) *
      (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
    stmt rest hSSA hAgree hd (by simp [stmt, ConstrainStmt.reads]) hFit
  have hsrc1_ne : src1 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src1 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  have hsrc2_ne : src2 ≠ dest :=
    isSSA_read_ne_dest init stmt rest dest src2 hSSA hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltDiv_satisfies witnessBase m i freshBase wt env objEnv runFresh
    dest src1 src2 rest ih hSrc2Nz hDest
    (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)

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
    (hFit :
      freshBase + StructIRFreshen.maxVarBody (.readMember dest self member :: rest) < runFresh)
    (hCeilCons :
      localCeilConstrainBody m i runFresh (.readMember dest self member :: rest) ≤ witnessBase)
    (hCeilRest : localCeilConstrainBody m i runFresh rest ≤ witnessBase)
    (ih : FlatIR.satisfies
      (materializeConstrainBody witnessBase m i
        (fun v => if v = StructIRFreshen.freshMap freshBase dest then
          wt (encodeWitnessVar witnessBase
                (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (wt (encodeWitnessVar witnessBase
                  (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
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
  let val :=
    wt (encodeWitnessVar witnessBase (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
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
        (encodeWitnessVar witnessBase
          (objEnv (StructIRFreshen.freshMap freshBase self)) member.val) = val := by
    let pos : StructIR.VarId := (objEnv (StructIRFreshen.freshMap freshBase self), member.val)
    have hslot :
        materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest) val)
          objEnvStep runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
          (encodeWitnessPos witnessBase pos) = ws pos :=
      materializeConstrainBody_tail_slot_after_write witnessBase m i freshBase runFresh dest
        wt ws env objEnvStep val stmt rest hSlots hFit hCeilRest hd hCeilCons pos
    calc
      materializeConstrainBody witnessBase m i
          (fun v => if v = StructIRFreshen.freshMap freshBase dest then val else wt v)
          (env.update (StructIRFreshen.freshMap freshBase dest) val)
          objEnvStep runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) rest)
           (encodeWitnessVar witnessBase
             (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
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
    (hEq :
      env (StructIRFreshen.freshMap freshBase src1) =
        env (StructIRFreshen.freshMap freshBase src2))
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
          env (StructIRFreshen.freshMap freshBase src1) +
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) +
             env (StructIRFreshen.freshMap freshBase src2)))
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
     (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
       objEnv runFresh dest
       (env (StructIRFreshen.freshMap freshBase src1) +
         env (StructIRFreshen.freshMap freshBase src2))
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
          env (StructIRFreshen.freshMap freshBase src1) -
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) -
             env (StructIRFreshen.freshMap freshBase src2)))
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
     (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
       objEnv runFresh dest
       (env (StructIRFreshen.freshMap freshBase src1) -
         env (StructIRFreshen.freshMap freshBase src2))
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
          env (StructIRFreshen.freshMap freshBase src1) *
            env (StructIRFreshen.freshMap freshBase src2)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (env (StructIRFreshen.freshMap freshBase src1) *
             env (StructIRFreshen.freshMap freshBase src2)))
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
     (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
       objEnv runFresh dest
       (env (StructIRFreshen.freshMap freshBase src1) *
         env (StructIRFreshen.freshMap freshBase src2))
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
     (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
       objEnv runFresh dest (-(env (StructIRFreshen.freshMap freshBase src)))
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
  exact materialize_step_feltConst_satisfies witnessBase m i init freshBase wt ws env objEnv
    runFresh dest c rest (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
      objEnv runFresh dest c (.feltConst dest c) rest hctx
      (by intro target args h; cases h) rfl))
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
          env (StructIRFreshen.freshMap freshBase src1) *
            (env (StructIRFreshen.freshMap freshBase src2))⁻¹
         else wt v)
        (env.update (StructIRFreshen.freshMap freshBase dest)
          (env (StructIRFreshen.freshMap freshBase src1) *
            (env (StructIRFreshen.freshMap freshBase src2))⁻¹))
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
     (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
       objEnv runFresh dest
       (env (StructIRFreshen.freshMap freshBase src1) *
         (env (StructIRFreshen.freshMap freshBase src2))⁻¹)
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
          wt (encodeWitnessVar witnessBase
                (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)
         else wt v)
         (env.update (StructIRFreshen.freshMap freshBase dest)
           (wt (encodeWitnessVar witnessBase
                  (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
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
  exact materialize_step_readMember_satisfies witnessBase m i init freshBase wt ws env objEnv
    runFresh dest self member rest
    (bodySatCtx.ssa hctx) (bodySatCtx.agree hctx) (bodySatCtx.slots hctx)
    (bodySatCtx.fit hctx) (bodySatCtx.ceil hctx)
    (bodySatCtx.ceil (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env
      objEnv runFresh dest
      (wt (encodeWitnessVar witnessBase
        (objEnv (StructIRFreshen.freshMap freshBase self)) member.val))
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
    | none => simp
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
          (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest ≤
        witnessBase := by
      simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody,
        reservedNextFresh] using hCeil
    have hReservedLeWitness : reservedNextFresh ≤ witnessBase := by
      exact le_trans
        (localCeilConstrainBody_next_ge m j reservedNextFresh
          (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody))
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
          (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest ≤
        witnessBase := by
      simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody,
        reservedNextFresh] using hCeil
    have hCeilRenamed : localCeilConstrainBody m j reservedNextFresh
        (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody) ≤ witnessBase := by
      exact le_trans
        (localCeilConstrainBody_next_ge m i
          (localCeilConstrainBody m j reservedNextFresh
            (StructIRFreshen.renameBody (fun v => runFresh + v) calleeBody)) rest)
        hCeil'
    exact
      (localCeilConstrainBody_rename m j reservedNextFresh (fun v => runFresh + v) calleeBody) ▸
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
  have hReserved : runFresh ≤ reservedNextFresh :=
    le_trans (Nat.le_add_right _ _) (le_max_left _ _)
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
    exact lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hReservedLeWitness : reservedNextFresh ≤ witnessBase := by
    exact le_trans
      (localCeilConstrainBody_next_ge m j reservedNextFresh freshBody)
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
      exact lt_of_le_of_lt
        (Nat.add_le_add_left (maxVarBody_tail_le_cons (.call target args) rest) _) hFit
    exact lt_of_lt_of_le hFitRest hRunLeNext
  · simpa [localCeilConstrainBody, StructIRFreshen.freshenBody, j, calleeBody, reservedNextFresh,
      freshBody, nextFresh'', hNextEq] using hCeil
  · intro y hy
    exact lt_of_lt_of_le (hInitBound y hy) hRunLeNext

/-- All instruction variables in a compiled renamed body are either
    in `[base, ceil)` or `≥ witnessBase`. -/
private lemma getElem?_le_foldl_max_seed (seed : Nat) (xs : List Nat) (k a : Nat)
    (h : xs[k]? = some a) :
    a ≤ xs.foldl max seed := by
  induction xs generalizing seed k with
  | nil =>
      cases h
  | cons x xs ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero] at h
          cases h
          simp only [List.foldl_cons]
          exact le_trans (Nat.le_max_right _ _) (foldl_max_ge_seed _ _)
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          simp only [List.foldl_cons]
          exact ih (max seed x) k h

private lemma compileParamBindings_go_instrVars_in_range
    (base nextFresh idx remaining ceiling : Nat) (args : List Nat)
    (hBaseNext : base ≤ nextFresh)
    (hArgsIdx : ∀ (k a : Nat), args[k]? = some a → base ≤ a ∧ a < ceiling)
    (hCeil : nextFresh + idx + remaining ≤ ceiling)
    (instr : FlatIR.Instr F)
    (hInstr : instr ∈ compileParamBindings.go (F := F) args (StructIRFreshen.freshMap nextFresh)
      idx remaining)
    (v : Nat) (hv : v ∈ FlatIR.instrVars instr) :
    base ≤ v ∧ v < ceiling := by
  induction remaining generalizing idx instr with
  | zero =>
      simp [compileParamBindings.go] at hInstr
  | succ k ih =>
      simp only [compileParamBindings.go] at hInstr
      rcases List.mem_append.mp hInstr with hHead | hRest
      · cases hcase : args[idx]? with
        | some arg =>
            rw [hcase] at hHead
            simp only [List.mem_singleton] at hHead
            subst hHead
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            have hDestLo : base ≤ StructIRFreshen.freshMap nextFresh idx := by
              exact le_trans hBaseNext (Nat.le_add_right _ _)
            have hDestHi : StructIRFreshen.freshMap nextFresh idx < ceiling := by
              simp [StructIRFreshen.freshMap]
              omega
            have hArgRange := hArgsIdx idx arg hcase
            rcases hv with rfl | rfl
            · exact ⟨hDestLo, hDestHi⟩
            · exact hArgRange
        | none =>
            rw [hcase] at hHead
            simp only [List.mem_singleton] at hHead
            subst hHead
            simp only [FlatIR.instrVars, List.mem_singleton] at hv
            have hDestLo : base ≤ StructIRFreshen.freshMap nextFresh idx := by
              exact le_trans hBaseNext (Nat.le_add_right _ _)
            have hDestHi : StructIRFreshen.freshMap nextFresh idx < ceiling := by
              simp [StructIRFreshen.freshMap]
              omega
            rcases hv with rfl
            exact ⟨hDestLo, hDestHi⟩
      · have hCeil' : nextFresh + (idx + 1) + k ≤ ceiling := by omega
        exact ih (idx + 1) hCeil' instr hRest hv

private lemma compileParamBindings_instrVars_in_range
    (base nextFresh numParams ceiling : Nat) (args : List Nat)
    (hBaseNext : base ≤ nextFresh)
    (hArgsIdx : ∀ (k a : Nat), args[k]? = some a → base ≤ a ∧ a < ceiling)
    (hCeil : nextFresh + numParams ≤ ceiling)
    (instr : FlatIR.Instr F)
    (hInstr :
      instr ∈ compileParamBindings (F := F) numParams args (StructIRFreshen.freshMap nextFresh))
    (v : Nat) (hv : v ∈ FlatIR.instrVars instr) :
    base ≤ v ∧ v < ceiling := by
  unfold compileParamBindings at hInstr
  simpa using compileParamBindings_go_instrVars_in_range (F := F) base nextFresh 0 numParams
    ceiling args hBaseNext hArgsIdx (by simpa using hCeil) instr hInstr v hv

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
  induction origBody generalizing objEnv nextFresh with
  | nil =>
      simp [StructIRFreshen.renameBody, compileConstrainBody] at hInstr
  | cons stmt rest ih =>
      have hBound' : base + StructIRFreshen.maxVarBody rest < nextFresh := by
        exact lt_of_le_of_lt (Nat.add_le_add_left (maxVarBody_tail_le_cons stmt rest) _) hBound
      cases stmt with
      | feltAdd d s1 s2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltAdd d s1 s2 :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltAdd d s1 s2) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | feltSub d s1 s2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltSub d s1 s2 :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltSub d s1 s2) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | feltMul d s1 s2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltMul d s1 s2 :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltMul d s1 s2) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | feltDiv d s1 s2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltDiv d s1 s2 :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltDiv d s1 s2) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | feltNeg d s =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltNeg d s :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltNeg d s) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | feltInv d s =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltInv d s :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltInv d s) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | feltConst d c =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.feltConst d c :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.feltConst d c) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_singleton] at hv
            rw [hS]
            rcases hv with rfl
            left
            exact ⟨by omega, by
              simp [StructIRFreshen.maxVarStmt] at hmv
              omega⟩
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | readMember d s member =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.readMember d s member :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            rw [compileConstrainBody_localCeil_eq, compileConstrainBody_localCeil_eq]
            simp [localCeilConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt]
          have hTailObjEq :
              (compileConstrainBody witnessBase m i
                (objEnv.update (base + d) (objEnv (base + s) ++ [member.val])) nextFresh
                (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 =
              (compileConstrainBody witnessBase m i objEnv nextFresh
                (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            rw [compileConstrainBody_localCeil_eq, compileConstrainBody_localCeil_eq]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.readMember d s member) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl
            · left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩
            · right
              simp [encodeWitnessVar, encodeWitnessPos]
          · rcases ih (objEnv.update (base + d) (objEnv (base + s) ++ [member.val]))
              nextFresh hBound' hTail with
              ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ (hTailObjEq ▸ hhi)⟩
            · right; exact hge
      | constrainEq s1 s2 =>
          simp only [StructIRFreshen.renameBody, List.map_cons, StructIRFreshen.renameStmt,
            compileConstrainBody, List.mem_cons] at hInstr
          have hS : (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v)
                (ConstrainStmt.constrainEq s1 s2 :: rest))).2.2 =
            (compileConstrainBody witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            simp [StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody]
          rcases hInstr with rfl | hTail
          · have hmv := maxVarStmt_le_maxVarBody_cons (ConstrainStmt.constrainEq s1 s2) rest
            have hge := compileConstrainBody_next_ge witnessBase m i objEnv nextFresh
              (StructIRFreshen.renameBody (fun v => base + v) rest)
            simp only [FlatIR.instrVars, List.mem_cons, List.not_mem_nil, or_false] at hv
            rw [hS]
            rcases hv with rfl | rfl <;>
              (left; exact ⟨by omega, by
                simp [StructIRFreshen.maxVarStmt] at hmv; omega⟩)
          · rcases ih objEnv nextFresh hBound' hTail with ⟨hlo, hhi⟩ | hge
            · left; exact ⟨hlo, hS ▸ hhi⟩
            · right; exact hge
      | call target args =>
          let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
          let calleeBody := (m.structs j).constrain.body
          let numParams := (m.structs j).constrain.numParams
          let adjustedObjEnv : ObjEnv := fun v =>
            if nextFresh ≤ v then
              match (args.map (fun x => base + x))[v - nextFresh]? with
              | some arg => objEnv arg
              | none => []
            else
              []
          let reservedNextFresh :=
            max (nextFresh + (StructIRFreshen.maxVarBody calleeBody + 1)) (nextFresh + numParams)
          let freshBody := StructIRFreshen.renameBody (fun v => nextFresh + v) calleeBody
          let nextFresh'' :=
            (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
          have hBaseNextFresh : base ≤ nextFresh := by
            omega
          have hReservedLe : reservedNextFresh ≤ nextFresh'' := by
            simpa [j, calleeBody, numParams, adjustedObjEnv, reservedNextFresh, freshBody,
              nextFresh''] using
              compileConstrainBody_next_ge witnessBase m j adjustedObjEnv reservedNextFresh
                freshBody
          have hNextFreshLe : nextFresh ≤ nextFresh'' := by
            exact le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) hReservedLe
          have hTailGe : nextFresh'' ≤
              (compileConstrainBody witnessBase m i objEnv nextFresh''
                (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            exact compileConstrainBody_next_ge witnessBase m i objEnv nextFresh''
              (StructIRFreshen.renameBody (fun v => base + v) rest)
          have hOverallEq :
              (compileConstrainBody witnessBase m i objEnv nextFresh
                (StructIRFreshen.renameBody (fun v => base + v)
                  (ConstrainStmt.call target args :: rest))).2.2 =
              (compileConstrainBody witnessBase m i objEnv nextFresh''
                (StructIRFreshen.renameBody (fun v => base + v) rest)).2.2 := by
            have hNextEq :
                nextFresh'' = localCeilConstrainBody m j reservedNextFresh freshBody := by
              exact compileConstrainBody_localCeil_eq witnessBase m j adjustedObjEnv
                reservedNextFresh freshBody
            rw [compileConstrainBody_localCeil_eq, compileConstrainBody_localCeil_eq]
            rw [hNextEq]
            simp [localCeilConstrainBody, j, calleeBody, numParams, reservedNextFresh,
              freshBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt,
              StructIRFreshen.freshenBody]
          have hBoundTail : base + StructIRFreshen.maxVarBody rest < nextFresh'' := by
            exact lt_of_lt_of_le hBound' hNextFreshLe
          have hCalleeBound :
              nextFresh + StructIRFreshen.maxVarBody calleeBody < reservedNextFresh := by
            refine lt_of_lt_of_le ?_ (Nat.le_max_left _ _)
            omega
          have hArgsIdx : ∀ (k a : Nat), (args.map (fun x : Nat => base + x))[k]? = some a →
              base ≤ a ∧ a < nextFresh'' := by
            intro k a hget
            rw [List.getElem?_map] at hget
            cases hsrc : args[k]? with
            | none =>
                simp [hsrc] at hget
            | some arg =>
                have hget' : some (base + arg) = some a := by simpa [hsrc] using hget
                injection hget' with hEq
                subst hEq
                have hArgLe : arg ≤ args.foldl max 0 :=
                  getElem?_le_foldl_max_seed 0 args k arg hsrc
                have hCallMax :
                    args.foldl max 0 ≤ StructIRFreshen.maxVarBody (.call target args :: rest) :=
                  by
                  have hmv :=
                    maxVarStmt_le_maxVarBody_cons (.call target args : ConstrainStmt n i F _) rest
                  simpa [StructIRFreshen.maxVarStmt] using hmv
                have hArgFresh : base + arg < nextFresh := by
                  have hArgBody : arg ≤ StructIRFreshen.maxVarBody (.call target args :: rest) :=
                    le_trans hArgLe hCallMax
                  have hAdd :
                      base + arg ≤
                        base + StructIRFreshen.maxVarBody (.call target args :: rest) :=
                    Nat.add_le_add_left hArgBody base
                  exact lt_of_le_of_lt hAdd hBound
                refine ⟨by omega, lt_of_lt_of_le ?_ hNextFreshLe⟩
                exact hArgFresh
          have hParamCeil : nextFresh + numParams ≤ nextFresh'' := by
            exact le_trans (Nat.le_max_right _ _) hReservedLe
          have hComp : instr ∈
              compileParamBindings (F := F) numParams (args.map (fun x => base + x))
                (StructIRFreshen.freshMap nextFresh) ++
              ((compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh
                  freshBody).1 ++
                (compileConstrainBody witnessBase m i objEnv nextFresh''
                  (StructIRFreshen.renameBody (fun v => base + v) rest)).1) := by
            simpa [j, calleeBody, numParams, adjustedObjEnv, reservedNextFresh, freshBody,
              nextFresh'', StructIRFreshen.renameBody, StructIRFreshen.renameStmt,
              compileConstrainBody, StructIRFreshen.freshenBody, List.append_assoc] using hInstr
          rw [List.mem_append] at hComp
          rcases hComp with hParam | hComp
          · have hRange :=
              compileParamBindings_instrVars_in_range (F := F) base nextFresh numParams
               nextFresh'' (args.map (fun x => base + x)) hBaseNextFresh hArgsIdx hParamCeil
              instr hParam v hv
            left
            exact ⟨hRange.1, by
              rw [hOverallEq]
              exact lt_of_lt_of_le hRange.2 hTailGe⟩
          · rw [List.mem_append] at hComp
            rcases hComp with hCallee | hTail
            · rcases ih_i j target.isLt adjustedObjEnv nextFresh reservedNextFresh calleeBody
                hCalleeBound instr hCallee v hv with ⟨hlo, hhi⟩ | hge
              · left
                exact ⟨le_trans hBaseNextFresh hlo, by
                  rw [hOverallEq]
                  exact lt_of_lt_of_le hhi hTailGe⟩
              · right
                exact hge
            · rcases ih objEnv nextFresh'' hBoundTail hTail with ⟨hlo, hhi⟩ | hge
              · left
                exact ⟨hlo, hOverallEq ▸ hhi⟩
              · right
                exact hge
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

/-- Wrapper: instruction variables of compiled renamed body lie in `[base, ceil)` or above
`witnessBase`. -/
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
          (base ≤ v ∧ v <
              (compileConstrainBody witnessBase m i objEnv nextFresh
                (StructIRFreshen.renameBody (fun v => base + v) origBody)).2.2) ∨
        witnessBase ≤ v)
  · intro k ih_k i hi objEnv base nextFresh origBody hBound instr hInstr v hv
    exact compileConstrainBody_instrVars_in_range_aux witnessBase m i
      (fun j hj => ih_k j.val (hi ▸ hj) j rfl) objEnv base nextFresh origBody hBound instr
      hInstr v hv
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
    let _wtAfterCallee :=
      materializeConstrainBody witnessBase m j wtParams adjustedEnv adjustedObjEnv
        reservedNextFresh freshBody
    let _nextFresh'' :=
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).2.2
    let wtFinal :=
      materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase)
          (.call target args :: rest))
    FlatIR.satisfies wtFinal
      (compileConstrainBody witnessBase m j adjustedObjEnv reservedNextFresh freshBody).1 := by
  intro j calleeBody numParams adjustedObjEnv wtParams adjustedEnv reservedNextFresh freshBody
    wtAfterCallee nextFresh'' wtFinal
  have _ := wtAfterCallee
  have _ := nextFresh''
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
  have hCalleeCtx :
      BodySatCtx witnessBase m j (fun v => decide (v < numParams)) runFresh wtParams ws
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
  have hRestCtx :
      BodySatCtx witnessBase m i init freshBase wtAfterCallee ws env objEnv nextFresh'' rest := by
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
    simp only [adjustedObjEnv, reservedNextFresh, freshBody, nextFresh'', numParams, calleeBody, j,
      StructIRFreshen.renameBody, StructIRFreshen.renameStmt, compileConstrainBody,
      StructIRFreshen.freshenBody, List.map, ← List.getElem?_map, List.append_assoc]
    rfl
  rw [hCompEq, satisfies_append, satisfies_append]
  exact ⟨⟨hParamSat, hCalleeFrame⟩, hRestSatFinal⟩

omit [Field F] in
private lemma localEnv_update_freshMap_comp (env : LocalEnv F) (freshBase dest : Nat) (val : F) :
    (fun x => (env.update (StructIRFreshen.freshMap freshBase dest) val)
      (StructIRFreshen.freshMap freshBase x)) =
    (LocalEnv.update (fun x => env (StructIRFreshen.freshMap freshBase x)) dest val) := by
  funext x
  simp only [LocalEnv.update, beq_iff_eq,
    (StructIRFreshen.freshMap_injective freshBase).eq_iff]

omit [Field F] in
private lemma objEnv_update_freshMap_comp (objEnv : ObjEnv) (freshBase dest : Nat)
    (val : InstancePath) :
    (fun x => (ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest) val)
      (StructIRFreshen.freshMap freshBase x)) =
    (ObjEnv.update (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) dest val) := by
  funext x
  simp only [ObjEnv.update, beq_iff_eq,
    (StructIRFreshen.freshMap_injective freshBase).eq_iff]

private lemma eval_after_update
    (m : Module n F) (ws : StructIR.Witness F) (i : Fin n)
    (env : LocalEnv F) (objEnv : ObjEnv) (freshBase dest : Nat) (val : F)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hEval : evalConstrainBody m ws i
      (LocalEnv.update (fun x => env (StructIRFreshen.freshMap freshBase x)) dest val)
      (fun x => objEnv (StructIRFreshen.freshMap freshBase x))
      rest) :
    evalConstrainBody m ws i
      (fun x => (env.update (StructIRFreshen.freshMap freshBase dest) val)
        (StructIRFreshen.freshMap freshBase x))
      (fun x => objEnv (StructIRFreshen.freshMap freshBase x))
      rest := by
  rwa [← localEnv_update_freshMap_comp] at hEval

private lemma eval_after_update_obj
    (m : Module n F) (ws : StructIR.Witness F) (i : Fin n)
    (env : LocalEnv F) (objEnv : ObjEnv) (freshBase dest : Nat) (val : F)
    (objVal : InstancePath)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (hEval : evalConstrainBody m ws i
      (LocalEnv.update (fun x => env (StructIRFreshen.freshMap freshBase x)) dest val)
      (ObjEnv.update (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) dest objVal)
      rest) :
    evalConstrainBody m ws i
      (fun x => (env.update (StructIRFreshen.freshMap freshBase dest) val)
        (StructIRFreshen.freshMap freshBase x))
      (fun x => (ObjEnv.update objEnv (StructIRFreshen.freshMap freshBase dest) objVal)
        (StructIRFreshen.freshMap freshBase x))
      rest := by
  rwa [← localEnv_update_freshMap_comp, ← objEnv_update_freshMap_comp] at hEval

private theorem body_forward_satisfies_aux
    (witnessBase : Nat) (m : Module n F) (ws : StructIR.Witness F)
    (i : Fin n)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
    (ih_i : ∀ (j : Fin n), j.val < i.val →
      ∀ (init : Nat → Bool) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (runFresh : Nat)
        (stmts : List (ConstrainStmt n j F (m.structs j).members.length)),
      BodySatCtx witnessBase m j init freshBase wt ws env objEnv runFresh stmts →
      evalConstrainBody m ws j
        (fun x => env (StructIRFreshen.freshMap freshBase x))
        (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) stmts →
      FlatIR.satisfies
        (materializeConstrainBody witnessBase m j wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts))
        (compileConstrainBody witnessBase m j objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)).1)
    (init : Nat → Bool) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts)
    (hEval : evalConstrainBody m ws i
      (fun x => env (StructIRFreshen.freshMap freshBase x))
      (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) stmts) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)).1 := by
  induction stmts generalizing init wt env objEnv runFresh with
  | nil =>
      simp only [StructIRFreshen.renameBody, List.map_nil, compileConstrainBody,
        FlatIR.satisfies, List.not_mem_nil, false_implies, implies_true]
  | cons stmt rest ih =>
      cases stmt with
      | feltAdd dest src1 src2 =>
          simp only [evalConstrainBody, true_and] at hEval
          exact bodySatCtx_feltAdd_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest src1 src2 rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.feltAdd dest src1 src2) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval))
      | feltSub dest src1 src2 =>
          simp only [evalConstrainBody, true_and] at hEval
          exact bodySatCtx_feltSub_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest src1 src2 rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.feltSub dest src1 src2) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval))
      | feltMul dest src1 src2 =>
          simp only [evalConstrainBody, true_and] at hEval
          exact bodySatCtx_feltMul_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest src1 src2 rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.feltMul dest src1 src2) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval))
      | feltDiv dest src1 src2 =>
          simp only [evalConstrainBody] at hEval
          obtain ⟨hNz, hEval_rest⟩ := hEval
          exact bodySatCtx_feltDiv_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest src1 src2 rest hctx hNz
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.feltDiv dest src1 src2) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval_rest))
      | feltNeg dest src =>
          simp only [evalConstrainBody, true_and] at hEval
          exact bodySatCtx_feltNeg_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest src rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.feltNeg dest src) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval))
      | feltInv dest src =>
          simp only [evalConstrainBody, true_and] at hEval
          exact bodySatCtx_feltInv_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest src rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.feltInv dest src) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval))
      | feltConst dest c =>
          simp only [evalConstrainBody, true_and] at hEval
          exact bodySatCtx_feltConst_cons_satisfies witnessBase m i init freshBase wt ws env objEnv
            runFresh dest c rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest c (.feltConst dest c) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update m ws i env objEnv freshBase dest _ rest hEval))
      | readMember dest self member =>
          simp only [evalConstrainBody, true_and] at hEval
          have hSlots := bodySatCtx.slots hctx
          have hWitEq : ws (objEnv (StructIRFreshen.freshMap freshBase self), member.val) =
              wt (encodeWitnessVar witnessBase
                (objEnv (StructIRFreshen.freshMap freshBase self)) member.val) := by
            rw [← hSlots (objEnv (StructIRFreshen.freshMap freshBase self), member.val)]
            simp [encodeWitnessVar, encodeWitnessPos]
          have hEval' : evalConstrainBody m ws i
              (LocalEnv.update (fun x => env (StructIRFreshen.freshMap freshBase x)) dest
                (wt (encodeWitnessVar witnessBase
                  (objEnv (StructIRFreshen.freshMap freshBase self)) member.val)))
              (ObjEnv.update (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) dest
                (objEnv (StructIRFreshen.freshMap freshBase self) ++ [member.val]))
              rest := by
            have : (LocalEnv.update (fun x => env (StructIRFreshen.freshMap freshBase x)) dest
                (wt (encodeWitnessVar witnessBase
                  (objEnv (StructIRFreshen.freshMap freshBase self)) member.val))) =
                (LocalEnv.update (fun x => env (StructIRFreshen.freshMap freshBase x)) dest
                  (ws (objEnv (StructIRFreshen.freshMap freshBase self), member.val))) := by
              ext x
              simp only [LocalEnv.update, beq_iff_eq]
              split <;> [exact hWitEq.symm; rfl]
            rw [this]
            exact hEval
          exact bodySatCtx_readMember_cons_satisfies witnessBase m i init freshBase wt ws env
            objEnv runFresh dest self member rest hctx
            (ih _ _ _ _ _
              (bodySatCtx_after_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh dest _ (.readMember dest self member) rest hctx
                (by intro target args h; cases h) rfl)
              (eval_after_update_obj m ws i env objEnv freshBase dest _ _ rest hEval'))
      | constrainEq src1 src2 =>
          simp only [evalConstrainBody] at hEval
          obtain ⟨hEq, hEval_rest⟩ := hEval
          exact bodySatCtx_constrainEq_cons_satisfies witnessBase m i init freshBase wt ws env
            objEnv runFresh src1 src2 rest hctx hEq
            (ih init wt env objEnv runFresh
              (bodySatCtx_after_no_dest_noncall witnessBase m i init freshBase wt ws env objEnv
                runFresh (.constrainEq src1 src2) rest hctx
                (by intro target args h; cases h) rfl)
              hEval_rest)
      | call target args =>
          simp only [evalConstrainBody] at hEval
          obtain ⟨hCalleeEval, hRestEval⟩ := hEval
          exact bodySatCtx_call_cons_satisfies witnessBase m i hSSA init freshBase wt ws env objEnv
            runFresh target args rest hctx hCalleeEval hRestEval
            (fun init' freshBase' wt' env' objEnv' runFresh' stmts' hctx' heval' =>
              ih_i ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩ target.isLt
                init' freshBase' wt' env' objEnv' runFresh' stmts' hctx' heval')
            (fun init' wt' env' objEnv' runFresh' hctx' heval' =>
              ih init' wt' env' objEnv' runFresh' hctx' heval')

/-- Forward body satisfaction wrapped with well-founded induction on `i`. -/
theorem body_forward_satisfies
    (witnessBase : Nat) (m : Module n F) (ws : StructIR.Witness F)
    (hSSA : ∀ j : Fin n,
      StructIR.isSSA (fun v => v < (m.structs j).constrain.numParams)
        (m.structs j).constrain.body = true)
    (i : Fin n) (init : Nat → Bool) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
    (objEnv : ObjEnv) (runFresh : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hctx : BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts)
    (hEval : evalConstrainBody m ws i
      (fun x => env (StructIRFreshen.freshMap freshBase x))
      (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) stmts) :
    FlatIR.satisfies
      (materializeConstrainBody witnessBase m i wt env objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts))
      (compileConstrainBody witnessBase m i objEnv runFresh
        (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)).1 := by
  revert i init freshBase wt env objEnv runFresh stmts hctx hEval
  intro i
  apply Nat.strongRecOn (n := i.val)
    (motive := fun k => ∀ (i : Fin n), i.val = k →
      ∀ (init : Nat → Bool) (freshBase : Nat) (wt : FlatIR.Witness F) (env : LocalEnv F)
        (objEnv : ObjEnv) (runFresh : Nat)
        (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
      BodySatCtx witnessBase m i init freshBase wt ws env objEnv runFresh stmts →
      evalConstrainBody m ws i
        (fun x => env (StructIRFreshen.freshMap freshBase x))
        (fun x => objEnv (StructIRFreshen.freshMap freshBase x)) stmts →
      FlatIR.satisfies
        (materializeConstrainBody witnessBase m i wt env objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts))
        (compileConstrainBody witnessBase m i objEnv runFresh
          (StructIRFreshen.renameBody (StructIRFreshen.freshMap freshBase) stmts)).1)
  · intro k ih_k i hi init freshBase wt env objEnv runFresh stmts hctx hEval
    apply body_forward_satisfies_aux witnessBase m ws i hSSA
    · intro j hj
      exact ih_k j.val (hi ▸ hj) j rfl
    · exact hctx
    · exact hEval
  · rfl

theorem preservation_via_simulation
    (m : Module (n + 1) F) (ws : StructIR.Witness F)
    (hsat : StructIR.satisfies ws m) :
    ∃ wt, (ExecutablePass (F := F) (n := n)).witnessRel m ws wt ∧
      FlatIR.satisfies wt (compileProgram m) := by
  refine ⟨witnessCompile m ws, witnessCompile_rel m ws, ?_⟩
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let numParams := (m.structs mainIdx).constrain.numParams
  let numMembers := (m.structs mainIdx).members.length
  let localBase := localBoundOfModule m
  let ρ := StructIRFreshen.freshMap localBase
  let renamedBody := StructIRFreshen.renameBody ρ mainBody
  let initObjEnv := ObjEnv.update (fun _ => []) (ρ 0) []
  let initNextFresh := max (localBase + StructIRFreshen.maxVarBody mainBody + 1)
    (localBase + numParams)
  let wBase := witnessBase m
  change FlatIR.satisfies (witnessCompile m ws) (compileProgram m)
  change FlatIR.satisfies (witnessCompile m ws)
    (compileMainParamBindings (F := F) wBase numMembers numParams ρ ++
      (compileConstrainBody wBase m mainIdx initObjEnv initNextFresh renamedBody).1)
  rw [satisfies_append]
  refine ⟨witnessCompile_main_param_bindings_satisfy m ws, ?_⟩
  let wtSeed := seedMainParamLocalsWitness localBase numParams numMembers ws
    (witnessSlotLift wBase ws)
  let envSeed : LocalEnv F := seedMainParamLocalsEnv localBase numParams numMembers ws
  change FlatIR.satisfies
    (materializeConstrainBody wBase m mainIdx wtSeed envSeed initObjEnv initNextFresh renamedBody)
    (compileConstrainBody wBase m mainIdx initObjEnv initNextFresh renamedBody).1
  change FlatIR.satisfies
    (materializeConstrainBody wBase m mainIdx wtSeed envSeed initObjEnv initNextFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap localBase) mainBody))
    (compileConstrainBody wBase m mainIdx initObjEnv initNextFresh
      (StructIRFreshen.renameBody (StructIRFreshen.freshMap localBase) mainBody)).1
  apply body_forward_satisfies wBase m ws m.all_ssa mainIdx
    (fun v => decide (v < numParams)) localBase wtSeed envSeed initObjEnv initNextFresh mainBody
  · refine bodySatCtx.mk wBase m mainIdx (fun v => decide (v < numParams)) localBase
      wtSeed ws envSeed initObjEnv initNextFresh mainBody (m.all_ssa mainIdx) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [decide_eq_true_eq] at hy
      simp only [wtSeed, seedMainParamLocalsWitness, envSeed, seedMainParamLocalsEnv,
        StructIRFreshen.freshMap, Nat.add_sub_cancel_left, hy, and_self, ite_true,
        Nat.le_add_right]
    · intro pos
      have hwBase_ge_params : localBase + numParams ≤ wBase := by
        have hInit : localBase + numParams ≤ initNextFresh := by simp [initNextFresh]
        have hCeil : initNextFresh ≤ wBase := by
          simpa [wBase, witnessBase] using
            localCeilConstrainBody_next_ge m mainIdx initNextFresh renamedBody
        exact le_trans hInit hCeil
      have hsub : numParams ≤ encodeWitnessPos wBase pos - localBase := by
        apply Nat.le_sub_of_add_le
        rw [Nat.add_comm]
        exact le_trans hwBase_ge_params (by simp [encodeWitnessPos])
      have hnot : ¬ (localBase ≤ encodeWitnessPos wBase pos ∧
          encodeWitnessPos wBase pos - localBase < numParams) := by
        intro h
        exact Nat.not_lt_of_ge hsub h.2
      change wtSeed (encodeWitnessPos wBase pos) = ws pos
      simp only [wtSeed, seedMainParamLocalsWitness, hnot, ite_false]
      exact witnessSlotLift_encodeWitnessPos wBase ws pos
    · simp [initNextFresh]
    · have hRename := localCeilConstrainBody_rename m mainIdx initNextFresh ρ mainBody
      have hwBase : wBase = localCeilConstrainBody m mainIdx initNextFresh renamedBody := by
        simp [wBase, witnessBase, mainIdx, mainBody, numParams, localBase, ρ, renamedBody,
          initNextFresh]
      rw [← hRename]
      simp [hwBase, renamedBody]
    · intro y hy
      simp only [decide_eq_true_eq] at hy
      simp [StructIRFreshen.freshMap, initNextFresh]
      omega
  · have hEvalOrig : evalConstrainBody m ws mainIdx
        (fun k => if k < numParams then ws (StructIR.paramCoord numMembers k) else 0)
        (ObjEnv.update (fun _ => []) 0 []) mainBody := hsat
    have hEnvEq : (fun x => envSeed (StructIRFreshen.freshMap localBase x)) =
        (fun k => if k < numParams then ws (StructIR.paramCoord numMembers k) else 0) := by
      funext x
      simp [envSeed, seedMainParamLocalsEnv, StructIRFreshen.freshMap, Nat.add_sub_cancel_left]
    have hObjEq : (fun x => initObjEnv (StructIRFreshen.freshMap localBase x)) =
        (ObjEnv.update (fun _ => ([] : StructIR.InstancePath)) 0 []) := by
      funext x
      change initObjEnv (ρ x) = ObjEnv.update (fun _ => ([] : StructIR.InstancePath)) 0 [] x
      simp only [ObjEnv.update, initObjEnv]
      by_cases hx : x = 0
      · subst hx
        simp
      · have hxρ : ρ x ≠ ρ 0 := fun h => hx (StructIRFreshen.freshMap_injective _ h)
        have hxρ' : (ρ x == ρ 0) = false := by simp [hxρ]
        have hx' : (x == 0) = false := by simp [hx]
        rw [hxρ', hx']
    rw [hEnvEq, hObjEq]
    exact hEvalOrig

/-- Top-level preservation: StructIR satisfies source → FlatIR satisfies compiled program. -/
instance CorrectPreservingPass :
    PreservingPass (StructIR.Language n F) (FlatIR.Language F) where
  toPass := ExecutablePass (F := F) (n := n)
  preservation := by
    intro ws m hsat
    exact preservation_via_simulation (F := F) (n := n) m ws hsat

/-- Top-level reflection used by `CorrectPass`. -/
private theorem correctPass_reflection
    (wt : FlatIR.Witness F) (m : StructIR.Module (n + 1) F)
    (hSat : FlatIR.satisfies wt (compileProgram (F := F) (n := n) m)) :
    ∃ ws : StructIR.Witness F,
      (ExecutablePass (F := F) (n := n)).witnessRel m ws wt ∧ StructIR.satisfies ws m := by
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
      have hSwap :
          evalConstrainBody m ws mainIdx (wt ∘ ρ) (ObjEnv.update (fun _ => []) 0 []) mainBody ↔
            evalConstrainBody m ws mainIdx envSeed (ObjEnv.update (fun _ => []) 0 []) mainBody :=
        evalConstrainBody_env_agree_on_init m ws mainIdx (wt ∘ ρ) envSeed
          (ObjEnv.update (fun _ => []) 0 []) mainBody (m.all_ssa mainIdx)
          (by intro v hv
              exact hParamAgree v (by simpa using hv))
      -- Conclude: `StructIR.satisfies ws m` unfolds definitionally to this goal.
      change evalConstrainBody m ws mainIdx envSeed
            (ObjEnv.update (fun _ => []) 0 []) mainBody
      exact hSwap.mp hCanonObj

instance CorrectPass : PresReflPass (StructIR.Language n F) (FlatIR.Language F) where
  compile := compileProgram (F := F)
  witnessRel := (ExecutablePass (F := F) (n := n)).witnessRel
  preservation := CorrectPreservingPass.preservation
  reflection := by
    intro wt p hs
    simpa using correctPass_reflection (F := F) (n := n) wt p hs

end StructIRToFlatIR
