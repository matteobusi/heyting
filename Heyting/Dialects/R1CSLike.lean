/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Dialects.Felt
import Heyting.Dialects.ConstrainEq
import Heyting.Core.WitnessCodec
import Heyting.Languages.R1CS
import Heyting.Passes.Tactics

/-!
# R1CS-like instruction dialect

Single-dialect, SSA instruction form immediately above R1CS. Arithmetic
instructions update semantic environment; equality instructions constrain it.
Every operation has direct constraint, witness, materialization, and checking
semantics.

## Semantic boundaries

`sem` is the sequential handler interpretation used by generic dialect lowering.
`satisfies` instead checks all equations against a fixed terminal witness.
`materializeBody` constructs that witness; `R1CSLikePass` relates the two views.

## Main results and proof sketch

- `check_true_iff` proves that the Boolean checker decides terminal satisfaction.
- `compileWitness_satisfies_iff` proves equivalence for constructed auxiliary wires.
- `toR1CS_reflection` reflects an arbitrary satisfying R1CS witness by `readback`.
- `CorrectPass` packages existential preservation and reflection; `compilationArtifact`
  additionally supplies constructive forwarding and exact readback.

The arithmetic proofs split on the operation and normalize its linear combinations.
Division uses both quotient and nonzero-denominator equations. Inverse splits on
zero input and uses all three equations to force the output, even when auxiliary
wires were chosen by an arbitrary prover. List induction lifts the operation results
to programs. No parser or serializer is covered by these theorems.
-/

namespace Dialect.R1CSLike

open Dialect

inductive Op (γ : OpCtx) (F : Type) where
  | assign (op : Felt.Op γ F)
  | assertEq (src1 src2 : LocalVar)
  deriving Repr, DecidableEq

def dest : Op γ F → Option LocalVar
  | .assign op => Felt.dest op
  | .assertEq _ _ => none

def reads : Op γ F → List LocalVar
  | .assign op => Felt.reads op
  | .assertEq a b => [a, b]

def cap : Op γ F → Capability
  | .assign _ => .pure
  | .assertEq _ _ => .constraint

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .assign op => .assign (Felt.mapVars ρ op)
  | .assertEq a b => .assertEq (ρ a) (ρ b)

def sig : OpSig where
  Op := Op
  dest := dest
  reads := reads
  mapVars := mapVars
  cap := cap
  mapVars_id := by
    intro γ F op
    cases op with
    | assign felt => cases felt <;> rfl
    | assertEq => rfl
  mapVars_comp := by
    intro γ F ρ σ op
    cases op with
    | assign felt => cases felt <;> rfl
    | assertEq => rfl
  dest_mapVars := by
    intro γ F ρ op
    cases op with
    | assign felt => cases felt <;> rfl
    | assertEq => rfl
  reads_mapVars := by
    intro γ F ρ op
    cases op with
    | assign felt => cases felt <;> simp [mapVars, reads, Felt.mapVars, Felt.reads]
    | assertEq => rfl
  cap_mapVars := by intro γ F ρ op; cases op <;> rfl

def sem (F : Type) [Field F] (Δ : DialectSet := [sig]) : DialectSem Δ sig F where
  constrainStep := fun _ctx op env =>
    match op with
    | .assign felt => (Felt.applyOp felt env, True)
    | .assertEq a b => (env, env a = env b)
  computeStep := fun _ctx op env =>
    match op with
    | .assign felt => some (Felt.applyOp felt env)
    | .assertEq _ _ => some env
  constrainStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h
    cases op with
    | assign felt =>
      refine ⟨Iff.rfl, ?_⟩
      intro d hd
      have hd' : d = Felt.destVar felt := by
        change Felt.dest felt = some d at hd
        rw [Felt.dest_eq] at hd
        exact (Option.some.inj hd).symm
      subst d
      simp only
      rw [Felt.applyOp_at_dest, Felt.applyOp_at_dest]
      exact Felt.evalVal_reads_congr felt env₁ env₂ (by simpa [reads] using h)
    | assertEq a b =>
      change ∀ v ∈ [a, b], env₁ v = env₂ v at h
      have ha := h a (by simp)
      have hb := h b (by simp)
      constructor
      · change (env₁ a = env₁ b) ↔ (env₂ a = env₂ b)
        rw [ha, hb]
      · intro d hd
        change none = some d at hd
        cases hd
  constrainStep_frame := by
    intro n γ ctx op env v hv
    cases op with
    | assign felt =>
      exact Felt.applyOp_at_other felt env v (by
        intro h
        subst v
        exact hv (Felt.dest_eq felt))
    | assertEq a b => rfl
  computeStep_reads_congr := by
    intro n γ ctx op env₁ env₂ h d hd
    cases op with
    | assign felt =>
      have hd' : d = Felt.destVar felt := by
        simp only [sig, dest, Felt.dest_eq] at hd
        exact (Option.some.inj hd).symm
      subst d
      simp only [Option.map]
      rw [Felt.applyOp_at_dest, Felt.applyOp_at_dest]
      exact congrArg some (Felt.evalVal_reads_congr felt env₁ env₂
        (by simpa [reads] using h))
    | assertEq a b => simp [sig, dest] at hd
  computeStep_status_congr := by
    intro n γ ctx op env₁ env₂ h
    cases op <;> rfl
  computeStep_frame := by
    intro n γ ctx op env env' v hsome hv
    cases op with
    | assign felt =>
      have hout : env' = Felt.applyOp felt env := by simpa using hsome.symm
      rw [hout]
      exact Felt.applyOp_at_other felt env v (by
        intro h
        subst v
        exact hv (Felt.dest_eq felt))
    | assertEq a b =>
      have hout : env' = env := Option.some.inj hsome.symm
      subst env'
      rfl

abbrev Set : DialectSet := [sig]

def ix : Fin Set.length := ⟨0, by simp [Set]⟩

theorem fin_eq_ix (d : Fin Set.length) : d = ix := by
  ext
  exact Nat.lt_one_iff.mp d.isLt

/-- Extract operation from a statement in this single-dialect set. -/
def stmtOp : Stmt Set γ F → Op γ F
  | .op ⟨0, _⟩ op => op
  | .op ⟨n + 1, h⟩ _ => by
      simp [Set] at h

@[simp] theorem stmtOp_op (op : Op γ F) : stmtOp (.op ix op) = op := by
  rfl

@[simp] theorem stmtOp_zero (h : 0 < Set.length) (op : Op γ F) :
    stmtOp (.op ⟨0, h⟩ op) = op := by
  rfl

/-- Compile one leaf operation directly to R1CS constraints.

This is terminal-dialect lowering: no compatibility IR is constructed. -/
def compileOp [Field F] : Op γ F → List (R1CS.Constraint F)
  | .assign (.add d a b) =>
      [{ A := [(.var a, 1), (.var b, 1)],
         B := [(.varOne, 1)], C := [(.var d, 1)] }]
  | .assign (.sub d a b) =>
      [{ A := [(.var a, 1), (.var b, -1)],
         B := [(.varOne, 1)], C := [(.var d, 1)] }]
  | .assign (.mul d a b) =>
      [{ A := [(.var a, 1)], B := [(.var b, 1)], C := [(.var d, 1)] }]
  | .assign (.div d a b) =>
      [{ A := [(.var b, 1)], B := [(.var d, 1)], C := [(.var a, 1)] },
       { A := [(.var b, 1)], B := [(.aux b, 1)], C := [(.varOne, 1)] }]
  | .assign (.neg d a) =>
      [{ A := [(.var a, 1)], B := [(.varOne, -1)], C := [(.var d, 1)] }]
  | .assign (.inv d a) =>
      [{ A := [(.var a, 1)], B := [(.var d, 1)],
         C := [(.varOne, 1), (.auxIsZero a, -1)] },
       { A := [(.var a, 1)], B := [(.auxIsZero a, 1)], C := [] },
       { A := [(.var d, 1)], B := [(.auxIsZero a, 1)], C := [] }]
  | .assign (.const d c) =>
      [{ A := [(.varOne, c)], B := [(.varOne, 1)], C := [(.var d, 1)] }]
  | .assertEq a b =>
      [{ A := [(.var a, 1)], B := [(.varOne, 1)], C := [(.var b, 1)] }]

/-- Compile terminal dialect statements directly to constraint lists. -/
def compileConstraints [Field F] {γ : OpCtx} :
    List (Stmt Set γ F) → List (R1CS.Constraint F)
  | [] => []
  | .op d op :: rest =>
      (by
        have hd : d = ix := fin_eq_ix d
        subst d
        exact compileOp op) ++ compileConstraints rest

theorem compileConstraints_cons [Field F] {γ : OpCtx}
    (stmt : Stmt Set γ F) (rest : List (Stmt Set γ F)) :
    compileConstraints (stmt :: rest) =
      compileOp (stmtOp stmt) ++ compileConstraints rest := by
  cases stmt with
  | op d op =>
      have hd : d = ix := fin_eq_ix d
      subst d
      rfl

/-- Compile a terminal dialect body directly to an R1CS system. -/
def toR1CS [Field F] {γ : OpCtx} (body : List (Stmt Set γ F)) : R1CS.System F :=
  { constraints := compileConstraints body }

/-! ## Terminal witness codec -/

/-- Values assigned to terminal dialect locals before R1CS wire expansion. -/
abbrev Witness (F : Type) := LocalVar → F

/-- Update one terminal local while executing a canonical leaf witness. -/
def writeWitness [DecidableEq F] (w : Witness F) (dest : LocalVar) (value : F) :
    Witness F :=
  fun v => if v = dest then value else w v

/-- Execute one terminal leaf operation. Equality remains an observation, not
a witness-generation fault. Division by zero is explicit because direct R1CS
encoding requires an inverse witness. -/
def materializeOp [Field F] [DecidableEq F] (w : Witness F) (op : Op γ F) :
    Except String (Witness F) :=
  match op with
  | .assign (.add d a b) => .ok (writeWitness w d (w a + w b))
  | .assign (.sub d a b) => .ok (writeWitness w d (w a - w b))
  | .assign (.mul d a b) => .ok (writeWitness w d (w a * w b))
  | .assign (.div d a b) =>
      if w b = 0 then .error s!"division by zero at local {b}"
      else .ok (writeWitness w d (w a * (w b)⁻¹))
  | .assign (.neg d a) => .ok (writeWitness w d (-w a))
  | .assign (.inv d a) => .ok (writeWitness w d (w a)⁻¹)
  | .assign (.const d c) => .ok (writeWitness w d c)
  | .assertEq _ _ => .ok w

/-- Execute terminal assignments in source order. -/
def materializeBody [Field F] [DecidableEq F] {γ : OpCtx} :
    List (Stmt Set γ F) → Witness F → Except String (Witness F)
  | [], w => .ok w
  | stmt :: rest, w => materializeOp w (stmtOp stmt) >>= materializeBody rest

/-- Satisfaction of one terminal operation by final local values. -/
def satisfiesOp [Field F] (w : Witness F) : Op γ F → Prop
  | .assign (.add d a b) => w d = w a + w b
  | .assign (.sub d a b) => w d = w a - w b
  | .assign (.mul d a b) => w d = w a * w b
  | .assign (.div d a b) => w b ≠ 0 ∧ w d = w a * (w b)⁻¹
  | .assign (.neg d a) => w d = -w a
  | .assign (.inv d a) => w d = (w a)⁻¹
  | .assign (.const d c) => w d = c
  | .assertEq a b => w a = w b

/-- Terminal dialect satisfaction, independent from compatibility IRs. -/
def satisfies [Field F] {γ : OpCtx} (w : Witness F)
    (body : List (Stmt Set γ F)) : Prop :=
  ∀ stmt ∈ body, satisfiesOp w (stmtOp stmt)

/-- Executable satisfaction checker for one terminal operation. -/
def checkOp [Field F] [DecidableEq F] (w : Witness F) : Op γ F → Bool
  | .assign (.add d a b) => decide (w d = w a + w b)
  | .assign (.sub d a b) => decide (w d = w a - w b)
  | .assign (.mul d a b) => decide (w d = w a * w b)
  | .assign (.div d a b) => decide (w b ≠ 0 ∧ w d = w a * (w b)⁻¹)
  | .assign (.neg d a) => decide (w d = -w a)
  | .assign (.inv d a) => decide (w d = (w a)⁻¹)
  | .assign (.const d c) => decide (w d = c)
  | .assertEq a b => decide (w a = w b)

/-- The operation checker decides its fixed-witness satisfaction predicate.
Proof: split on the operation and reduce `decide`. -/
theorem checkOp_true_iff [Field F] [DecidableEq F] (w : Witness F) (op : Op γ F) :
    checkOp w op = true ↔ satisfiesOp w op := by
  cases op with
  | assign felt => cases felt <;> simp [checkOp, satisfiesOp]
  | assertEq => simp [checkOp, satisfiesOp]

/-- Executable terminal satisfaction checker. -/
def check [Field F] [DecidableEq F] {γ : OpCtx} (w : Witness F)
    (body : List (Stmt Set γ F)) : Bool :=
  body.all fun stmt ↦ checkOp w (stmtOp stmt)

/-- The body checker accepts exactly when every terminal operation is satisfied.
Proof: rewrite list-wide Boolean conjunction using `checkOp_true_iff`. -/
theorem check_true_iff [Field F] [DecidableEq F] {γ : OpCtx}
    (w : Witness F) (body : List (Stmt Set γ F)) :
    check w body = true ↔ satisfies w body := by
  simp [check, satisfies, checkOp_true_iff]

/-- Terminal program package. Existential operation context is intentionally
hidden: R1CS constraint collection needs no module-level SSA context. -/
inductive Program (F : Type) where
  | mk {γ : OpCtx} (body : List (Stmt Set γ F))

/-- Execute a terminal program's leaf assignments. -/
def Program.materialize [Field F] [DecidableEq F] :
    Program F → Witness F → Except String (Witness F)
  | .mk body, w => materializeBody body w

/-- Check terminal program satisfaction. -/
def Program.check [Field F] [DecidableEq F] : Program F → Witness F → Bool
  | .mk body, w => Dialect.R1CSLike.check w body

/-- Direct terminal compilation. -/
def compileProgram [Field F] : Program F → R1CS.System F
  | .mk body => toR1CS body

/-- Terminal language used by constructive backend artifacts. -/
instance Language (F : Type) [Field F] : _root_.Language LocalVar F where
  Program := Program F
  satisfies := fun w program =>
    match program with
    | .mk body => satisfies w body

theorem Program.check_true_iff [Field F] [DecidableEq F]
    (program : Program F) (w : Witness F) :
    program.check w = true ↔ (Language F).satisfies w program := by
  cases program
  exact Dialect.R1CSLike.check_true_iff w _

/-- Construct R1CS wire assignment directly from terminal local values. -/
def compileWitness [Field F] (w : Witness F) : R1CS.Witness F :=
  fun | .varOne => 1
      | .var v => w v
      | .aux v => (w v)⁻¹
      | .auxIsZero v => 1 - w v * (w v)⁻¹

/-- Read terminal local values from ordinary R1CS wires. -/
def readback [Field F] (w : R1CS.Witness F) : Witness F :=
  fun v => w (.var v)

/-- Constructing auxiliary wires leaves ordinary local values unchanged on readback. -/
@[simp] theorem readback_compileWitness [Field F] (w : Witness F) :
    readback (compileWitness w) = w := by
  funext v
  rfl

set_option linter.flexible false in
private theorem compileWitness_op_iff [Field F] (w : Witness F) (op : Op γ F) :
    (∀ c ∈ compileOp op, R1CS.satisfiesLinComb (compileWitness w) c) ↔
      satisfiesOp w op := by
  cases op with
  | assign felt =>
      cases felt with
      | add | sub | mul | neg | const =>
          simp [compileOp, R1CS.satisfiesLinComb, R1CS.evalLinComb,
            compileWitness, satisfiesOp]
          constructor <;> intro h <;>
            simpa [sub_eq_add_neg] using h.symm
      | div dest left right =>
          simp only [compileOp, List.forall_mem_cons,
            R1CS.satisfiesLinComb, R1CS.evalLinComb, compileWitness,
            satisfiesOp, List.foldl, zero_add, one_mul]
          constructor
          · rintro ⟨hquotient, hinverse, _⟩
            have hnonzero : w right ≠ 0 := by
              intro hzero
              simp [hzero] at hinverse
            refine ⟨hnonzero, ?_⟩
            calc
              w dest = w left * (w right)⁻¹ := by
                have hmul : w dest * w right = w left := by
                  simpa [mul_comm] using hquotient
                simpa [div_eq_mul_inv] using (eq_div_iff hnonzero).2 hmul
              _ = _ := rfl
          · rintro ⟨hnonzero, hquotient⟩
            constructor
            · rw [hquotient]
              field_simp
            · constructor
              · field_simp
              · simp
      | inv dest source =>
          simp only [compileOp, List.forall_mem_cons,
            R1CS.satisfiesLinComb, R1CS.evalLinComb, compileWitness,
            satisfiesOp, List.foldl, zero_add, one_mul]
          constructor
          · rintro ⟨hmain, hsource, hdest, _⟩
            by_cases hzero : w source = 0
            · simp [hzero] at hmain hdest ⊢
              exact hdest
            · have hinverse : w source * (w source)⁻¹ = 1 := mul_inv_cancel₀ hzero
              rw [hinverse] at hmain
              ring_nf at hmain
              have hproduct : w dest * w source = 1 := by
                rw [mul_comm]
                exact hmain
              exact eq_inv_of_mul_eq_one_left hproduct
          · intro hdest
            constructor
            · simp [hdest]
            · constructor
              · by_cases hzero : w source = 0
                · simp [hzero]
                · rw [mul_inv_cancel₀ hzero]
                  ring
              · constructor
                · by_cases hzero : w source = 0
                  · rw [hdest, hzero, inv_zero]
                    simp
                  · rw [mul_inv_cancel₀ hzero]
                    ring
                · simp
  | assertEq left right =>
      simp [compileOp, R1CS.satisfiesLinComb, R1CS.evalLinComb,
        compileWitness, satisfiesOp]

private theorem compileWitness_constraints_iff [Field F] {γ : OpCtx}
    (w : Witness F) (body : List (Stmt Set γ F)) :
    (∀ c ∈ compileConstraints body,
      R1CS.satisfiesLinComb (compileWitness w) c) ↔ satisfies w body := by
  induction body with
  | nil => simp [compileConstraints, satisfies]
  | cons stmt rest ih =>
      rw [compileConstraints_cons]
      simp only [List.forall_mem_append]
      rw [compileWitness_op_iff, ih]
      simp [satisfies]

/-- Direct codec preserves and reflects terminal satisfaction for its exact
wire assignment. -/
theorem compileWitness_satisfies_iff [Field F] {γ : OpCtx}
    (w : Witness F) (body : List (Stmt Set γ F)) :
    R1CS.satisfies (compileWitness w) (toR1CS body) ↔
      satisfies w body := by
  simp only [R1CS.satisfies, compileWitness, toR1CS]
  exact (and_iff_right True.intro).trans (compileWitness_constraints_iff w body)

set_option linter.flexible false in
/-- A satisfying assignment to an operation's constraints satisfies its terminal
equation on ordinary wires, assuming the distinguished wire is one.

Proof sketch: normalize single-equation operations. Division's inverse constraint
forces a nonzero denominator. For inverse, split on zero input and derive the is-zero
wire before recovering the output equation; do not assume canonical auxiliary values. -/
private theorem op_reflection [Field F] (w : R1CS.Witness F) (op : Op γ F)
    (hone : w .varOne = 1)
    (h : ∀ c ∈ compileOp op, R1CS.satisfiesLinComb w c) :
    satisfiesOp (readback w) op := by
  cases op with
  | assign felt =>
      cases felt with
      | add | sub | mul | neg | const =>
          simp only [compileOp, List.forall_mem_cons, R1CS.satisfiesLinComb,
            R1CS.evalLinComb, List.foldl, readback, satisfiesOp] at *
          r1cs_arith
      | div dest left right =>
          simp [compileOp, R1CS.satisfiesLinComb, R1CS.evalLinComb, hone] at h
          have hn : w (.var right) ≠ 0 := by
            intro hz
            simp [hz] at h
          refine ⟨hn, ?_⟩
          change w (.var dest) = w (.var left) * (w (.var right))⁻¹
          simpa [div_eq_mul_inv] using (eq_div_iff hn).2
            (show w (.var dest) * w (.var right) = w (.var left) by
              simpa [mul_comm] using h.1)
      | inv dest source =>
          simp [compileOp, R1CS.satisfiesLinComb, R1CS.evalLinComb, hone] at h
          change w (.var dest) = (w (.var source))⁻¹
          by_cases hz : w (.var source) = 0
          · have hi : w (.auxIsZero source) = 1 := by
              have hm := h.1
              rw [hz] at hm
              linear_combination hm
            simpa [hz, hi] using h.2.2
          · have hi : w (.auxIsZero source) = 0 :=
              h.2.1.resolve_left hz
            apply eq_inv_of_mul_eq_one_left
            simpa [hi, mul_comm] using h.1
  | assertEq =>
      simpa [compileOp, R1CS.satisfiesLinComb, R1CS.evalLinComb,
        hone, satisfiesOp, readback] using h

/-- Every satisfying R1CS witness reads back to satisfying terminal locals, regardless
of whether it was constructed by `compileWitness`.

Proof sketch: extract the constant-one equation, split the concatenated constraints
by operation, apply `op_reflection`, and induct over the body. -/
theorem toR1CS_reflection [Field F] {γ : OpCtx}
    (body : List (Stmt Set γ F)) (w : R1CS.Witness F)
    (h : R1CS.satisfies w (toR1CS body)) :
    satisfies (readback w) body := by
  obtain ⟨hone, hall⟩ := h
  induction body with
  | nil => simp [satisfies]
  | cons stmt rest ih =>
      rw [show (toR1CS (stmt :: rest)).constraints =
        compileOp (stmtOp stmt) ++ compileConstraints rest from
          compileConstraints_cons stmt rest] at hall
      have hp := List.forall_mem_append.mp hall
      exact (List.forall_mem_cons).mpr
        ⟨op_reflection w (stmtOp stmt) hone hp.1, ih hp.2⟩

/-- Direct terminal backend retains existential preservation and reflection. -/
instance CorrectPass [Field F] : PresReflPass (Language F) (R1CS.Language F) where
  compile := compileProgram
  witnessRel _ source target := ∀ v, target (.var v) = source v
  preservation := by
    intro w program h
    refine ⟨compileWitness w, fun _ ↦ rfl, ?_⟩
    cases program with
    | mk body =>
        exact (compileWitness_satisfies_iff w body).mpr h
  reflection := by
    intro w program h
    refine ⟨readback w, fun _ ↦ rfl, ?_⟩
    cases program with
    | mk body => exact toR1CS_reflection body w h

/-- Constructive direct terminal-to-R1CS artifact. -/
def compilationArtifact [Field F] (source : Program F) :
    WitnessCodec.CompilationArtifact (Language F) (R1CS.Language F) source where
  target := compileProgram source
  forward w := .ok (compileWitness w)
  readback := readback
  witnessRel source target := ∀ v, target (.var v) = source v
  forward_rel := by
    intro w target h v
    have htarget : target = compileWitness w := Except.ok.inj h.symm
    subst target
    rfl
  satisfies_iff := by
    intro w target h
    have htarget : target = compileWitness w := Except.ok.inj h.symm
    subst target
    cases source with
    | mk body =>
        change satisfies w body ↔
          R1CS.satisfies (compileWitness w) (toR1CS body)
        exact (compileWitness_satisfies_iff w body).symm
  readback_forward := by
    intro w target h
    have htarget : target = compileWitness w := Except.ok.inj h.symm
    subst target
    exact readback_compileWitness w

/-- Terminal dialect exposes a total constructive backend transport. -/
def witnessTransportingPass [Field F] :
    WitnessCodec.WitnessTransportingPass (Language F) (R1CS.Language F) where
  compileArtifact source := .ok (compilationArtifact source)

/-- Encode canonical reserved parameters using the terminal dialect's constant
equations. These slots are inputs, so this is constraint enforcement, not execution. -/
def enforceZeroPrefix [Field F] (count : Nat) (system : R1CS.System F) : R1CS.System F :=
  { system with constraints :=
      (List.range count).flatMap (fun v ↦ compileOp (γ := ⟨0, 0, 0⟩) (.assign (.const v 0))) ++
        system.constraints }

/-- Rewriting a local with its existing value leaves the witness unchanged. -/
theorem writeWitness_self [Field F] [DecidableEq F] (w : Witness F) (v : LocalVar) :
    writeWitness w v (w v) = w := by
  funext x
  by_cases h : x = v
  · simp [writeWitness, h]
  · simp [writeWitness, h]

/-- Every satisfying assignment is a fixed point of one terminal operation.
Proof sketch: the operation equation identifies its assigned value with the
existing destination; division satisfaction also excludes its failure branch. -/
theorem materializeOp_of_satisfies [Field F] [DecidableEq F] (w : Witness F)
    (op : Op γ F) (h : satisfiesOp w op) : materializeOp w op = .ok w := by
  cases op with
  | assertEq a b => rfl
  | assign op =>
    cases op with
    | div d a b =>
      simp only [satisfiesOp] at h
      simp [materializeOp, h.1, ← h.2, writeWitness_self]
    | _ =>
      simp only [satisfiesOp] at h
      simp [materializeOp, ← h, writeWitness_self]

/-- A satisfying terminal witness is unchanged by whole-body materialization.
Proof sketch: split head/tail satisfaction and apply the operation fixed-point
lemma before the induction hypothesis. No provenance or SSA premise is needed. -/
theorem materializeBody_of_satisfies [Field F] [DecidableEq F]
    (body : List (Stmt Set γ F)) (w : Witness F) (h : satisfies w body) :
    materializeBody body w = .ok w := by
  induction body with
  | nil => rfl
  | cons stmt rest ih =>
    have hs := h stmt (by simp)
    have hr : satisfies w rest := fun s hm ↦ h s (by simp [hm])
    rw [materializeBody, materializeOp_of_satisfies w (stmtOp stmt) hs]
    exact ih hr

/-- Zero-prefix enforcement adds exactly the canonical initialization equations.
Proof sketch: expand list membership and the terminal constant encoding; each new
rank-one equation simplifies to `w (.var v) = 0`. Existing constraints are unchanged. -/
theorem satisfies_enforceZeroPrefix_iff [Field F] (count : Nat) (system : R1CS.System F)
    (w : R1CS.Witness F) :
    R1CS.satisfies w (enforceZeroPrefix count system) ↔
      R1CS.satisfies w system ∧ ∀ v < count, w (.var v) = 0 := by
  simp only [R1CS.satisfies, enforceZeroPrefix, List.forall_mem_append,
    List.forall_mem_flatMap]
  simp [compileOp, R1CS.satisfiesLinComb, R1CS.evalLinComb,
    eq_comm, and_left_comm, and_comm]

end Dialect.R1CSLike
