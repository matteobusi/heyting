/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Passes.Tactics

/-!
# FlatIR → R1CS Pass

Encodes a flat list of felt-arithmetic instructions as a Rank-1 Constraint System.
Proved correct as a `PresReflPass`: reflection gives CC~ (soundness) and preservation
gives completeness (no spurious constraints added).

## Encoding

Each FlatIR instruction maps to one or two R1CS constraints of the form `A · B = C`:

| Instruction | Constraints | Encoding |
|---|---|---|
| `assignAdd dest src1 src2` | 1 | `(src1 + src2) · 1 = dest` |
| `assignSub dest src1 src2` | 1 | `(src1 − src2) · 1 = dest` |
| `assignMul dest src1 src2` | 1 | `src1 · src2 = dest` |
| `assignDiv dest src1 src2` | 2 | `src2 · dest = src1` ; `src2 · aux(src2) = 1` |
| `assignNeg dest src` | 1 | `src · (−1) = dest` |
| `assignConst dest c` | 1 | `c · 1 = dest` |
| `assertEq src1 src2` | 1 | `src1 · 1 = src2` |

`assignDiv` needs two constraints: the first encodes the quotient, and the second
witnesses invertibility by requiring an auxiliary variable `aux(src2)` with
`src2 · aux(src2) = 1` (forcing `src2 ≠ 0`).

## Witness translation

- **Forward** (`compileWitness`): FlatIR witness `w` → R1CS witness with
  `varOne = 1`, `var v = w v`, `aux v = (w v)⁻¹`.
- **Backward** (`extractWitness`): R1CS witness `w` → FlatIR witness `fun v => w (.var v)`.

## Witness relation

```
witnessRel _p ws wt := ∀ v, wt (.var v) = ws v
```

Program-independent: the R1CS witness must embed the FlatIR witness at all `.var` slots.
-/

namespace FlatIRToR1CS

variable (F : Type) [Field F]

/-! ## Variable compilation -/

/-- Embed a FlatIR variable ID into the R1CS `.var` constructor. -/
def compileVar (v : FlatIR.VarId) : R1CS.VarId := .var v

/-! ## Instruction encoding -/

/-- Compile a single FlatIR instruction to a list of R1CS constraints. -/
def compileInstr (instr : FlatIR.Instr F) : List (R1CS.Constraint F) :=
  match instr with
  | .assignAdd dest src1 src2 =>
      -- (src1 + src2) * 1 = dest
      [{
        A := [(compileVar src1, 1), (compileVar src2, 1)],
        B := [(.varOne, 1)],
        C := [(compileVar dest, 1)]
      }]
  | .assignSub dest src1 src2 =>
      -- (src1 - src2) * 1 = dest
      [{
        A := [(compileVar src1, 1), (compileVar src2, -1)],
        B := [(.varOne, 1)],
        C := [(compileVar dest, 1)]
      }]
  | .assignMul dest src1 src2 =>
      -- src1 * src2 = dest
      [{
        A := [(compileVar src1, 1)],
        B := [(compileVar src2, 1)],
        C := [(compileVar dest, 1)]
      }]
  | .assignDiv dest src1 src2 =>
      -- Two constraints to encode dest = src1 * src2⁻¹ with src2 ≠ 0:
      -- (1) src2 * dest = src1
      -- (2) src2 * aux(src2) = 1  (forces src2 to be invertible)
      [
        {
          A := [(compileVar src2, 1)],
          B := [(compileVar dest, 1)],
          C := [(compileVar src1, 1)]
        },
        {
          A := [(compileVar src2, 1)],
          B := [(.aux src2, 1)],
          C := [(.varOne, 1)]
        }
      ]
  | .assignNeg dest src =>
      -- src * (-1) = dest
      [{
        A := [(compileVar src, 1)],
        B := [(.varOne, -1)],
        C := [(compileVar dest, 1)]
      }]
  | .assignConst dest c =>
      -- c * 1 = dest
      [{
        A := [(.varOne, c)],
        B := [(.varOne, 1)],
        C := [(compileVar dest, 1)]
      }]
  | .assertEq src1 src2 =>
      -- src1 * 1 = src2
      [{
        A := [(compileVar src1, 1)],
        B := [(.varOne, 1)],
        C := [(compileVar src2, 1)]
      }]

/-! ## Program compilation -/

/-- Compile a full FlatIR program to an R1CS system by flat-mapping each
    instruction's constraint encoding.  `numPublicInputs` is forwarded verbatim
    from the source module's main struct member count. -/
def compileProgram (s : FlatIR.Program F) (numPublicInputs : Nat := 0) : R1CS.System F :=
  { constraints := s.flatMap (compileInstr F), numPublicInputs }

/-! ## Witness translation -/

/-- Forward witness: extend a FlatIR witness to an R1CS witness.
    Sets `varOne = 1`, preserves FlatIR variable values, and provides
    auxiliary inverse witnesses needed by the `assignDiv` encoding. -/
def compileWitness (w : FlatIR.Witness F) : R1CS.Witness F :=
  fun | (.varOne) => 1
      | (.var v)  => w v
      | (.aux v)  => (w v)⁻¹

/-- Backward witness: project an R1CS witness down to a FlatIR witness
    by reading out the `.var` slots. -/
def extractWitness (w : R1CS.Witness F) : FlatIR.Witness F :=
  fun v => w (.var v)

/-! ## Correctness instance -/

instance CorrectPass : PresReflPass (FlatIR.Language F) (R1CS.Language F) where
  compile := compileProgram F
  witnessRel _p ws wt := ∀ v, wt (.var v) = ws v

  preservation := by
    intro w p h
    simp only [FlatIR.Language, R1CS.Language, R1CS.satisfies] at *
    exists (compileWitness (F:=F) w)
    constructor
    · intro; simp only [compileWitness]
    · constructor
      · simp [compileWitness]
      · intro c hc
        simp only [compileProgram, List.mem_flatMap] at hc
        obtain ⟨instr, hinstr, hc_mem⟩ := hc
        have h_instr := h instr hinstr
        cases instr with
        | assignAdd dest src1 src2 =>
          simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
          simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
          r1cs_arith
        | assignSub dest src1 src2 =>
          simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
          simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
          r1cs_arith
        | assignMul dest src1 src2 =>
          simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
          simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
          r1cs_arith
        | assignDiv dest src1 src2 =>
          simp only [compileInstr, List.mem_cons, List.mem_nil_iff,
                or_false] at hc_mem
          obtain ⟨h_nz, h_eq⟩ := h_instr
          rcases hc_mem with rfl | rfl
          · simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                  compileWitness, List.foldl]
            rw [h_eq]; field_simp
            simp_all only [ne_eq, zero_add, zero_mul]
          · simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                  compileWitness, List.foldl]
            field_simp
            simp_all only [ne_eq, zero_add, zero_mul, mul_one]
        | assignNeg dest src =>
          simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
          simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
          r1cs_arith
        | assignConst dest c =>
          simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
          simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
          r1cs_arith
        | assertEq src1 src2 =>
          simp only [compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
          simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
                compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
          r1cs_arith

  reflection := by
    intro w p h
    exists (extractWitness (F:=F) w)
    simp only [R1CS.Language, R1CS.satisfies] at h
    obtain ⟨h_one, h_constrs⟩ := h
    simp only [FlatIR.Language, FlatIR.satisfies] at *
    constructor
    · intro v; rfl
    · intro instr hinstr
      -- Gather all R1CS constraints emitted by this instruction
      have h_all : ∀ c ∈ compileInstr F instr,
          R1CS.satisfiesLinComb w c := by
        intro c hc
        apply h_constrs
        simp only [compileProgram, List.mem_flatMap]
        exact ⟨instr, hinstr, hc⟩
      cases instr with
      | assignAdd dest src1 src2 =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
              extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
        r1cs_arith
      | assignSub dest src1 src2 =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
              extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
        r1cs_arith
      | assignMul dest src1 src2 =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
              extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
        r1cs_arith
      | assignDiv dest src1 src2 =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        obtain ⟨h_c1, h_c2, _⟩ := h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
          FlatIR.satisfiesInstr, List.foldl] at h_c1 h_c2 ⊢
        simp only [one_mul, zero_add, extractWitness] at h_c1 h_c2 ⊢
        constructor
        · intro h_zero
          rw [h_zero] at h_c2
          simp at h_c2
          simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, one_mul, zero_ne_one]
        · have h_nz : w (R1CS.VarId.var src2) ≠ 0 := by
            intro h_zero
            rw [h_zero] at h_c2
            simp at h_c2
            aesop
          field_simp at h_c1 ⊢
          exact h_c1
      | assignNeg dest src =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
              extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
        r1cs_arith
      | assignConst dest c =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
              extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
        r1cs_arith
      | assertEq src1 src2 =>
        simp only [compileInstr, List.forall_mem_cons] at h_all
        simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, compileVar,
              extractWitness, FlatIR.satisfiesInstr, List.foldl] at *
        r1cs_arith

end FlatIRToR1CS
