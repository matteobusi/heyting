import Heyting.Core.Language

namespace FlatIR
  variable (F : Type) [Field F]
  abbrev VarId := Nat

  inductive Instr (F : Type) where
    | assignAdd (dest : VarId) (src1 src2 : VarId)
    | assignSub (dest : VarId) (src1 src2 : VarId)
    | assignMul (dest : VarId) (src1 src2 : VarId)
    | assignDiv (dest : VarId) (src1 src2 : VarId)
    | assignNeg (dest : VarId) (src : VarId)
    | assignConst (dest : VarId) (c : F)
    | assertEq (src1 src2 : VarId)
    deriving Repr

  abbrev Program (F : Type) := List (Instr F)

  abbrev Witness (F : Type) := VarId → F

  def satisfiesInstr {F : Type} [Field F] (w : Witness F) (instr : Instr F) : Prop :=
    match instr with
    | .assignAdd dest src1 src2 => w dest = w src1 + w src2
    | .assignSub dest src1 src2 => w dest = w src1 - w src2
    | .assignMul dest src1 src2 => w dest = w src1 * w src2
    | .assignDiv dest src1 src2 => w src2 ≠ 0 ∧ w dest = w src1 * (w src2)⁻¹
    | .assignNeg dest src       => w dest = -(w src)
    | .assignConst dest c       => w dest = c
    | .assertEq src1 src2       => w src1 = w src2

  -- Variables referenced by an instruction
  def instrVars {F : Type} (instr : Instr F) : List VarId :=
    match instr with
    | .assignAdd dest src1 src2 => [dest, src1, src2]
    | .assignSub dest src1 src2 => [dest, src1, src2]
    | .assignMul dest src1 src2 => [dest, src1, src2]
    | .assignDiv dest src1 src2 => [dest, src1, src2]
    | .assignNeg dest src       => [dest, src]
    | .assignConst dest _       => [dest]
    | .assertEq src1 src2       => [src1, src2]

  -- If two witnesses agree on all variables of an instruction, satisfaction transfers
  theorem satisfiesInstr_congr {F : Type} [Field F] {w1 w2 : Witness F}
      {instr : Instr F}
      (h : ∀ v ∈ instrVars instr, w1 v = w2 v) :
      satisfiesInstr w1 instr ↔ satisfiesInstr w2 instr := by
    cases instr with
    | assignAdd dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignSub dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignMul dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignDiv dest src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src1 (by tauto), h src2 (by tauto)]
    | assignNeg dest src =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h dest (by tauto), h src (by tauto)]
    | assignConst dest c =>
      simp only [instrVars, List.mem_singleton] at h
      simp only [satisfiesInstr, h dest (by tauto)]
    | assertEq src1 src2 =>
      simp only [instrVars, List.mem_cons] at h
      simp only [satisfiesInstr,
        h src1 (by tauto), h src2 (by tauto)]

  def satisfies {F : Type} [Field F] (w : Witness F) (prog : Program F) : Prop :=
    ∀ instr ∈ prog, satisfiesInstr w instr

  instance Language (F : Type) [Field F] : Language VarId F where
    Program := Program F
    satisfies := satisfies
end FlatIR
