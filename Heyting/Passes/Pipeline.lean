import Heyting.Core.Pass
import Heyting.Core.ComputingLanguage
import Heyting.Languages.StructIR
import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRToR1CS

/-!
# End-to-End Pipeline: StructIR → R1CS

Composes `StructIRToFlatIR` and `FlatIRToR1CS` into a single, top-level
`PresReflPass` from `StructIR.Language` to `R1CS.Language`.

## Correctness

Preservation and reflection follow immediately by chaining the two
sub-pass instances:

- **Preservation**: StructIR sat → (by `StructIRToFlatIR.preservation`) FlatIR sat →
  (by `FlatIRToR1CS.preservation`) R1CS sat.
- **Reflection**: R1CS sat → (by `FlatIRToR1CS.reflection`) FlatIR sat →
  (by `StructIRToFlatIR.reflection`) StructIR sat.

## Witness chain

```
ws : StructIR.Witness F
  --[compileWitnessFlat]-->  wf : FlatIR.Witness F
  --[FlatIRToR1CS.compileWitness]-->  wr : R1CS.Witness F
```

`compileWitnessFlat` is a top-level wrapper around `StructIRToFlatIR.compileWitness`
that supplies the same initial state used in the `preservation` proof.

## End-to-end witness correctness

`compileWitnessCorrect` states that the concrete witness `compileWitness m ws` satisfies
`compileProgram m` whenever `ws` satisfies `m`. This is a corollary of the two
preservation theorems, proved by constructing the witness explicitly (bypassing the
existential in `PresReflPass.preservation`).

## End-to-end witness generation

`pipelineWitness` chains `StructIR.computeWitness` with the two forward witness
translations to produce an `R1CS.Witness F` directly from public inputs.
-/

namespace Pipeline

variable {n : Nat} {F : Type} [Field F]

/-! ## Program compilation -/

/-- Compile a StructIR module straight to an R1CS system by composing the two passes.
    The public-input count is derived from the main struct's `{llzk.pub}` members. -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  { (FlatIRToR1CS.compileProgram F (StructIRToFlatIR.compileProgram m)) with
    numPublicInputs := numPub }

/-! ## Witness translation -/

/-- Forward witness (StructIR → FlatIR): top-level wrapper around
    `StructIRToFlatIR.compileWitness` with the canonical initial state
    used by the `preservation` proof. -/
def compileWitnessFlat (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    FlatIR.Witness F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef  := m.structs mainIdx
  let initVarMap : StructIRToFlatIR.VarMap := fun v =>
    if v < mainDef.constrain.numParams then v else 0
  let initNext   := max mainDef.constrain.numParams 1
  let initEnv    : StructIR.LocalEnv F := fun _ => 0
  let initObjEnv : StructIR.ObjEnv    := StructIR.ObjEnv.update (fun _ => []) 0 []
  let initAcc    : FlatIR.VarId → F   := fun _ => 0
  (StructIRToFlatIR.compileWitness m ws mainIdx initVarMap initNext
    initEnv initObjEnv mainDef.constrain.body initAcc).1

/-- Forward witness (StructIR → R1CS): compose the two forward translations. -/
def compileWitness (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    R1CS.Witness F :=
  FlatIRToR1CS.compileWitness F (compileWitnessFlat m ws)

/-- Backward witness (R1CS → StructIR): compose the two backward translations. -/
def extractWitness (m : StructIR.Module (n + 1) F) (wr : R1CS.Witness F) :
    StructIR.Witness F :=
  StructIRToFlatIR.extractWitness m (FlatIRToR1CS.extractWitness F wr)

/-! ## Composed `witnessRel` -/

/-- The composed witness relation: there exists an intermediate FlatIR witness
    related to `ws` by the first pass and to `wr` by the second pass. -/
def witnessRel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (wr : R1CS.Witness F) : Prop :=
  ∃ wf : FlatIR.Witness F,
    (StructIRToFlatIR.CorrectPass n F).witnessRel m ws wf ∧
    (FlatIRToR1CS.CorrectPass F).witnessRel (StructIRToFlatIR.compileProgram m) wf wr

/-! ## Composed `PresReflPass` instance -/

/-- `PresReflPass` instance for the full StructIR → R1CS pipeline.
    Preservation and reflection follow by composing the two sub-passes. -/
instance CorrectPass (n : Nat) (F : Type) [Field F] :
    PresReflPass (StructIR.Language n F) (R1CS.Language F) where
  compile    := compileProgram
  witnessRel := witnessRel

  preservation := by
    intro ws p hsat
    -- Lift StructIR witness to FlatIR.
    obtain ⟨wf, hrel1, hsat_f⟩ :=
      (StructIRToFlatIR.CorrectPass n F).preservation ws p hsat
    -- Lift FlatIR witness to R1CS.
    obtain ⟨wr, hrel2, hsat_r⟩ :=
      (FlatIRToR1CS.CorrectPass F).preservation wf
        (StructIRToFlatIR.compileProgram p) hsat_f
    exact ⟨wr, ⟨wf, hrel1, hrel2⟩, hsat_r⟩

  reflection := by
    intro wr p hsat
    -- Pull R1CS witness back to FlatIR.
    obtain ⟨wf, hrel2, hsat_f⟩ :=
      (FlatIRToR1CS.CorrectPass F).reflection wr
        (StructIRToFlatIR.compileProgram p) hsat
    -- Pull FlatIR witness back to StructIR.
    obtain ⟨ws, hrel1, hsat_s⟩ :=
      (StructIRToFlatIR.CorrectPass n F).reflection wf p hsat_f
    exact ⟨ws, ⟨wf, hrel1, hrel2⟩, hsat_s⟩

/-! ## End-to-end witness correctness -/

/-- If `ws` satisfies the StructIR module `m`, then the concretely constructed
    R1CS witness `compileWitness m ws` satisfies the compiled R1CS system
    `compileProgram m`.

    This is a corollary of the two preservation theorems, proved without using
    the existential `PresReflPass.preservation` so that the specific witness is
    named explicitly.

    **Proof outline:**
    1. Establish FlatIR satisfaction of `compileWitnessFlat m ws` by replicating
       the `StructIRToFlatIR.preservation` argument (using `preservation_body` and
       `compileWitness_preserves_below`).
    2. Establish R1CS satisfaction of `compileWitness m ws` by inlining the
       `FlatIRToR1CS.preservation` argument (per-instruction case split). -/
theorem compileWitnessCorrect (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F)
    (hsat : StructIR.satisfies ws m) :
    R1CS.satisfies (compileWitness m ws) (compileProgram m) := by
  -- Unfold StructIR satisfaction
  simp only [StructIR.satisfies] at hsat
  -- Set up the canonical initial state (mirrors StructIRToFlatIR.preservation)
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef  := m.structs mainIdx
  let initVarMap : StructIRToFlatIR.VarMap := fun v =>
    if v < mainDef.constrain.numParams then v else 0
  let initNext   := max mainDef.constrain.numParams 1
  let initEnv    : StructIR.LocalEnv F := fun _ => 0
  let initObjEnv : StructIR.ObjEnv    := StructIR.ObjEnv.update (fun _ => []) 0 []
  let initAcc    : FlatIR.VarId → F   := fun _ => 0
  have hpoz : 0 < initNext :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  -- Step 1: prove FlatIR satisfaction of compileWitnessFlat m ws
  have hsat_f : FlatIR.satisfies (compileWitnessFlat m ws) (StructIRToFlatIR.compileProgram m) := by
    simp only [FlatIR.satisfies, StructIRToFlatIR.compileProgram]
    have hcoh : StructIRToFlatIR.WitnessCoherent initAcc initVarMap initEnv :=
      fun v => by simp [initAcc, initEnv]
    have hbound : StructIRToFlatIR.VarMapBound initVarMap initNext := by
      intro v; simp only [initVarMap, initNext]
      split
      case isTrue h  => exact Nat.lt_of_lt_of_le h (le_max_left _ _)
      case isFalse   => exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hacc_zero : initAcc 0 = 0 := rfl
    intro instr hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem_zero | hmem_body
    · -- Zero-initialization constraints: compileWitnessFlat m ws v = 0 for v < initNext
      simp only [List.mem_map, List.mem_range] at hmem_zero
      obtain ⟨v, hv, rfl⟩ := hmem_zero
      simp only [FlatIR.satisfiesInstr]
      change (StructIRToFlatIR.compileWitness m ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc).1 v = 0
      exact StructIRToFlatIR.compileWitness_preserves_below m ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc v hv
    · -- Body constraints via preservation_body
      change FlatIR.satisfiesInstr (StructIRToFlatIR.compileWitness m ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc).1 instr
      exact StructIRToFlatIR.preservation_body m ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc
        hcoh hbound hpoz hacc_zero hsat instr hmem_body
  -- Step 2: prove R1CS satisfaction of compileWitness m ws
  -- = FlatIRToR1CS.compileWitness (compileWitnessFlat m ws)
  simp only [R1CS.satisfies, compileProgram, FlatIRToR1CS.compileProgram]
  constructor
  · -- varOne slot = 1
    simp [compileWitness, FlatIRToR1CS.compileWitness]
  · -- Each R1CS constraint is satisfied
    intro c hc
    simp only [List.mem_flatMap] at hc
    obtain ⟨instr, hinstr, hc_mem⟩ := hc
    have h_instr := hsat_f instr hinstr
    -- compileWitness m ws = FlatIRToR1CS.compileWitness (compileWitnessFlat m ws)
    change R1CS.satisfiesLinComb (compileWitness m ws) c
    simp only [compileWitness]
    cases instr with
    | assignAdd dest src1 src2 =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
      simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
            FlatIRToR1CS.compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
      r1cs_arith
    | assignSub dest src1 src2 =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
      simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
            FlatIRToR1CS.compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
      r1cs_arith
    | assignMul dest src1 src2 =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
      simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
            FlatIRToR1CS.compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
      r1cs_arith
    | assignDiv dest src1 src2 =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_cons, List.mem_nil_iff,
            or_false] at hc_mem
      obtain ⟨h_nz, h_eq⟩ := h_instr
      rcases hc_mem with rfl | rfl
      · simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
              FlatIRToR1CS.compileWitness, List.foldl]
        rw [h_eq]; field_simp
        simp_all only [ne_eq, zero_add, zero_mul]
      · simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
              FlatIRToR1CS.compileWitness, List.foldl]
        field_simp
        simp_all only [ne_eq, zero_add, zero_mul, mul_one]
    | assignNeg dest src =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
      simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
            FlatIRToR1CS.compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
      r1cs_arith
    | assignConst dest c =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
      simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
            FlatIRToR1CS.compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
      r1cs_arith
    | assertEq src1 src2 =>
      simp only [FlatIRToR1CS.compileInstr, List.mem_singleton] at hc_mem; subst hc_mem
      simp only [R1CS.satisfiesLinComb, R1CS.evalLinComb, FlatIRToR1CS.compileVar,
            FlatIRToR1CS.compileWitness, FlatIR.satisfiesInstr, List.foldl] at *
      r1cs_arith

/-! ## End-to-end witness generation -/

/-- Attempt to produce an R1CS witness directly from a StructIR module and
    public inputs by chaining the compute interpreter with the two forward
    witness translations.  Returns `none` if the interpreter encounters a
    runtime fault (e.g. division by zero). -/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map (compileWitness m)

end Pipeline
