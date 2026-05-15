import Heyting.Core.CheckedSemantics
import Heyting.Core.Pass
import Heyting.Core.VarIdEncoding
import Heyting.Languages.FlatIRSubst
import Heyting.Languages.StructIR
import Heyting.Languages.StructIRSubst
import Heyting.Passes.StructIRToFlatIRDirect

/-!
# StructIR -> FlatIR Direct Simulation Helpers

Phase-5 helper lemmas for checked-semantics simulation.

This file relates:
- source checked atoms (`StructIRSubst.checkAtom`), and
- target checked atoms after concretization (`FlatIRSubst.checkAtom`).

The proved alignment is at list-of-atoms level and gives first-failure alignment
through `CheckedSemantics.ResultRel`.
-/
namespace StructIRToFlatIRDirectSim

open CheckedSemantics
open SubstSemantics

variable {F : Type} [Field F]

abbrev Atom (F : Type) := CAtom F

/-- Concretize a symbolic value term by interpreting it under the source witness. -/
def concretizeVTerm (w : StructIR.Witness F) (t : VTerm F) : VTerm F :=
  .const (VTerm.interp w StructIRSubst.defaultValuation StructIRSubst.defaultPathValuation t)

/-- Concretize an atom by concretizing all value-term payloads. -/
def concretizeAtom (w : StructIR.Witness F) : Atom F → Atom F
  | .eq lhs rhs => .eq (concretizeVTerm w lhs) (concretizeVTerm w rhs)
  | .neZero t => .neZero (concretizeVTerm w t)

/-- Source-side checked evaluation over a list of atoms. -/
def evalAtomsCheckedStruct [DecidableEq F] (w : StructIR.Witness F) (atoms : List (Atom F)) :
    Result (Atom F) :=
  match atoms with
  | [] => Result.success []
  | a :: rest =>
    if StructIRSubst.checkAtom w a then
      match evalAtomsCheckedStruct w rest with
      | Result.success trace => Result.success (a :: trace)
      | Result.failure checkedPrefix failed => Result.failure (a :: checkedPrefix) failed
    else
      Result.failure [] a

/-- Target-side checked evaluation on concretized atoms. -/
def evalAtomsCheckedFlat [DecidableEq F] (w : StructIR.Witness F) (atoms : List (Atom F)) :
    Result (Atom F) :=
  FlatIRSubst.evalAtomsChecked (F := F) (fun _ => 0) (atoms.map (concretizeAtom w))

/-- Pointwise relation between source and concretized target atoms. -/
def stepRel (w : StructIR.Witness F) (aSrc aTgt : Atom F) : Prop :=
  aTgt = concretizeAtom w aSrc

/-- Trace relation: target trace is the mapped concretization of source trace. -/
def traceRel (w : StructIR.Witness F) (srcTrace tgtTrace : List (Atom F)) : Prop :=
  tgtTrace = srcTrace.map (concretizeAtom w)

/-- Map a source checked result to the concretized target checked result shape. -/
def concretizeResult (w : StructIR.Witness F) : Result (Atom F) → Result (Atom F)
  | .success trace => .success (trace.map (concretizeAtom w))
  | .failure checkedPrefix failed =>
      .failure (checkedPrefix.map (concretizeAtom w)) (concretizeAtom w failed)

theorem checkAtom_concretize_eq [DecidableEq F]
    (w : StructIR.Witness F) (a : Atom F) :
    FlatIRSubst.checkAtom (F := F) (fun _ => 0) (concretizeAtom w a) =
      StructIRSubst.checkAtom w a := by
  cases a with
  | eq lhs rhs =>
    simp [FlatIRSubst.checkAtom, StructIRSubst.checkAtom, concretizeAtom, concretizeVTerm,
      VTerm.interp]
  | neZero t =>
    simp [FlatIRSubst.checkAtom, StructIRSubst.checkAtom, concretizeAtom, concretizeVTerm,
      VTerm.interp]

theorem checkAtom_concretize_eq_with [DecidableEq F]
    (wSrc : StructIR.Witness F) (wTgt : FlatIR.Witness F) (a : Atom F) :
    FlatIRSubst.checkAtom (F := F) wTgt (concretizeAtom wSrc a) =
      StructIRSubst.checkAtom wSrc a := by
  cases a with
  | eq lhs rhs =>
    simp [FlatIRSubst.checkAtom, StructIRSubst.checkAtom, concretizeAtom, concretizeVTerm,
      VTerm.interp]
  | neZero t =>
    simp [FlatIRSubst.checkAtom, StructIRSubst.checkAtom, concretizeAtom, concretizeVTerm,
      VTerm.interp]

theorem evalAtomsChecked_concretize_eq_with [DecidableEq F]
    (wSrc : StructIR.Witness F) (wTgt : FlatIR.Witness F) (atoms : List (Atom F)) :
    FlatIRSubst.evalAtomsChecked wTgt (atoms.map (concretizeAtom wSrc)) =
      concretizeResult wSrc (evalAtomsCheckedStruct wSrc atoms) := by
  induction atoms with
  | nil =>
    simp [FlatIRSubst.evalAtomsChecked, evalAtomsCheckedStruct, concretizeResult]
  | cons a rest ih =>
    by_cases h : StructIRSubst.checkAtom wSrc a
    · have hflat : FlatIRSubst.checkAtom (F := F) wTgt (concretizeAtom wSrc a) = true := by
        simpa [checkAtom_concretize_eq_with] using h
      simp only [FlatIRSubst.evalAtomsChecked, evalAtomsCheckedStruct, h, hflat, List.map]
      rw [ih]
      cases hrest : evalAtomsCheckedStruct wSrc rest <;> simp [concretizeResult]
    · have hflat : FlatIRSubst.checkAtom (F := F) wTgt (concretizeAtom wSrc a) = false := by
        simpa [checkAtom_concretize_eq_with] using h
      simp [FlatIRSubst.evalAtomsChecked, evalAtomsCheckedStruct, h, hflat, concretizeResult]

theorem evalAtomsChecked_concretize_eq [DecidableEq F]
    (w : StructIR.Witness F) (atoms : List (Atom F)) :
    evalAtomsCheckedFlat w atoms = concretizeResult w (evalAtomsCheckedStruct w atoms) := by
  simpa [evalAtomsCheckedFlat] using evalAtomsChecked_concretize_eq_with w (fun _ => 0) atoms

theorem resultRel_concretizeResult (w : StructIR.Witness F) (r : Result (Atom F)) :
    ResultRel (traceRel w) (stepRel w) r (concretizeResult w r) := by
  cases r with
  | success trace =>
    simp [ResultRel, traceRel, concretizeResult]
  | failure checkedPrefix failed =>
    simp [ResultRel, traceRel, stepRel, concretizeResult]

/-- First-failure alignment at atom-list level via `ResultRel`. -/
theorem evalAtomsChecked_firstFailure_alignment [DecidableEq F]
    (w : StructIR.Witness F) (atoms : List (Atom F)) :
    ResultRel (traceRel w) (stepRel w)
      (evalAtomsCheckedStruct w atoms)
      (evalAtomsCheckedFlat w atoms) := by
  rw [evalAtomsChecked_concretize_eq]
  exact resultRel_concretizeResult w (evalAtomsCheckedStruct w atoms)

/-- Reflection-style counterpart at atom-list level: target success implies source success. -/
theorem evalAtomsChecked_reflect_success [DecidableEq F]
    (w : StructIR.Witness F) (atoms : List (Atom F)) :
    (∃ tgtTrace, evalAtomsCheckedFlat w atoms = Result.success tgtTrace) →
      ∃ srcTrace, evalAtomsCheckedStruct w atoms = Result.success srcTrace := by
  intro hSucc
  rw [evalAtomsChecked_concretize_eq] at hSucc
  cases hSrc : evalAtomsCheckedStruct w atoms with
  | success srcTrace =>
    exact ⟨srcTrace, by simp⟩
  | failure checkedPrefix failed =>
    simp [concretizeResult, hSrc] at hSucc

/-- Preservation-style direction at atom-list level: source success implies target success. -/
theorem evalAtomsChecked_preserve_success [DecidableEq F]
    (w : StructIR.Witness F) (atoms : List (Atom F)) :
    (∃ srcTrace, evalAtomsCheckedStruct w atoms = Result.success srcTrace) →
      ∃ tgtTrace, evalAtomsCheckedFlat w atoms = Result.success tgtTrace := by
  intro hSucc
  rw [evalAtomsChecked_concretize_eq]
  rcases hSucc with ⟨srcTrace, hSrc⟩
  refine ⟨srcTrace.map (concretizeAtom w), ?_⟩
  simp [concretizeResult, hSrc]

theorem evalAtomsChecked_success_iff [DecidableEq F]
    (w : StructIR.Witness F) (atoms : List (Atom F)) :
    (∃ srcTrace, evalAtomsCheckedStruct w atoms = Result.success srcTrace) ↔
      (∃ tgtTrace, evalAtomsCheckedFlat w atoms = Result.success tgtTrace) := by
  constructor
  · exact evalAtomsChecked_preserve_success w atoms
  · exact evalAtomsChecked_reflect_success w atoms

/-- Struct witness projected to FlatIR witness via `VarIdEncoding.decode`. -/
def liftStructWitness (w : StructIR.Witness F) : FlatIR.Witness F :=
  fun v => w (VarIdEncoding.decode v)

/-- Target checked result for a compiled constrain body. -/
def evalCompiledBodyChecked [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    CheckedSemantics.Result (Atom F) :=
  FlatIRSubst.evalAtomsChecked (liftStructWitness w)
    (FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
      (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh stmts).1)

/-- Source checked result for a constrain body under substitution semantics. -/
def evalSourceBodyChecked [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (σv : StructIRSubst.ValSubst F) (σo : StructIRSubst.PathSubst)
    (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    CheckedSemantics.Result (Atom F) :=
  (StructIRSubst.evalConstrainBodyChecked m w i σv σo nextFresh stmts).res

/--
Lifting lemma: once body-level atom correspondence is provided, first-failure
alignment follows from the atom-list simulation theorem.
-/
theorem compiledBody_firstFailure_of_atoms
    [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (atoms : List (Atom F))
    (hProgAtoms :
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh stmts).1 =
      atoms.map (concretizeAtom w)) :
    ResultRel (traceRel w) (stepRel w)
      (evalAtomsCheckedStruct w atoms)
      (evalCompiledBodyChecked w m i objEnv nextFresh stmts) := by
  simp only [evalCompiledBodyChecked]
  rw [hProgAtoms]
  have hEq := evalAtomsChecked_concretize_eq_with w (liftStructWitness w) atoms
  rw [hEq]
  exact resultRel_concretizeResult w (evalAtomsCheckedStruct w atoms)

/--
Lifting lemma: with body-level atom correspondence, success reflection and
preservation both reduce to atom-list simulation.
-/
theorem compiledBody_success_iff_of_atoms
    [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length))
    (atoms : List (Atom F))
    (hProgAtoms :
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh stmts).1 =
      atoms.map (concretizeAtom w)) :
    (∃ srcTrace, evalAtomsCheckedStruct w atoms = Result.success srcTrace) ↔
      (∃ tgtTrace, evalCompiledBodyChecked w m i objEnv nextFresh stmts =
        Result.success tgtTrace) := by
  simp only [evalCompiledBodyChecked]
  rw [hProgAtoms]
  have hEq := evalAtomsChecked_concretize_eq_with w (liftStructWitness w) atoms
  rw [hEq]
  constructor
  · intro hSucc
    rcases hSucc with ⟨srcTrace, hSrc⟩
    refine ⟨srcTrace.map (concretizeAtom w), ?_⟩
    simp [concretizeResult, hSrc]
  · intro hSucc
    cases hSrc : evalAtomsCheckedStruct w atoms with
    | success srcTrace =>
      exact ⟨srcTrace, by simp⟩
    | failure checkedPrefix failed =>
      simp [concretizeResult, hSrc] at hSucc

omit [Field F] in
theorem programAtoms_append (w : FlatIR.Witness F)
    (p1 p2 : FlatIR.Program F) :
    FlatIRSubst.programAtoms (F := F) w (p1 ++ p2) =
      FlatIRSubst.programAtoms (F := F) w p1 ++ FlatIRSubst.programAtoms (F := F) w p2 := by
  induction p1 with
  | nil => simp [FlatIRSubst.programAtoms]
  | cons instr rest ih =>
    simp [FlatIRSubst.programAtoms, List.cons_append, List.append_assoc]

theorem compileConstrainBody_readMember_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.readMember dest self member :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assertEq dest
          (StructIRToFlatIRDirect.encodeWitnessVar (objEnv self) member.val)) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i
          (StructIR.ObjEnv.update objEnv dest ((objEnv self) ++ [member.val]))
          nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody,
    FlatIRSubst.programAtoms]

theorem compileConstrainBody_constrainEq_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.constrainEq src1 src2 :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assertEq src1 src2) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody,
    FlatIRSubst.programAtoms]

theorem compileConstrainBody_feltAdd_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.feltAdd dest src1 src2 :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assignAdd dest src1 src2) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, FlatIRSubst.programAtoms]

theorem compileConstrainBody_feltSub_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.feltSub dest src1 src2 :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assignSub dest src1 src2) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, FlatIRSubst.programAtoms]

theorem compileConstrainBody_feltMul_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.feltMul dest src1 src2 :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assignMul dest src1 src2) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, FlatIRSubst.programAtoms]

theorem compileConstrainBody_feltDiv_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.feltDiv dest src1 src2 :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assignDiv dest src1 src2) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, FlatIRSubst.programAtoms]

theorem compileConstrainBody_feltNeg_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.feltNeg dest src :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assignNeg dest src) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, FlatIRSubst.programAtoms]

theorem compileConstrainBody_feltConst_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest : Nat) (c : F)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.feltConst dest c :: rest)).1
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.atomsOfInstr (F := F) (FlatIRSubst.initValSubst (F := F) (liftStructWitness w))
        (FlatIR.Instr.assignConst dest c) ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, FlatIRSubst.programAtoms]

theorem compileConstrainBody_call_programAtoms
    (w : StructIR.Witness F) (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    let p := (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh
      (.call target args :: rest)).1
    let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
    let calleeBody := (m.structs j).constrain.body
    let ρ : Nat → Nat := StructIRSubst.freshMap nextFresh
    let (freshBody, nextFresh') := StructIRSubst.freshenBody nextFresh calleeBody
    let paramBinds :=
      StructIRToFlatIRDirect.compileParamBindings (F := F) (m.structs j).constrain.numParams args ρ
    let calleeObjEnv : StructIR.ObjEnv := fun param =>
      match args[param]? with
      | some arg => objEnv arg
      | none => []
    let adjustedObjEnv : StructIR.ObjEnv := fun v =>
      if h : nextFresh ≤ v then
        calleeObjEnv (v - nextFresh)
      else
        []
    let callee :=
      (StructIRToFlatIRDirect.compileConstrainBody m j adjustedObjEnv nextFresh' freshBody).1
    let nextFresh'' := (StructIRToFlatIRDirect.compileConstrainBody m j adjustedObjEnv
      nextFresh' freshBody).2.2
    FlatIRSubst.programAtoms (F := F) (liftStructWitness w) p =
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w) paramBinds ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w) callee ++
      FlatIRSubst.programAtoms (F := F) (liftStructWitness w)
        (StructIRToFlatIRDirect.compileConstrainBody m i objEnv nextFresh'' rest).1 := by
  simp [StructIRToFlatIRDirect.compileConstrainBody, programAtoms_append, List.append_assoc]
  rfl

end StructIRToFlatIRDirectSim
