import Heyting.Core.VarIdEncoding
import Heyting.Core.Pass
import Heyting.Languages.FlatIR
import Heyting.Languages.FlatIRSubst
import Heyting.Languages.StructIR
import Heyting.Languages.StructIRSubst

/-!
# StructIR -> FlatIR (Direct)

Direct compiler from StructIR constrain bodies to FlatIR instruction lists.

Design points:
- lowers arithmetic and equality directly,
- lowers `readMember` using concrete `(path, member)` encoding,
- inlines calls recursively,
- uses the same deterministic freshening strategy as `StructIRSubst`.
-/
namespace StructIRToFlatIRDirect

open StructIR

variable {F : Type} [Field F]

/-- Encode a concrete witness coordinate `(path, member)` as a FlatIR variable id. -/
def encodeWitnessVar (path : StructIR.InstancePath) (member : Nat) : FlatIR.VarId :=
  VarIdEncoding.encode (path, member)

/-- Compile call parameter bindings after freshening (`ρ idx = nextFresh + idx`). -/
def compileParamBindings (numParams : Nat) (args : List Nat) (ρ : Nat → Nat) :
    List (FlatIR.Instr F) :=
  let rec go (idx remaining : Nat) : List (FlatIR.Instr F) :=
    match remaining with
    | 0 => []
    | k + 1 =>
      let head :=
        match args[idx]? with
        | some arg => [FlatIR.Instr.assertEq (ρ idx) arg]
        | none => [FlatIR.Instr.assignConst (ρ idx) (0 : F)]
      head ++ go (idx + 1) k
  go 0 numParams

/--
Compile a StructIR constrain body to FlatIR, threading object environment and
freshness state.
-/
def compileConstrainBody (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    List (FlatIR.Instr F) × StructIR.ObjEnv × Nat :=
  match stmts with
  | [] => ([], objEnv, nextFresh)
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltSub dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignSub dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltMul dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignMul dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltDiv dest src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignDiv dest src1 src2 :: tail, objEnv', nextFresh')
    | .feltNeg dest src =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignNeg dest src :: tail, objEnv', nextFresh')
    | .feltConst dest c =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignConst dest c :: tail, objEnv', nextFresh')
    | .readMember dest self member =>
      let path := objEnv self
      let witnessVar := encodeWitnessVar path member.val
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnvStep nextFresh rest
      (FlatIR.Instr.assertEq dest witnessVar :: tail, objEnv', nextFresh')
    | .constrainEq src1 src2 =>
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assertEq src1 src2 :: tail, objEnv', nextFresh')
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let ρ : Nat → Nat := StructIRSubst.freshMap nextFresh
      let (freshBody, nextFresh') := StructIRSubst.freshenBody nextFresh calleeBody
      let paramBinds := compileParamBindings (F := F) (m.structs j).constrain.numParams args ρ
      let calleeObjEnv : StructIR.ObjEnv := fun param =>
        match args[param]? with
        | some arg => objEnv arg
        | none => []
      -- Adjust objEnv for ρ-renaming: ρ(k) = nextFresh + k should map to
      -- calleeObjEnv(k) (the path of the k-th arg).  For k ≥ nextFresh + numParams
      -- (non-param freshened vars) the result is [] which is overwritten by
      -- subsequent readMember updates inside the callee.
      let adjustedObjEnv : StructIR.ObjEnv := fun v =>
        if nextFresh ≤ v then
          calleeObjEnv (v - nextFresh)
        else
          []
      let (calleeInstrs, _, nextFresh'') :=
        compileConstrainBody m j adjustedObjEnv nextFresh' freshBody
      let (tail, objEnvTail, nextFreshTail) :=
        compileConstrainBody m i objEnv nextFresh'' rest
      (paramBinds ++ calleeInstrs ++ tail, objEnvTail, nextFreshTail)
  termination_by (i, stmts.length)
  decreasing_by
    all_goals
      first
      | apply Prod.Lex.left
        exact target.isLt
      | apply Prod.Lex.right
        simp

theorem compileConstrainBody_feltAdd_eq
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody m i objEnv nextFresh (.feltAdd dest src1 src2 :: rest) =
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

theorem compileConstrainBody_constrainEq_eq
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (src1 src2 : Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody m i objEnv nextFresh (.constrainEq src1 src2 :: rest) =
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnv nextFresh rest
      (FlatIR.Instr.assertEq src1 src2 :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

theorem compileConstrainBody_readMember_eq
    (m : StructIR.Module n F)
    (i : Fin n) (objEnv : StructIR.ObjEnv) (nextFresh : Nat)
    (dest self : Nat) (member : Fin (m.structs i).members.length)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    compileConstrainBody m i objEnv nextFresh (.readMember dest self member :: rest) =
      let path := objEnv self
      let witnessVar := encodeWitnessVar path member.val
      let objEnvStep := StructIR.ObjEnv.update objEnv dest (path ++ [member.val])
      let (tail, objEnv', nextFresh') := compileConstrainBody m i objEnvStep nextFresh rest
      (FlatIR.Instr.assertEq dest witnessVar :: tail, objEnv', nextFresh') := by
  simp [compileConstrainBody]

/-- Compile a full StructIR module directly to a FlatIR program. -/
def compileProgram (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initObjEnv : StructIR.ObjEnv := StructIR.ObjEnv.update (fun _ => []) 0 []
  let initNextFresh := StructIRSubst.maxVarBody (m.structs mainIdx).constrain.body + 1
  let (instrs, _, _) :=
    compileConstrainBody m mainIdx initObjEnv initNextFresh (m.structs mainIdx).constrain.body
  instrs

instance CorrectPass (F : Type) [Field F] (n : Nat) :
    Pass (StructIRSubst.Language n F) (FlatIRSubst.Language F) where
  compile := compileProgram (F := F)
  witnessRel _ ws wt :=
    -- Uniform bijection: FlatIR var v corresponds to StructIR position decode v.
    -- This aligns with the decode-seeded satisfies semantics.
    ∀ v, wt v = ws (VarIdEncoding.decode v)

end StructIRToFlatIRDirect
