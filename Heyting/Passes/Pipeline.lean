/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Core.ComputingLanguage
import Heyting.Languages.StructIR
import Heyting.Languages.StructInlineIR
import Heyting.Languages.MemberlessIR
import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Passes.StructIRToStructInlineIR
import Heyting.Passes.StructInlineIRToMemberlessIR
import Heyting.Passes.MemberlessIRToFlatIR
import Heyting.Passes.FlatIRToR1CS

namespace Pipeline

variable {n : Nat} {F : Type} [Field F]

/-- Compile StructIR to StructInlineIR (pass 1). -/
def compileInline (m : StructIR.Module (n + 1) F) : StructInlineIR.Module (n + 1) F :=
  StructIRToStructInlineIR.compile m

/-- Compile StructInlineIR to MemberlessIR (pass 2). -/
def compileMemberlessFromInline (m : StructInlineIR.Module (n + 1) F) :
    MemberlessIR.Module (n + 1) F :=
  StructInlineIRToMemberlessIR.compile m

/-- Compile StructIR to MemberlessIR (passes 1+2). -/
def compileMemberless (m : StructIR.Module (n + 1) F) : MemberlessIR.Module (n + 1) F :=
  compileMemberlessFromInline (compileInline m)

/-- Compile MemberlessIR to FlatIR (pass 3). -/
def compileFlatFromMemberless (m : MemberlessIR.Module (n + 1) F) : FlatIR.Program F :=
  MemberlessIRToFlatIR.compile m

/-- Compile StructIR to FlatIR (passes 1+2+3). -/
def compileFlatIR (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  compileFlatFromMemberless (compileMemberless m)

/-- Compile StructIR to R1CS (passes 1+2+3+4). -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  { (FlatIRToR1CS.compileProgram F (compileFlatIR m)) with
    numPublicInputs := numPub }

/-- Forward witness (StructIR -> StructInlineIR): identity relation carrier. -/
def compileWitnessInline (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    StructInlineIR.Witness F :=
  let _ := m.structs
  ws

/-- Forward witness (StructInlineIR -> MemberlessIR). -/
def compileWitnessMemberless (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    Nat -> F :=
  StructInlineIRToMemberlessIR.compileWitness (compileInline m) ws

/-- Forward witness (MemberlessIR -> FlatIR). -/
def compileWitnessFlat (m : MemberlessIR.Module (n + 1) F) (mw : Nat -> F) :
    FlatIR.Witness F :=
  MemberlessIRToFlatIR.compileModuleWitness m mw

/-- Forward witness (StructIR -> FlatIR). -/
def compileWitnessFlatIR (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    FlatIR.Witness F :=
  compileWitnessFlat (compileMemberless m) (compileWitnessMemberless m ws)

/-- Forward witness (StructIR -> R1CS). -/
def compileWitness (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    R1CS.Witness F :=
  FlatIRToR1CS.compileWitness F (compileWitnessFlatIR m ws)

/-- Backward witness (R1CS -> MemberlessIR). -/
def extractWitnessMemberless (m : MemberlessIR.Module (n + 1) F) (wr : R1CS.Witness F) :
    Nat -> F :=
  MemberlessIRToFlatIR.extractWitness m (FlatIRToR1CS.extractWitness F wr)

/-- Backward witness (R1CS -> StructInlineIR). -/
def extractWitnessInline (m : StructIR.Module (n + 1) F) (wr : R1CS.Witness F) :
    StructInlineIR.Witness F :=
  StructInlineIRToMemberlessIR.extractWitness (compileInline m)
    (extractWitnessMemberless (compileMemberless m) wr)

/-- Backward witness (R1CS -> StructIR). -/
def extractWitness (m : StructIR.Module (n + 1) F) (wr : R1CS.Witness F) :
    StructIR.Witness F :=
  extractWitnessInline m wr

/-- Composed witness relation for the four-pass pipeline. -/
def witnessRel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (wr : R1CS.Witness F) : Prop :=
  ∃ (wi : StructInlineIR.Witness F) (mw : Nat -> F) (wf : FlatIR.Witness F),
    StructIRToStructInlineIR.witnessRel m ws wi ∧
    StructInlineIRToMemberlessIR.witnessRel (compileInline m) wi mw ∧
    MemberlessIRToFlatIR.witnessRel (compileMemberless m) mw wf ∧
    (FlatIRToR1CS.CorrectPass F).witnessRel (compileFlatFromMemberless (compileMemberless m)) wf wr

/-- Four-pass pipeline as a `Pass` (proof obligations deferred to phase 2). -/
instance Pass (n : Nat) (F : Type) [Field F] :
    Pass (StructIR.Language n F) (R1CS.Language F) where
  compile := compileProgram
  witnessRel := witnessRel

/-- End-to-end witness generation utility. -/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map (compileWitness m)

end Pipeline
