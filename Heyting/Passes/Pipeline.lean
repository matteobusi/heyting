/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Core.ComputingLanguage
import Heyting.Languages.StructIR
import Heyting.Languages.MemberlessIR
import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Passes.StructIRToMemberlessIR
import Heyting.Passes.MemberlessIRToFlatIR
import Heyting.Passes.FlatIRToR1CS

/-!
# End-to-End Pipeline: StructIR → R1CS

Composes three passes into a single, top-level `PresReflPass` from
`StructIR.Language` to `R1CS.Language`:

```
StructIR
  --[StructIRToMemberlessIR]--> MemberlessIR
  --[MemberlessIRToFlatIR]-->   FlatIR
  --[FlatIRToR1CS]-->           R1CS
```

## Correctness

Preservation and reflection follow by chaining the three sub-passes:

- **Preservation**: StructIR sat → MemberlessIR sat → FlatIR sat → R1CS sat.
- **Reflection**: R1CS sat → FlatIR sat → MemberlessIR sat → StructIR sat.

## Witness chain

```
ws : StructIR.Witness F
  --[StructIRToMemberlessIR.compileModuleWitness]--> mw : Nat → F
  --[MemberlessIRToFlatIR.compileModuleWitness]-->   wf : FlatIR.Witness F
  --[FlatIRToR1CS.compileWitness]-->                 wr : R1CS.Witness F
```

## End-to-end witness generation

`pipelineWitness` chains `StructIR.computeWitness` with the forward witness
translations to produce an `R1CS.Witness F` directly from public inputs.
-/

namespace Pipeline

variable {n : Nat} {F : Type} [Field F]

/-! ## Program compilation -/

/-- Compile a StructIR module to a MemberlessIR module (Pass 1). -/
def compileMemberless (m : StructIR.Module (n + 1) F) : MemberlessIR.Module (n + 1) F :=
  StructIRToMemberlessIR.compile m

/-- Compile a MemberlessIR module to a FlatIR program (Pass 2). -/
def compileFlatFromMemberless (m : MemberlessIR.Module (n + 1) F) : FlatIR.Program F :=
  MemberlessIRToFlatIR.compile m

/-- Compile a StructIR module to a FlatIR program (Passes 1+2). -/
def compileFlatIR (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  compileFlatFromMemberless (compileMemberless m)

/-- Compile a StructIR module to an R1CS system (all three passes).
    The public-input count is derived from the main struct's `{llzk.pub}` members. -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  { (FlatIRToR1CS.compileProgram F (compileFlatIR m)) with
    numPublicInputs := numPub }

/-! ## Witness translation -/

/-- Forward witness (StructIR → MemberlessIR). -/
def compileWitnessMemberless (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    Nat → F :=
  StructIRToMemberlessIR.compileModuleWitness m ws

/-- Forward witness (MemberlessIR → FlatIR). -/
def compileWitnessFlat (m : MemberlessIR.Module (n + 1) F) (mw : Nat → F) :
    FlatIR.Witness F :=
  MemberlessIRToFlatIR.compileModuleWitness m mw

/-- Forward witness (StructIR → FlatIR): compose passes 1 and 2. -/
def compileWitnessFlatIR (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    FlatIR.Witness F :=
  compileWitnessFlat (compileMemberless m) (compileWitnessMemberless m ws)

/-- Forward witness (StructIR → R1CS): compose all three passes. -/
def compileWitness (m : StructIR.Module (n + 1) F) (ws : StructIR.Witness F) :
    R1CS.Witness F :=
  FlatIRToR1CS.compileWitness F (compileWitnessFlatIR m ws)

/-- Backward witness (R1CS → MemberlessIR): pull back through passes 2+3. -/
def extractWitnessMemberless (m : MemberlessIR.Module (n + 1) F) (wr : R1CS.Witness F) :
    Nat → F :=
  MemberlessIRToFlatIR.extractWitness m (FlatIRToR1CS.extractWitness F wr)

/-- Backward witness (R1CS → StructIR): pull back through all three passes. -/
def extractWitness (m : StructIR.Module (n + 1) F) (wr : R1CS.Witness F) :
    StructIR.Witness F :=
  StructIRToMemberlessIR.extractWitness m
    (extractWitnessMemberless (compileMemberless m) wr)

/-! ## Composed `witnessRel` -/

/-- The composed witness relation: there exist intermediate witnesses at each
    IR level relating the source StructIR witness to the target R1CS witness. -/
def witnessRel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (wr : R1CS.Witness F) : Prop :=
  ∃ (mw : Nat → F) (wf : FlatIR.Witness F),
    StructIRToMemberlessIR.witnessRel m ws mw ∧
    MemberlessIRToFlatIR.witnessRel (compileMemberless m) mw wf ∧
    (FlatIRToR1CS.CorrectPass F).witnessRel (compileFlatFromMemberless (compileMemberless m)) wf wr

/-! ## Composed `PresReflPass` instance -/

/-- `PresReflPass` instance for the full StructIR → R1CS pipeline.
    Preservation and reflection follow by composing the three sub-passes.
    Note: the preservation and reflection proofs for passes 1 and 2 are
    currently `sorry`d in the sub-pass files; they will be filled in. -/
instance CorrectPass (n : Nat) (F : Type) [Field F] :
    PresReflPass (StructIR.Language n F) (R1CS.Language F) where
  compile    := compileProgram
  witnessRel := witnessRel

  preservation := by
    intro ws p hsat
    -- Pass 1: StructIR → MemberlessIR
    have hmw := StructIRToMemberlessIR.preservation p ws hsat
    -- Pass 2: MemberlessIR → FlatIR
    have hwf := MemberlessIRToFlatIR.preservation (compileMemberless p)
      (compileWitnessMemberless p ws) hmw
    -- Pass 3: FlatIR → R1CS
    obtain ⟨wr, hrel3, hsat_r⟩ :=
      (FlatIRToR1CS.CorrectPass F).preservation
        (compileWitnessFlatIR p ws)
        (compileFlatIR p)
        hwf
    exact ⟨wr,
      ⟨compileWitnessMemberless p ws, compileWitnessFlatIR p ws,
       rfl, rfl, hrel3⟩,
      hsat_r⟩

  reflection := by
    intro wr p hsat_r
    -- Pass 3 backward: R1CS → FlatIR
    obtain ⟨wf, hrel3, hsat_f⟩ :=
      (FlatIRToR1CS.CorrectPass F).reflection wr
        (compileFlatIR p) hsat_r
    -- Pass 2 backward: FlatIR → MemberlessIR
    have hmw := MemberlessIRToFlatIR.reflection (compileMemberless p) wf hsat_f
    -- Pass 1 backward: MemberlessIR → StructIR
    have hws := StructIRToMemberlessIR.reflection p
      (MemberlessIRToFlatIR.extractWitness (compileMemberless p) wf) hmw
    exact ⟨StructIRToMemberlessIR.extractWitness p
        (MemberlessIRToFlatIR.extractWitness (compileMemberless p) wf),
      ⟨MemberlessIRToFlatIR.extractWitness (compileMemberless p) wf, wf,
       sorry, sorry, hrel3⟩,
      hws⟩

/-! ## End-to-end witness generation -/

/-- Attempt to produce an R1CS witness directly from a StructIR module and
    public inputs by chaining the compute interpreter with the three forward
    witness translations.  Returns `none` if the interpreter encounters a
    runtime fault (e.g. division by zero). -/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map (compileWitness m)

end Pipeline
