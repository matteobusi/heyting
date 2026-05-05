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

/-! ## Pass composition instances

The four-pass pipeline is built by composing individual `PresReflPass` instances:

```
StructIR --[pass1]--> StructInlineIR --[pass2]--> MemberlessIR --[pass3]--> FlatIR --[pass4]--> R1CS
```

We compose them using `PresReflPass.compose`:
- `pass12 = compose pass1 pass2` : StructIR → MemberlessIR
- `pass34 = compose pass3 pass4` : MemberlessIR → R1CS  
- `pipeline = compose pass12 pass34` : StructIR → R1CS

All preservation and reflection proofs are automatically composed by `PresReflPass.compose`!
The witness relation chains through all intermediate languages:
`witnessRel m ws wr := ∃ wi wm wf, rel1 m ws wi ∧ rel2 (compile1 m) wi wm ∧
                                    rel3 (compile2 m') wm wf ∧ rel4 (compile3 m'') wf wr`
-/

/-- Full pipeline: StructIR → R1CS via 4-pass composition -/
instance instPresReflPass : PresReflPass (StructIR.Language n F) (R1CS.Language F) :=
  -- Compose pass1 and pass2
  let pass12 := PresReflPass.compose 
    (S := StructIR.Language n F)
    (M := StructInlineIR.Language n F)
    (T := MemberlessIR.instLanguage n F)
    (StructIRToStructInlineIR.CorrectPass n F)
    (StructInlineIRToMemberlessIR.PresReflPass n F)
  -- Compose pass3 and pass4
  let pass34 := PresReflPass.compose
    (S := MemberlessIR.instLanguage n F)
    (M := FlatIR.Language F)
    (T := R1CS.Language F)
    (MemberlessIRToFlatIR.PresReflPass n F)
    (FlatIRToR1CS.CorrectPass F)
  -- Compose the two halves
  PresReflPass.compose
    (S := StructIR.Language n F)
    (M := MemberlessIR.instLanguage n F)
    (T := R1CS.Language F)
    pass12 pass34

/-- Full pipeline as a `Pass` (derived from PresReflPass) -/
instance instPass : Pass (StructIR.Language n F) (R1CS.Language F) :=
  inferInstance

/-! ## Convenience definitions

These provide explicit access to the compiled program and witness relation.
-/

/-- Compile StructIR program through the full 4-pass pipeline to R1CS. -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  { (@instPresReflPass n F _).compile m with numPublicInputs := numPub }

/-- Compile StructIR to StructInlineIR (pass 1 only). -/
def compileInline (m : StructIR.Module (n + 1) F) : StructInlineIR.Module (n + 1) F :=
  StructIRToStructInlineIR.compile m

/-- Compile StructIR to MemberlessIR (passes 1+2). -/
def compileMemberless (m : StructIR.Module (n + 1) F) : MemberlessIR.Module (n + 1) F :=
  StructInlineIRToMemberlessIR.compile (compileInline m)

/-- Compile StructIR to FlatIR (passes 1+2+3). -/
def compileFlatIR (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  MemberlessIRToFlatIR.compile (compileMemberless m)

/-- The composed witness relation for the full pipeline. -/
def witnessRel (m : StructIR.Module (n + 1) F)
    (ws : StructIR.Witness F) (wr : R1CS.Witness F) : Prop :=
  (@instPresReflPass n F _).witnessRel m ws wr

/-- End-to-end witness generation utility.
    
    Given a StructIR module and inputs, computes the StructIR witness and then
    compiles it through all 4 passes to produce an R1CS witness.
-/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map fun ws =>
    -- Compile witness through all 4 passes
    let wi := ws  -- Pass 1: StructIR → StructInlineIR (identity)
    let wm := StructInlineIRToMemberlessIR.compileWitness (compileInline m) wi
    let wf := MemberlessIRToFlatIR.compileModuleWitness (compileMemberless m) wm
    FlatIRToR1CS.compileWitness (F := F) wf

end Pipeline
