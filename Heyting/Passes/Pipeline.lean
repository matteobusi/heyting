/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Pass
import Heyting.Core.ComputingLanguage
import Heyting.Languages.StructIR
import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Core.VarIdEncoding
import Heyting.Passes.StructIRToFlatIRDirect
import Heyting.Passes.FlatIRToR1CS

/-!
# Executable Compiler Pipeline

Top-level executable composition used by the CLI.

Current path:

`StructIR -> FlatIR -> R1CS`

This file contains only executable composition and witness plumbing. Proofs of
individual pass correctness live in the pass-specific files.
-/

namespace Pipeline

variable {n : Nat} {F : Type} [Field F]

/-! ## Direct pipeline

Current executable pipeline:

```
StructIR --[StructIRToFlatIRDirect]--> FlatIR --[FlatIRToR1CS]--> R1CS
```

Old intermediate-language pipeline removed from build until those files return.
-/

/-! ## Convenience definitions -/

/-- FlatIR witness induced by decode-seeded StructIR witness semantics. -/
def liftStructWitness (w : StructIR.Witness F) : FlatIR.Witness F :=
  fun v => w (VarIdEncoding.decode v)

/-- Compile StructIR program through direct StructIR -> FlatIR -> R1CS pipeline. -/
def compileProgram (m : StructIR.Module (n + 1) F) : R1CS.System F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let numPub := (m.structs mainIdx).members.countP (·.isPublic)
  FlatIRToR1CS.compileProgram F (StructIRToFlatIRDirect.compileProgram m) numPub

/-- Compile StructIR to FlatIR. -/
def compileFlatIR (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  StructIRToFlatIRDirect.compileProgram m

/-- End-to-end executable witness generation through StructIR and FlatIR witnesses. -/
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F)
    [DecidableEq F] : Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map fun ws =>
    FlatIRToR1CS.compileWitness (F := F) (liftStructWitness ws)

end Pipeline
