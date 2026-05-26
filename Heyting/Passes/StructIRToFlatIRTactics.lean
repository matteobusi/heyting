/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Heyting.Languages.StructIR
import Heyting.Languages.FlatIR

/-!
# StructIRToFlatIR Proof Compression Tactics

Custom tactics to eliminate repetitive proof patterns in StructIRToFlatIR.lean.

## Tactics

- `materialize_binop op` — Prove `materialize_step_feltXXX_satisfies` for binary felt ops
- `materialize_rename_simp` — Prove `materializeConstrainBody_XXX_rename_eq` via simp
- `frame_by_fresh` — Prove freshness-based non-interference lemmas
- `ssa_lemmas_for x y z` — Derive SSA properties for variables x, y, z in current goal
-/

namespace StructIRToFlatIR.CompressTactics

open Lean Meta Elab Tactic

/--
Tactic to prove `materializeConstrainBody_XXX_rename_eq` theorems.
These all follow the pattern: unfold definitions, apply `simp`, done.
-/
elab "materialize_rename_simp" : tactic => do
  evalTactic (← `(tactic| simp only [
    materializeConstrainBody, StructIRFreshen.renameBody, StructIRFreshen.renameStmt]))
  try
    evalTactic (← `(tactic| rfl))
  catch _ =>
    pure ()

/--
Tactic to prove frame lemmas: updating a fresh variable doesn't affect old slots.
Pattern: `(fun u => if u = freshMap n d then v else w u) x = w x` when `x < n`.
-/
elab "frame_by_fresh" : tactic => do
  -- Try to find freshness disjointness lemma in context
  evalTactic (← `(tactic| (
    have hne : _ := StructIRFreshen.fresh_old_disjoint _ _ _ ‹_›
    simp [hne]
  )))

/--
Tactic to derive SSA properties for a list of variables.
For each var `x` that appears in `stmt.reads`:
- Apply `materializeConstrainBody_head_read_after_write` if `x ≠ dest`
- Derive `x ≠ dest` via `isSSA_read_ne_dest`
-/
syntax "ssa_lemmas_for" ident* : tactic

elab_rules : tactic
  | `(tactic| ssa_lemmas_for) => pure ()
  | `(tactic| ssa_lemmas_for $x:ident $xs:ident*) => do
    -- Generate hypothesis name like hSrc1, hSrc2, etc.
    let xName := x.getId.toString
    let hName := Lean.mkIdent (.mkSimple s!"h{xName.capitalize}")
    let hNeName := Lean.mkIdent (.mkSimple s!"h{xName}_ne")
    
    -- Apply read-after-write lemma
    evalTactic (← `(tactic| have $hName:ident :=
      materializeConstrainBody_head_read_after_write witnessBase m i init wt env
        objEnv freshBase runFresh dest $x:ident val stmt rest hSSA hAgree hd
        (by simp [stmt, ConstrainStmt.reads]) hFit))
    
    -- Derive ne via SSA
    evalTactic (← `(tactic| have $hNeName:ident :=
      StructIR.isSSA_read_ne_dest init stmt rest dest $x:ident hSSA hd
        (by simp [stmt, ConstrainStmt.reads])))
    
    -- Recurse for remaining variables
    evalTactic (← `(tactic| ssa_lemmas_for $xs*))

end StructIRToFlatIR.CompressTactics
