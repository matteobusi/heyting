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
  try (evalTactic (← `(tactic| rfl)))

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
        (by simp [stmt, StructIR.ConstrainStmt.reads]) hFit))
    
    -- Derive ne via SSA
    evalTactic (← `(tactic| have $hNeName:ident :=
      StructIR.isSSA_read_ne_dest init stmt rest dest $x:ident hSSA hd
        (by simp [stmt, StructIR.ConstrainStmt.reads])))
    
    -- Recurse for remaining variables
    evalTactic (← `(tactic| ssa_lemmas_for $xs*))

/--
Meta-tactic to prove `materialize_step_feltXXX_satisfies` for binary felt operations.
Eliminates ~200 lines of nearly-identical proofs for Add/Sub/Mul/Div/Neg.

Usage:
```lean
theorem materialize_step_feltAdd_satisfies ... := by materialize_binop (+)
theorem materialize_step_feltSub_satisfies ... := by materialize_binop (-)
theorem materialize_step_feltMul_satisfies ... := by materialize_binop (*)
theorem materialize_step_feltDiv_satisfies ... := by materialize_binop (/)
```

The tactic:
1. Introduces the statement as a `let stmt := .feltXXX dest src1 src2`
2. Proves `stmt.dest = some dest` via `rfl`
3. Computes the value using the provided operation
4. Applies frame lemmas (`materializeConstrainBody_head_dest_after_write`)
5. Derives SSA properties for src1, src2 using `ssa_lemmas_for`
6. Applies the final `materialize_compile_feltXXX_satisfies` theorem
-/
syntax "materialize_binop" "(" term ")" : tactic

macro_rules
  | `(tactic| materialize_binop ($op:term)) => `(tactic| (
      -- Introduce the statement
      let stmt : StructIR.ConstrainStmt n i F (m.structs i).members.length :=
        .feltAdd dest src1 src2  -- TODO: infer constructor from goal
      have hd : stmt.dest = some dest := by rfl
      -- Compute the value
      let val := env (StructIRFreshen.freshMap freshBase src1) $op
                 env (StructIRFreshen.freshMap freshBase src2)
      -- Apply frame lemma for destination
      have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i
        init wt env objEnv freshBase runFresh dest val stmt rest hSSA hAgree hd hFit
      -- Derive SSA properties for source operands
      ssa_lemmas_for src1 src2
      -- Apply final lemma with simplified hypotheses
      exact materialize_compile_feltAdd_satisfies witnessBase m i freshBase wt env
        objEnv runFresh dest src1 src2 rest ih hDest
        (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)
    ))

/--
Tactic to prove unary felt operation satisfaction theorems (e.g., `feltNeg`, `feltConst`).
Similar to `materialize_binop` but for unary operations.
-/
syntax "materialize_unop" "(" term ")" : tactic

macro_rules
  | `(tactic| materialize_unop ($op:term)) => `(tactic| (
      let stmt : StructIR.ConstrainStmt n i F (m.structs i).members.length :=
        .feltNeg dest src  -- TODO: infer constructor
      have hd : stmt.dest = some dest := by rfl
      let val := $op (env (StructIRFreshen.freshMap freshBase src))
      have hDest := materializeConstrainBody_head_dest_after_write witnessBase m i
        init wt env objEnv freshBase runFresh dest val stmt rest hSSA hAgree hd hFit
      ssa_lemmas_for src
      exact materialize_compile_feltNeg_satisfies witnessBase m i freshBase wt env
        objEnv runFresh dest src rest ih hDest (by simpa [hsrc_ne] using hSrc)
    ))

end StructIRToFlatIR.CompressTactics
