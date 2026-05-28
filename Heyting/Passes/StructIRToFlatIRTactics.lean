/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Heyting.Languages.StructIR
import Heyting.Languages.FlatIR

/-!
# StructIRToFlatIR Proof Compression Tactics

Custom macros eliminating repetitive felt-op case patterns in
`Heyting/Passes/StructIRToFlatIR.lean`. Each macro discharges one
`| feltX ... =>` arm of a `cases stmt with` inside a frame-style
theorem.

## High-frame family (`materializeConstrainBody_*_frame_aux`)

Each frame theorem proves that `materializeConstrainBody` on a renamed
body leaves slot `v` unchanged, under a different "out-of-range"
hypothesis on `v`. The `feltAdd`/`feltSub`/.../`feltConst` cases all
share the same boilerplate:

1. unfold materializer and renameBody at the head,
2. derive `freshBase + dest < bound`  from `maxVarStmt_le_maxVarBody_cons`,
3. derive a tail hypothesis from `localCeilConstrainBody_noncall_tail_le`,
4. close with `ih ...` then a single `witness_update_*_frame` lemma.

## Tactics

- `materialize_high_frame_felt_case stmt` — discharges one felt-op arm of
  `materializeConstrainBody_high_frame_aux`. `stmt` is the matched
  constructor expression (e.g. `.feltAdd dest src1 src2`).
- `materialize_middle_frame_felt_case stmt` — same for
  `materializeConstrainBody_middle_frame_aux`.
- `materialize_fresh_frame_felt_case stmt val` — same for
  `materializeConstrainBody_fresh_frame_aux`. `val` is the felt value
  produced by the op (e.g. `env (freshMap freshBase src1) + ...`).
- `materialize_init_frame_felt_case stmt` — same for
  `materializeConstrainBody_init_frame_aux`.
- `compile_next_ge_felt_case` / `compile_localCeil_felt_case` — one-line
  arm for `compileConstrainBody_next_ge_aux` /
  `compileConstrainBody_localCeil_eq_aux`.

## Hygiene note

The macros use `Lean.mkIdent` to construct identifier syntax for both
global names (the lemmas they reference) and the local names bound by
the enclosing theorem (`m`, `i`, `freshBase`, `dest`, `runFresh`, `v`,
`rest`, `wt`, `env`, `objEnv`, `ih`, `hFitRest`, ...). `mkIdent`
deliberately bypasses macro hygiene so the produced syntax refers to
the call-site names; this is the intended behaviour here since the
macro body is supposed to manipulate the caller's locals, not introduce
fresh ones. Each macro doc lists the locals it expects to find in
scope.
-/

namespace StructIRToFlatIR.CompressTactics

open Lean Meta Elab Tactic

/-- Non-hygienic two-segment identifier. `mkIdent` here intentionally bypasses
hygiene so the produced syntax refers to globals at the call site. -/
private def i₂ (s₁ s₂ : String) : Lean.Ident :=
  Lean.mkIdent (.mkStr2 s₁ s₂)

/-- Non-hygienic single-segment identifier. Used to refer to locals bound by
the enclosing theorem at the call site. -/
private def i₁ (s : String) : Lean.Ident := Lean.mkIdent (.mkSimple s)

/--
Discharge a felt-op `| feltX ... =>` arm of
`materializeConstrainBody_high_frame_aux`. Expects the enclosing theorem
to have bound: `m`, `i`, `freshBase`, `dest`, `runFresh`, `v`, `rest`,
`wt`, `ih`, `hFitRest`, `hv`, `hRun_le_v`, plus the implicit `witnessBase`.

Usage: `materialize_high_frame_felt_case (.feltAdd dest src1 src2)`.
-/
syntax "materialize_high_frame_felt_case" term : tactic
elab_rules : tactic
  | `(tactic| materialize_high_frame_felt_case $stmt:term) => do
    -- Global references
    let renameBody             := i₂ "StructIRFreshen" "renameBody"
    let renameStmt             := i₂ "StructIRFreshen" "renameStmt"
    let materializeConstrainBody :=
      i₂ "StructIRToFlatIR" "materializeConstrainBody"
    let maxVarStmt             := i₂ "StructIRFreshen" "maxVarStmt"
    let maxVarStmt_le_maxVarBody_cons :=
      i₂ "StructIRToFlatIR" "maxVarStmt_le_maxVarBody_cons"
    let localCeilConstrainBody :=
      i₂ "StructIRToFlatIR" "localCeilConstrainBody"
    let localCeilConstrainBody_noncall_tail_le :=
      i₂ "StructIRToFlatIR" "localCeilConstrainBody_noncall_tail_le"
    let witness_update_high_frame :=
      i₂ "StructIRToFlatIR" "witness_update_high_frame"
    let ConstrainStmt          := i₂ "StructIR" "ConstrainStmt"
    -- Local references (resolved at the call site by mkIdent's non-hygienic
    -- name handling).
    let freshBase := i₁ "freshBase"
    let dest      := i₁ "dest"
    let runFresh  := i₁ "runFresh"
    let m         := i₁ "m"
    let i         := i₁ "i"
    let v         := i₁ "v"
    let rest      := i₁ "rest"
    let ih        := i₁ "ih"
    let wt        := i₁ "wt"
    let hFitRest  := i₁ "hFitRest"
    let hv        := i₁ "hv"
    let hRun_le_v := i₁ "hRun_le_v"
    let n         := i₁ "n"
    let F         := i₁ "F"
    evalTactic (← `(tactic| (
      simp only [$renameBody:ident, List.map_cons, $renameStmt:ident,
        $materializeConstrainBody:ident]
      have hDest : $freshBase:ident + $dest:ident < $runFresh:ident := by
        have := $maxVarStmt_le_maxVarBody_cons:ident
          ($stmt : $ConstrainStmt:ident $n:ident $i:ident $F:ident _) $rest:ident
        simp [$maxVarStmt:ident] at this; omega
      have hv' : $localCeilConstrainBody:ident
          $m:ident $i:ident $runFresh:ident $rest:ident ≤ $v:ident := by
        exact $localCeilConstrainBody_noncall_tail_le:ident
          $m:ident $runFresh:ident $v:ident
          $stmt $rest:ident (by intro target args hCall; cases hCall) $hv:ident
      calc _ = _ := $ih:ident _ _ _ _ $hFitRest:ident hv'
        _ = $wt:ident $v:ident :=
          $witness_update_high_frame:ident
            $wt:ident $freshBase:ident $dest:ident $runFresh:ident $v:ident _
            hDest $hRun_le_v:ident)))

/--
Discharge a felt-op `| feltX ... =>` arm of
`materializeConstrainBody_middle_frame_aux`. Expects the enclosing theorem
to have bound: `m`, `i`, `freshBase`, `dest`, `runFresh`, `anchor`, `v`,
`rest`, `wt`, `env`, `objEnv`, `ih`, `hFitRest`, `hAnchorRun`, `hAnchorV`,
`hv`, plus the implicit `witnessBase`.

Usage: `materialize_middle_frame_felt_case (.feltAdd dest src1 src2)`.
-/
syntax "materialize_middle_frame_felt_case" term : tactic
elab_rules : tactic
  | `(tactic| materialize_middle_frame_felt_case $stmt:term) => do
    -- Globals
    let renameBody := i₂ "StructIRFreshen" "renameBody"
    let renameStmt := i₂ "StructIRFreshen" "renameStmt"
    let materializeConstrainBody :=
      i₂ "StructIRToFlatIR" "materializeConstrainBody"
    let maxVarStmt := i₂ "StructIRFreshen" "maxVarStmt"
    let maxVarStmt_le_maxVarBody_cons :=
      i₂ "StructIRToFlatIR" "maxVarStmt_le_maxVarBody_cons"
    let witness_update_high_frame :=
      i₂ "StructIRToFlatIR" "witness_update_high_frame"
    let ConstrainStmt := i₂ "StructIR" "ConstrainStmt"
    -- Locals
    let freshBase   := i₁ "freshBase"
    let dest        := i₁ "dest"
    let anchor      := i₁ "anchor"
    let runFresh    := i₁ "runFresh"
    let v           := i₁ "v"
    let rest        := i₁ "rest"
    let ih          := i₁ "ih"
    let wt          := i₁ "wt"
    let objEnv      := i₁ "objEnv"
    let hFitRest    := i₁ "hFitRest"
    let hAnchorRun  := i₁ "hAnchorRun"
    let hAnchorV    := i₁ "hAnchorV"
    let hv          := i₁ "hv"
    let n           := i₁ "n"
    let i           := i₁ "i"
    let F           := i₁ "F"
    evalTactic (← `(tactic| (
      simp only [$renameBody:ident, List.map_cons, $renameStmt:ident,
        $materializeConstrainBody:ident]
      have hDest : $freshBase:ident + $dest:ident < $anchor:ident := by
        have := $maxVarStmt_le_maxVarBody_cons:ident
          ($stmt : $ConstrainStmt:ident $n:ident $i:ident $F:ident _) $rest:ident
        simp [$maxVarStmt:ident] at this; omega
      calc _ = _ := $ih:ident (wt := _) (env := _) (objEnv := $objEnv:ident)
              (runFresh := $runFresh:ident) $hFitRest:ident $hAnchorRun:ident $hv:ident
        _ = $wt:ident $v:ident :=
          $witness_update_high_frame:ident
            $wt:ident $freshBase:ident $dest:ident $anchor:ident $v:ident _
            hDest $hAnchorV:ident)))

/--
Discharge a felt-op `| feltX ... =>` arm of
`materializeConstrainBody_init_frame_aux`. Expects the enclosing theorem
to have bound: `m`, `i`, `freshBase`, `dest`, `runFresh`, `x`, `rest`,
`wt`, `env`, `objEnv`, `init`, `ih`, `hSSA'`, `hx`, `hlt`, plus the
implicit `witnessBase`. The constructor fields (`dest`, `src...`) must
already be in scope via the `cases stmt with` destructuring.

Usage: `materialize_init_frame_felt_case` (no arguments needed).
-/
syntax "materialize_init_frame_felt_case" : tactic
elab_rules : tactic
  | `(tactic| materialize_init_frame_felt_case) => do
    -- Globals
    let renameBody := i₂ "StructIRFreshen" "renameBody"
    let renameStmt := i₂ "StructIRFreshen" "renameStmt"
    let materializeConstrainBody :=
      i₂ "StructIRToFlatIR" "materializeConstrainBody"
    let freshMap   := i₂ "StructIRFreshen" "freshMap"
    let isSSA      := i₂ "StructIR" "isSSA"
    let init_true_dest_ne := i₁ "init_true_dest_ne"
    -- The ConstrainStmt.dest projection.
    let constrainStmtDest :=
      mkIdent (.mkStr3 "StructIR" "ConstrainStmt" "dest")
    -- Locals
    let init      := i₁ "init"
    let dest      := i₁ "dest"
    let rest      := i₁ "rest"
    let ih        := i₁ "ih"
    let wt        := i₁ "wt"
    let freshBase := i₁ "freshBase"
    let x         := i₁ "x"
    let hSSA'     := i₁ "hSSA'"
    let hx        := i₁ "hx"
    let hlt       := i₁ "hlt"
    evalTactic (← `(tactic| (
      have hStep :
          !$init:ident $dest:ident
            && $isSSA:ident (fun y => $init:ident y || y == $dest:ident) $rest:ident = true := by
        simpa [$constrainStmtDest:ident] using $hSSA':ident
      have hStep' :
          (!$init:ident $dest:ident = true) ∧
            $isSSA:ident (fun y => $init:ident y || y == $dest:ident) $rest:ident = true := by
        simpa [Bool.and_eq_true] using hStep
      have hne : $x:ident ≠ $dest:ident :=
        $init_true_dest_ne:ident $hx:ident (by simpa using hStep'.1)
      simp only [$renameBody:ident, List.map_cons, $renameStmt:ident,
        $materializeConstrainBody:ident]
      calc _ = _ := by
              apply $ih:ident
              · exact hStep'.2
              · simp [$hx:ident]
              · exact $hlt:ident
        _ = $wt:ident ($freshMap:ident $freshBase:ident $x:ident) := by
              simp [$freshMap:ident, hne])))

/--
One-liner arm for `compileConstrainBody_next_ge_aux` and
`compileConstrainBody_localCeil_eq_aux` felt-op cases (the cases that
just step `ih objEnv nextFresh`).

Usage: `compile_next_ge_felt_case` (no arguments needed since IH and
context are uniform across all felt arms).
-/
syntax "compile_next_ge_felt_case" : tactic
elab_rules : tactic
  | `(tactic| compile_next_ge_felt_case) => do
    let compileConstrainBody :=
      i₂ "StructIRToFlatIR" "compileConstrainBody"
    let ih      := i₁ "ih"
    let objEnv  := i₁ "objEnv"
    let nextFresh := i₁ "nextFresh"
    evalTactic (← `(tactic|
      simpa [$compileConstrainBody:ident] using
        $ih:ident $objEnv:ident $nextFresh:ident))

/-- Same as `compile_next_ge_felt_case` but unfolds `localCeilConstrainBody`
too — for `compileConstrainBody_localCeil_eq_aux`. -/
syntax "compile_localCeil_felt_case" : tactic
elab_rules : tactic
  | `(tactic| compile_localCeil_felt_case) => do
    let compileConstrainBody :=
      i₂ "StructIRToFlatIR" "compileConstrainBody"
    let localCeilConstrainBody :=
      i₂ "StructIRToFlatIR" "localCeilConstrainBody"
    let ih      := i₁ "ih"
    let objEnv  := i₁ "objEnv"
    let nextFresh := i₁ "nextFresh"
    evalTactic (← `(tactic|
      simpa [$compileConstrainBody:ident, $localCeilConstrainBody:ident] using
        $ih:ident $objEnv:ident $nextFresh:ident))



end StructIRToFlatIR.CompressTactics
