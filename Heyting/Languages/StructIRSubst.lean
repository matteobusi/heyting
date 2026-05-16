import Heyting.Core.CheckedSemantics
import Heyting.Core.Language
import Heyting.Core.SubstSemantics
import Heyting.Core.VarIdEncoding
import Heyting.Languages.StructIR

/-!
# StructIR Checked Substitution Semantics

This module provides a deterministic checked evaluator for StructIR constrain
bodies based on symbolic substitution.

The evaluator emits atomic checks (`CAtom`) and returns either:
- `Result.success trace` with the full checked trace, or
- `Result.failure checkedPrefix failed` at first failure.

Call handling follows explicit freshening (1A): each callee body is renamed to
a fresh local-variable block before parameter substitution.
-/
namespace StructIRSubst

open CheckedSemantics
open SubstSemantics

variable {F : Type} [Field F] {n : Nat}

abbrev ValSubst (F : Type) := SubstSemantics.ValSubst F
abbrev PathSubst := SubstSemantics.PathSubst
abbrev Atom (F : Type) := SubstSemantics.CAtom F

def defaultValuation : SubstSemantics.LocalVar → F := fun _ => 0
def defaultPathValuation : SubstSemantics.LocalVar → SubstSemantics.InstancePath := fun _ => []

/-- Boolean checker for emitted atomic constraints. -/
def checkAtom [DecidableEq F] (w : StructIR.Witness F) (a : Atom F) : Bool :=
  match a with
  | .eq lhs rhs =>
    decide (VTerm.interp w defaultValuation defaultPathValuation lhs =
      VTerm.interp w defaultValuation defaultPathValuation rhs)
  | .neZero term =>
    decide (VTerm.interp w defaultValuation defaultPathValuation term ≠ 0)

theorem checkAtom_true_iff [DecidableEq F] (w : StructIR.Witness F) (a : Atom F) :
    checkAtom w a = true ↔ CAtom.interp w defaultValuation defaultPathValuation a := by
  cases a with
  | eq lhs rhs => simp [checkAtom, CAtom.interp]
  | neZero term => simp [checkAtom, CAtom.interp]

/-- Boolean/Prop reflection for the negative result of `checkAtom`. -/
theorem checkAtom_false_iff [DecidableEq F] (w : StructIR.Witness F) (a : Atom F) :
    checkAtom w a = false ↔ ¬CAtom.interp w defaultValuation defaultPathValuation a := by
  cases a with
  | eq lhs rhs => simp [checkAtom, CAtom.interp]
  | neZero term => simp [checkAtom, CAtom.interp]

omit [Field F] in
/-- `bindV` rewrites the updated key to the newly bound value term. -/
theorem bindV_eq (σv : ValSubst F) (x : Nat) (t : VTerm F) :
    bindV σv x t x = t := by
  simp [bindV]

omit [Field F] in
/-- `bindV` leaves all non-updated keys unchanged. -/
theorem bindV_ne (σv : ValSubst F) (x y : Nat) (t : VTerm F) (h : y ≠ x) :
    bindV σv x t y = σv y := by
  simp [bindV, h]

/-- `bindO` rewrites the updated key to the newly bound path term. -/
theorem bindO_eq (σo : PathSubst) (x : Nat) (t : PTerm) :
    bindO σo x t x = t := by
  simp [bindO]

/-- `bindO` leaves all non-updated keys unchanged. -/
theorem bindO_ne (σo : PathSubst) (x y : Nat) (t : PTerm) (h : y ≠ x) :
    bindO σo x t y = σo y := by
  simp [bindO, h]

/-- Interpretation is compatible with reading the bound value at the updated key. -/
theorem interp_bindV_eq (w : StructIR.Witness F) (ρv : SubstSemantics.LocalVar → F)
    (ρo : SubstSemantics.LocalVar → SubstSemantics.InstancePath)
    (σv : ValSubst F) (x : Nat) (t : VTerm F) :
    VTerm.interp w ρv ρo (bindV σv x t x) = VTerm.interp w ρv ρo t := by
  simp [bindV_eq]

/-- Interpretation is compatible with `bindV` at non-updated keys. -/
theorem interp_bindV_ne (w : StructIR.Witness F) (ρv : SubstSemantics.LocalVar → F)
    (ρo : SubstSemantics.LocalVar → SubstSemantics.InstancePath)
    (σv : ValSubst F) (x y : Nat) (t : VTerm F) (h : y ≠ x) :
    VTerm.interp w ρv ρo (bindV σv x t y) = VTerm.interp w ρv ρo (σv y) := by
  simp [bindV_ne, h]

/-- Interpretation is compatible with reading the bound path at the updated key. -/
theorem interp_bindO_eq (ρo : SubstSemantics.LocalVar → SubstSemantics.InstancePath)
    (σo : PathSubst) (x : Nat) (t : PTerm) :
    PTerm.interp ρo (bindO σo x t x) = PTerm.interp ρo t := by
  simp [bindO_eq]

/-- Interpretation is compatible with `bindO` at non-updated keys. -/
theorem interp_bindO_ne (ρo : SubstSemantics.LocalVar → SubstSemantics.InstancePath)
    (σo : PathSubst) (x y : Nat) (t : PTerm) (h : y ≠ x) :
    PTerm.interp ρo (bindO σo x t y) = PTerm.interp ρo (σo y) := by
  simp [bindO_ne, h]

private lemma bindV_interp_update
    (w : StructIR.Witness F) (σv : ValSubst F) (env : StructIR.LocalEnv F)
    (hInv : ∀ v, VTerm.interp w defaultValuation defaultPathValuation (σv v) = env v)
    (dest : Nat) (t : VTerm F) (val : F)
    (ht : VTerm.interp w defaultValuation defaultPathValuation t = val) :
    ∀ v, VTerm.interp w defaultValuation defaultPathValuation (bindV σv dest t v) =
      (StructIR.LocalEnv.update env dest val) v := by
  intro v
  by_cases hv : v = dest
  · subst v
    simp [bindV, StructIR.LocalEnv.update, ht]
  · simp [bindV, StructIR.LocalEnv.update, hv, hInv v]

private lemma bindO_interp_update
    (σo : PathSubst) (objEnv : StructIR.ObjEnv)
    (hInvO : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v)
    (dest : Nat) (t : PTerm) (path : StructIR.InstancePath)
    (ht : PTerm.interp defaultPathValuation t = path) :
    ∀ v, PTerm.interp defaultPathValuation (bindO σo dest t v) =
      (StructIR.ObjEnv.update objEnv dest path) v := by
  intro v
  by_cases hv : v = dest
  · subst v
    simp [bindO, StructIR.ObjEnv.update, ht]
  · simp [bindO, StructIR.ObjEnv.update, hv, hInvO v]

/-- Prefix a checked atom when the downstream result is successful. -/
def prependIfSuccess (a : Atom F) : Result (Atom F) → Result (Atom F)
  | Result.success trace => Result.success (a :: trace)
  | Result.failure checkedPrefix failed => Result.failure (a :: checkedPrefix) failed

omit [Field F] in
def maxVarStmt {i : Fin n} {nm : Nat} (stmt : StructIR.ConstrainStmt n i F nm) : Nat :=
  match stmt with
  | .feltAdd d s1 s2 | .feltSub d s1 s2
  | .feltMul d s1 s2 | .feltDiv d s1 s2 => max d (max s1 s2)
  | .feltNeg d s | .readMember d s _ => max d s
  | .feltConst d _ => d
  | .constrainEq s1 s2 => max s1 s2
  | .call _ args => args.foldl max 0

omit [Field F] in
def maxVarBody {i : Fin n} {nm : Nat}
    (body : List (StructIR.ConstrainStmt n i F nm)) : Nat :=
  body.foldl (fun acc s => max acc (maxVarStmt s)) 0

def renameStmt {i : Fin n} {nm : Nat} (ρ : Nat → Nat)
    (stmt : StructIR.ConstrainStmt n i F nm) : StructIR.ConstrainStmt n i F nm :=
  match stmt with
  | .feltAdd d s1 s2 => .feltAdd (ρ d) (ρ s1) (ρ s2)
  | .feltSub d s1 s2 => .feltSub (ρ d) (ρ s1) (ρ s2)
  | .feltMul d s1 s2 => .feltMul (ρ d) (ρ s1) (ρ s2)
  | .feltDiv d s1 s2 => .feltDiv (ρ d) (ρ s1) (ρ s2)
  | .feltNeg d s => .feltNeg (ρ d) (ρ s)
  | .feltConst d c => .feltConst (ρ d) c
  | .readMember d s member => .readMember (ρ d) (ρ s) member
  | .constrainEq s1 s2 => .constrainEq (ρ s1) (ρ s2)
  | .call target args => .call target (args.map ρ)

def renameBody {i : Fin n} {nm : Nat} (ρ : Nat → Nat)
    (body : List (StructIR.ConstrainStmt n i F nm)) : List (StructIR.ConstrainStmt n i F nm) :=
  body.map (renameStmt ρ)

omit [Field F] in
def freshenBody {i : Fin n} {nm : Nat} (nextFresh : Nat)
    (body : List (StructIR.ConstrainStmt n i F nm)) :
    List (StructIR.ConstrainStmt n i F nm) × Nat :=
  let ρ : Nat → Nat := fun v => nextFresh + v
  let blockSize := maxVarBody body + 1
  (renameBody ρ body, nextFresh + blockSize)

def freshMap (nextFresh : Nat) : Nat → Nat := fun v => nextFresh + v

/-- Every freshened variable index is at least `nextFresh`. -/
theorem freshMap_ge (nextFresh v : Nat) : nextFresh ≤ freshMap nextFresh v := by
  simp [freshMap]

/-- Freshening by left-addition is injective. -/
theorem freshMap_injective (nextFresh : Nat) : Function.Injective (freshMap nextFresh) := by
  intro a b h
  exact Nat.add_left_cancel h

omit [Field F] in
/-- Freshening never decreases the freshness counter. -/
theorem freshenBody_next_ge {i : Fin n} {nm : Nat}
    (nextFresh : Nat) (body : List (StructIR.ConstrainStmt n i F nm)) :
    nextFresh ≤ (freshenBody nextFresh body).2 := by
  simp [freshenBody]

omit [Field F] in
/-- Freshening always strictly advances the freshness counter. -/
theorem freshenBody_next_gt {i : Fin n} {nm : Nat}
    (nextFresh : Nat) (body : List (StructIR.ConstrainStmt n i F nm)) :
    nextFresh < (freshenBody nextFresh body).2 := by
  simp [freshenBody]

/-- Variables below `nextFresh` cannot equal freshened variables. -/
theorem fresh_old_disjoint (nextFresh x v : Nat) (hx : x < nextFresh) :
    x ≠ freshMap nextFresh v := by
  intro h
  have : nextFresh ≤ x := by simpa [h] using freshMap_ge nextFresh v
  omega

def bindParamsLoop (idx remaining : Nat) (args : List Nat) (ρ : Nat → Nat)
    (srcσv : ValSubst F) (srcσo : PathSubst)
    (σv : ValSubst F) (σo : PathSubst) : ValSubst F × PathSubst :=
  match remaining with
  | 0 => (σv, σo)
  | k + 1 =>
    let argTerm : VTerm F :=
      match args[idx]? with
      | some arg => srcσv arg
      | none => .const 0
    let pathTerm : PTerm :=
      match args[idx]? with
      | some arg => srcσo arg
      | none => .const []
    let σv' := bindV σv (ρ idx) argTerm
    let σo' := bindO σo (ρ idx) pathTerm
    bindParamsLoop (idx + 1) k args ρ srcσv srcσo σv' σo'

def bindParams (numParams : Nat) (args : List Nat) (ρ : Nat → Nat)
    (srcσv : ValSubst F) (srcσo : PathSubst) : ValSubst F × PathSubst :=
  bindParamsLoop 0 numParams args ρ srcσv srcσo VTerm.idSubst PTerm.idSubst

/--
Parameter binding preserves old variables (`x < nextFresh`) since all bindings
target freshened keys `nextFresh + idx`.
-/
theorem bindParamsLoop_preserve_old (idx remaining : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (σv : ValSubst F) (σo : PathSubst) (x : Nat) (hx : x < nextFresh) :
    (bindParamsLoop idx remaining args (freshMap nextFresh) srcσv srcσo σv σo).1 x = σv x ∧
      (bindParamsLoop idx remaining args (freshMap nextFresh) srcσv srcσo σv σo).2 x = σo x := by
  induction remaining generalizing idx σv σo with
  | zero =>
    constructor <;> simp [bindParamsLoop]
  | succ k ih =>
    have hne : x ≠ freshMap nextFresh idx := fresh_old_disjoint nextFresh x idx hx
    have hσv : bindV σv (freshMap nextFresh idx)
      (match args[idx]? with | some arg => srcσv arg | none => VTerm.const 0) x = σv x := by
      simp [bindV_ne, hne]
    have hσo : bindO σo (freshMap nextFresh idx)
      (match args[idx]? with | some arg => srcσo arg | none => PTerm.const []) x = σo x := by
      simp [bindO_ne, hne]
    have hRec := ih (idx + 1)
      (bindV σv (freshMap nextFresh idx)
        (match args[idx]? with | some arg => srcσv arg | none => VTerm.const 0))
      (bindO σo (freshMap nextFresh idx)
        (match args[idx]? with | some arg => srcσo arg | none => PTerm.const []))
    simpa [bindParamsLoop, hσv, hσo] using hRec

/-- Specialization of `bindParamsLoop_preserve_old` to identity initial substitutions. -/
theorem bindParams_preserve_old (numParams : Nat) (args : List Nat) (nextFresh : Nat)
    (srcσv : ValSubst F) (srcσo : PathSubst) (x : Nat) (hx : x < nextFresh) :
    (bindParams numParams args (freshMap nextFresh) srcσv srcσo).1 x = VTerm.var x ∧
      (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2 x = PTerm.var x := by
  simpa [bindParams] using bindParamsLoop_preserve_old 0 numParams args nextFresh
    srcσv srcσo VTerm.idSubst PTerm.idSubst x hx

/--
Generalization of `bindParamsLoop_preserve_old`: any variable strictly below
`nextFresh + idx` is preserved by `bindParamsLoop idx remaining ...`.
-/
theorem bindParamsLoop_preserve_below (idx remaining : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (σv : ValSubst F) (σo : PathSubst) (x : Nat) (hx : x < nextFresh + idx) :
    (bindParamsLoop idx remaining args (freshMap nextFresh) srcσv srcσo σv σo).1 x = σv x ∧
      (bindParamsLoop idx remaining args (freshMap nextFresh) srcσv srcσo σv σo).2 x = σo x := by
  induction remaining generalizing idx σv σo with
  | zero =>
    constructor <;> simp [bindParamsLoop]
  | succ k ih =>
    have hne : x ≠ freshMap nextFresh idx := by
      intro h
      have : x = nextFresh + idx := by simpa [freshMap] using h
      omega
    have hσv : bindV σv (freshMap nextFresh idx)
      (match args[idx]? with | some arg => srcσv arg | none => VTerm.const 0) x = σv x := by
      simp [bindV_ne, hne]
    have hσo : bindO σo (freshMap nextFresh idx)
      (match args[idx]? with | some arg => srcσo arg | none => PTerm.const []) x = σo x := by
      simp [bindO_ne, hne]
    have hx' : x < nextFresh + (idx + 1) := by omega
    have hRec := ih (idx + 1)
      (bindV σv (freshMap nextFresh idx)
        (match args[idx]? with | some arg => srcσv arg | none => VTerm.const 0))
      (bindO σo (freshMap nextFresh idx)
        (match args[idx]? with | some arg => srcσo arg | none => PTerm.const []))
      hx'
    simpa [bindParamsLoop, hσv, hσo] using hRec

/--
Lookup at a freshened parameter position after `bindParamsLoop`: for `idx ≤ v <
idx + remaining`, the loop's resulting substitutions at position `freshMap
nextFresh v` are exactly the argument-derived terms.
-/
theorem bindParamsLoop_get (idx remaining : Nat) (args : List Nat) (nextFresh : Nat)
    (srcσv : ValSubst F) (srcσo : PathSubst) (σv : ValSubst F) (σo : PathSubst)
    (v : Nat) (hv1 : idx ≤ v) (hv2 : v < idx + remaining) :
    (bindParamsLoop idx remaining args (freshMap nextFresh) srcσv srcσo σv σo).1
        (freshMap nextFresh v) =
      (match args[v]? with | some arg => srcσv arg | none => VTerm.const 0) ∧
    (bindParamsLoop idx remaining args (freshMap nextFresh) srcσv srcσo σv σo).2
        (freshMap nextFresh v) =
      (match args[v]? with | some arg => srcσo arg | none => PTerm.const []) := by
  induction remaining generalizing idx σv σo with
  | zero =>
    -- vacuous: hv1 ≤ v and hv2 < idx + 0 = idx is contradictory
    omega
  | succ k ih =>
    by_cases hv_eq : v = idx
    · subst hv_eq
      have hbelow : freshMap nextFresh v < nextFresh + (v + 1) := by
        simp [freshMap]
      have hpres := bindParamsLoop_preserve_below (v + 1) k args nextFresh srcσv srcσo
        (bindV σv (freshMap nextFresh v)
          (match args[v]? with | some arg => srcσv arg | none => VTerm.const 0))
        (bindO σo (freshMap nextFresh v)
          (match args[v]? with | some arg => srcσo arg | none => PTerm.const []))
        (freshMap nextFresh v) hbelow
      refine ⟨?_, ?_⟩
      · simp [bindParamsLoop, hpres.1, bindV_eq]
      · simp [bindParamsLoop, hpres.2, bindO_eq]
    · have hv1' : idx + 1 ≤ v := by omega
      have hv2' : v < (idx + 1) + k := by omega
      have hRec := ih (idx + 1)
        (bindV σv (freshMap nextFresh idx)
          (match args[idx]? with | some arg => srcσv arg | none => VTerm.const 0))
        (bindO σo (freshMap nextFresh idx)
          (match args[idx]? with | some arg => srcσo arg | none => PTerm.const []))
        hv1' hv2'
      simpa [bindParamsLoop] using hRec

/--
Lookup at a freshened parameter position after `bindParams`: for `v <
numParams`, the resulting substitutions at position `freshMap nextFresh v` are
the argument-derived value/path terms (from the caller's substitutions).
-/
theorem bindParams_get (numParams : Nat) (args : List Nat) (nextFresh : Nat)
    (srcσv : ValSubst F) (srcσo : PathSubst) (v : Nat) (hv : v < numParams) :
    (bindParams numParams args (freshMap nextFresh) srcσv srcσo).1 (freshMap nextFresh v) =
      (match args[v]? with | some arg => srcσv arg | none => VTerm.const 0) ∧
    (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2 (freshMap nextFresh v) =
      (match args[v]? with | some arg => srcσo arg | none => PTerm.const []) := by
  have hv2 : v < 0 + numParams := by simpa using hv
  simpa [bindParams] using bindParamsLoop_get 0 numParams args nextFresh srcσv srcσo
    VTerm.idSubst PTerm.idSubst v (Nat.zero_le _) hv2

/-- All path-variable occurrences in `t` are strictly below `bound`. -/
def varsBelowPTerm : PTerm → Nat → Prop
  | .var v, bound => v < bound
  | .const _, _ => True
  | .append base _, bound => varsBelowPTerm base bound

/-- All value-variable occurrences (including witness path variables) are below `bound`. -/
def varsBelowVTerm : VTerm F → Nat → Prop
  | .var v, bound => v < bound
  | .const _, _ => True
  | .add lhs rhs, bound => varsBelowVTerm lhs bound ∧ varsBelowVTerm rhs bound
  | .sub lhs rhs, bound => varsBelowVTerm lhs bound ∧ varsBelowVTerm rhs bound
  | .mul lhs rhs, bound => varsBelowVTerm lhs bound ∧ varsBelowVTerm rhs bound
  | .div lhs rhs, bound => varsBelowVTerm lhs bound ∧ varsBelowVTerm rhs bound
  | .neg arg, bound => varsBelowVTerm arg bound
  | .witnessAt path _, bound => varsBelowPTerm path bound

/-- All variable occurrences in this atom are below `bound`. -/
def varsBelowAtom : Atom F → Nat → Prop
  | .eq lhs rhs, bound => varsBelowVTerm lhs bound ∧ varsBelowVTerm rhs bound
  | .neZero term, bound => varsBelowVTerm term bound

theorem bindParams_preserve_old_pterm_subst (numParams : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (t : PTerm) (hBelow : varsBelowPTerm t nextFresh) :
    t.subst (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2 = t := by
  induction t with
  | var v =>
    have hv : v < nextFresh := hBelow
    have hPres := bindParams_preserve_old numParams args nextFresh srcσv srcσo v hv
    simpa [PTerm.subst] using hPres.2
  | const p => rfl
  | append base member ih =>
    simpa [varsBelowPTerm, PTerm.subst] using ih hBelow

theorem bindParams_preserve_old_vterm_subst (numParams : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (t : VTerm F) (hBelow : varsBelowVTerm t nextFresh) :
    t.subst (bindParams numParams args (freshMap nextFresh) srcσv srcσo).1
      (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2 = t := by
  induction t with
  | var v =>
    have hv : v < nextFresh := hBelow
    have hPres := bindParams_preserve_old numParams args nextFresh srcσv srcσo v hv
    simpa [VTerm.subst] using hPres.1
  | const c => rfl
  | add lhs rhs ihL ihR =>
    rcases hBelow with ⟨hL, hR⟩
    simp [VTerm.subst, ihL hL, ihR hR]
  | sub lhs rhs ihL ihR =>
    rcases hBelow with ⟨hL, hR⟩
    simp [VTerm.subst, ihL hL, ihR hR]
  | mul lhs rhs ihL ihR =>
    rcases hBelow with ⟨hL, hR⟩
    simp [VTerm.subst, ihL hL, ihR hR]
  | div lhs rhs ihL ihR =>
    rcases hBelow with ⟨hL, hR⟩
    simp [VTerm.subst, ihL hL, ihR hR]
  | neg arg ih =>
    simp [VTerm.subst, ih hBelow]
  | witnessAt path member =>
    simp [VTerm.subst,
      bindParams_preserve_old_pterm_subst numParams args nextFresh srcσv srcσo path hBelow]

theorem bindParams_preserve_old_atom_subst (numParams : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (a : Atom F) (hBelow : varsBelowAtom a nextFresh) :
    a.subst (bindParams numParams args (freshMap nextFresh) srcσv srcσo).1
      (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2 = a := by
  cases a with
  | eq lhs rhs =>
    rcases hBelow with ⟨hL, hR⟩
    simp [CAtom.subst,
      bindParams_preserve_old_vterm_subst numParams args nextFresh srcσv srcσo lhs hL,
      bindParams_preserve_old_vterm_subst numParams args nextFresh srcσv srcσo rhs hR]
  | neZero term =>
    simpa [CAtom.subst] using
      congrArg CAtom.neZero
        (bindParams_preserve_old_vterm_subst numParams args nextFresh srcσv srcσo term hBelow)

/--
Composed call-frame preservation theorem: if an atom only depends on variables
below `nextFresh`, then applying the call parameter bindings at freshened keys
(`nextFresh + idx`) does not change its interpreted meaning.

This is the key semantic consequence of disjointness + substitution-preservation
lemmas and is used to reason that inlined call setup does not perturb already
established checks on old variables.
-/
theorem bindParams_preserve_old_atom_interp (numParams : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (a : Atom F) (hBelow : varsBelowAtom a nextFresh)
    (w : StructIR.Witness F)
    (ρv : SubstSemantics.LocalVar → F)
    (ρo : SubstSemantics.LocalVar → SubstSemantics.InstancePath) :
    CAtom.interp w ρv ρo
      (a.subst (bindParams numParams args (freshMap nextFresh) srcσv srcσo).1
        (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2) =
      CAtom.interp w ρv ρo a := by
  simp [bindParams_preserve_old_atom_subst numParams args nextFresh srcσv srcσo a hBelow]

/-- Boolean checker version of `bindParams_preserve_old_atom_interp`. -/
theorem checkAtom_bindParams_preserve_old (numParams : Nat) (args : List Nat)
    (nextFresh : Nat) (srcσv : ValSubst F) (srcσo : PathSubst)
    (a : Atom F) (hBelow : varsBelowAtom a nextFresh)
    [DecidableEq F] (w : StructIR.Witness F) :
    checkAtom w
      (a.subst (bindParams numParams args (freshMap nextFresh) srcσv srcσo).1
        (bindParams numParams args (freshMap nextFresh) srcσv srcσo).2) =
      checkAtom w a := by
  have hSubst := bindParams_preserve_old_atom_subst
    numParams args nextFresh srcσv srcσo a hBelow
  simp [hSubst]

/--
Call setup package used by the `call` branch:
- freshen the callee body starting from `nextFresh`,
- bind (renamed) parameters from caller substitutions.
-/
def callSetup (m : StructIR.Module n F) (i : Fin n)
    (σv : ValSubst F) (σo : PathSubst) (nextFresh : Nat)
    (target : Fin i) (args : List Nat) :
    ValSubst F × PathSubst × List (StructIR.ConstrainStmt n
      ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩ F
      (m.structs ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩).members.length) × Nat := by
  let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
  let calleeBody := (m.structs j).constrain.body
  let ρ : Nat → Nat := freshMap nextFresh
  let (freshBody, nextFresh') := freshenBody nextFresh calleeBody
  let numParams := (m.structs j).constrain.numParams
  let (calleeσv, calleeσo) := bindParams numParams args ρ σv σo
  exact (calleeσv, calleeσo, freshBody, nextFresh')

/--
Full composed call-setup preservation theorem: atoms over pre-fresh variables
keep the same boolean check result after the entire call setup package.
-/
theorem checkAtom_callSetup_preserve_old
    [DecidableEq F]
    (m : StructIR.Module n F) (i : Fin n)
    (σv : ValSubst F) (σo : PathSubst) (nextFresh : Nat)
    (target : Fin i) (args : List Nat)
    (a : Atom F) (hBelow : varsBelowAtom a nextFresh)
    (w : StructIR.Witness F) :
    let setup := callSetup m i σv σo nextFresh target args
    checkAtom w (a.subst setup.1 setup.2.1) = checkAtom w a := by
  dsimp [callSetup]
  simp [checkAtom_bindParams_preserve_old, hBelow]

/--
Unfolded evaluator equation for the `.call` branch, factored through
`callSetup`. This is the call-branch evaluator theorem used by later
simulation-style proofs.
-/
/-
The call-branch evaluator theorem is established by the definition equation for
`evalConstrainBodyChecked` and the composed call-setup preservation lemmas
above. We keep the reusable packaged result at atom-check level:
`checkAtom_callSetup_preserve_old`.
-/

/-
Evaluation output threads current substitutions and freshness state together
with the checked result.
-/
structure EvalOut (F : Type) where
  σv : ValSubst F
  σo : PathSubst
  nextFresh : Nat
  res : Result (Atom F)

/--
Checked substitution evaluator for StructIR constrain bodies.

The evaluator is deterministic by construction and eager in checking emitted
atoms (`constrainEq`, `feltDiv` nonzero side condition).
-/
def evalConstrainBodyChecked [DecidableEq F] (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (σv : ValSubst F) (σo : PathSubst) (nextFresh : Nat)
    (stmts : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    EvalOut F :=
  match stmts with
  | [] => { σv := σv, σo := σo, nextFresh := nextFresh, res := Result.success [] }
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      let σv' := bindV σv dest (.add (σv src1) (σv src2))
      evalConstrainBodyChecked m w i σv' σo nextFresh rest
    | .feltSub dest src1 src2 =>
      let σv' := bindV σv dest (.sub (σv src1) (σv src2))
      evalConstrainBodyChecked m w i σv' σo nextFresh rest
    | .feltMul dest src1 src2 =>
      let σv' := bindV σv dest (.mul (σv src1) (σv src2))
      evalConstrainBodyChecked m w i σv' σo nextFresh rest
    | .feltDiv dest src1 src2 =>
      let den := σv src2
      let nz : Atom F := CAtom.neZero den
      if checkAtom w nz then
        let σv' := bindV σv dest (.div (σv src1) den)
        let out := evalConstrainBodyChecked m w i σv' σo nextFresh rest
        { out with res := prependIfSuccess nz out.res }
      else
        { σv := σv, σo := σo, nextFresh := nextFresh, res := Result.failure [] nz }
    | .feltNeg dest src =>
      let σv' := bindV σv dest (.neg (σv src))
      evalConstrainBodyChecked m w i σv' σo nextFresh rest
    | .feltConst dest c =>
      let σv' := bindV σv dest (.const c)
      evalConstrainBodyChecked m w i σv' σo nextFresh rest
    | .readMember dest self member =>
      let basePath := σo self
      let σv' := bindV σv dest (.witnessAt basePath member.val)
      let σo' := bindO σo dest (.append basePath member.val)
      evalConstrainBodyChecked m w i σv' σo' nextFresh rest
    | .constrainEq src1 src2 =>
      let eqAtom : Atom F := CAtom.eq (σv src1) (σv src2)
      if checkAtom w eqAtom then
        let out := evalConstrainBodyChecked m w i σv σo nextFresh rest
        { out with res := prependIfSuccess eqAtom out.res }
      else
        { σv := σv, σo := σo, nextFresh := nextFresh, res := Result.failure [] eqAtom }
    | .call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let ρ : Nat → Nat := fun v => nextFresh + v
      let (freshBody, nextFresh') := freshenBody nextFresh calleeBody
      let numParams := (m.structs j).constrain.numParams
      let (calleeσv, calleeσo) := bindParams numParams args ρ σv σo
      let callOut := evalConstrainBodyChecked m w j calleeσv calleeσo nextFresh' freshBody
      match callOut.res with
      | Result.failure checkedPrefix failed =>
        { σv := σv, σo := σo, nextFresh := nextFresh',
          res := Result.failure checkedPrefix failed }
      | Result.success callTrace =>
        let out := evalConstrainBodyChecked m w i σv σo nextFresh' rest
        { out with res := Result.appendPrefix callTrace out.res }
  termination_by (i, stmts.length)
  decreasing_by
    all_goals first
    | apply Prod.Lex.left; exact target.isLt
    | apply Prod.Lex.right; simp

/-- Unfolded equation for the `.call` branch of the checked evaluator. -/
theorem evalConstrainBodyChecked_call_eq
    [DecidableEq F]
    (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (σv : ValSubst F) (σo : PathSubst) (nextFresh : Nat)
    (target : Fin i) (args : List Nat)
    (rest : List (StructIR.ConstrainStmt n i F (m.structs i).members.length)) :
    evalConstrainBodyChecked m w i σv σo nextFresh (.call target args :: rest) =
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let calleeBody := (m.structs j).constrain.body
      let ρ : Nat → Nat := fun v => nextFresh + v
      let (freshBody, nextFresh') := freshenBody nextFresh calleeBody
      let numParams := (m.structs j).constrain.numParams
      let (calleeσv, calleeσo) := bindParams numParams args ρ σv σo
      let callOut := evalConstrainBodyChecked m w j calleeσv calleeσo nextFresh' freshBody
      match callOut.res with
      | Result.failure checkedPrefix failed =>
        { σv := σv, σo := σo, nextFresh := nextFresh',
          res := Result.failure checkedPrefix failed }
      | Result.success callTrace =>
        let out := evalConstrainBodyChecked m w i σv σo nextFresh' rest
        { out with res := Result.appendPrefix callTrace out.res } := by
  simp [evalConstrainBodyChecked]

/--
Initial value substitution: each local variable `v` maps to `.witnessAt (decode v)`,
matching the initial environment in `StructIR.satisfies` where `env v = w (decode v)`.
-/
def initValSubst : ValSubst F := fun v =>
  let (path, member) := VarIdEncoding.decode v
  .witnessAt (.const path) member
def initPathSubst : PathSubst := fun _ => .const []

/-- Top-level checked evaluation on the main constrain body. -/
def evalChecked [DecidableEq F] (w : StructIR.Witness F) (m : StructIR.Module (n + 1) F) :
    Result (Atom F) :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let initNextFresh := maxVarBody (m.structs mainIdx).constrain.body + 1
  (evalConstrainBodyChecked m w mainIdx initValSubst initPathSubst initNextFresh
    (m.structs mainIdx).constrain.body).res

/-- Success predicate for checked substitution evaluation. -/
def checkedSuccess [DecidableEq F] (w : StructIR.Witness F) (m : StructIR.Module (n + 1) F) :
    Prop :=
  ∃ trace, evalChecked w m = Result.success trace

open StructIR hiding LocalVar InstancePath Witness

/-- Helper: isSuccess predicate for Result. -/
private def Result.isSuccess {α : Type} : Result α → Prop
  | .success _ => True
  | .failure _ _ => False

private theorem prependIfSuccess_isSuccess {α : Type} (a : Atom α) (r : Result (Atom α)) :
    Result.isSuccess (prependIfSuccess a r) ↔ Result.isSuccess r := by
  cases r <;> simp only [prependIfSuccess, Result.isSuccess]

private theorem appendPrefix_isSuccess {α : Type} (pre : List (Atom α))
    (r : Result (Atom α)) : Result.isSuccess (Result.appendPrefix pre r) ↔ Result.isSuccess r := by
  cases r <;> simp only [Result.appendPrefix, Result.isSuccess]

/-- Reindexing a call-argument lookup commutes with post-composition by `ρ`. -/
lemma get_map_lemma (ρ : ℕ → ℕ) (args : List ℕ) (env : ℕ → F) (n : ℕ) :
    (match Option.map ρ (args[n]?) with | some a => env a | none => 0) =
    (match args[n]? with | some a => (env ∘ ρ) a | none => 0) := by
  induction args generalizing n with
  | nil => simp
  | cons a args ih => cases n with | zero => simp | succ n => simp [ih n]

/-- Object-environment version of `get_map_lemma`. -/
lemma get_map_lemma_obj (ρ : ℕ → ℕ) (args : List ℕ) (env : ℕ → List ℕ) (n : ℕ) :
    (match Option.map ρ (args[n]?) with | some a => env a | none => []) =
    (match args[n]? with | some a => (env ∘ ρ) a | none => []) := by
  induction args generalizing n with
  | nil => simp
  | cons a args ih => cases n with | zero => simp | succ n => simp [ih n]

set_option linter.unusedSectionVars false in
/-- Post-composing an updated local environment with an injective renaming. -/
lemma env_update_rename_comm (env : LocalEnv F) (dest : LocalVar) (val : F)
    (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ) :
    (env.update (ρ dest) val) ∘ ρ = LocalEnv.update (env ∘ ρ) dest val := by
  funext x; simp only [Function.comp_apply, LocalEnv.update]
  by_cases hx : x = dest
  · subst x; simp
  · have hne : ρ x ≠ ρ dest := by intro hEq; exact hx (hρ_inj hEq)
    simp [hx, hne]

/-- Object-environment version of `env_update_rename_comm`. -/
lemma objEnv_update_rename_comm (objEnv : ObjEnv) (dest : LocalVar) (path : InstancePath)
    (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ) :
    (objEnv.update (ρ dest) path) ∘ ρ = ObjEnv.update (objEnv ∘ ρ) dest path := by
  funext x; simp only [Function.comp_apply, ObjEnv.update]
  by_cases hx : x = dest
  · subst x; simp
  · have hne : ρ x ≠ ρ dest := by intro hEq; exact hx (hρ_inj hEq)
    simp [hx, hne]

set_option linter.flexible false in
/--
Renaming a constrain body by an injective map `ρ` commutes with evaluation,
provided both environments are post-composed with `ρ` on the unrenamed side.
-/
lemma evalConstrainBody_rename (m : Module n F) (w : Witness F) (i : Fin n)
    (env : LocalEnv F) (objEnv : ObjEnv) (ρ : Nat → Nat) (hρ_inj : Function.Injective ρ)
    (body : List (ConstrainStmt n i F (m.structs i).members.length)) :
    evalConstrainBody m w i env objEnv (renameBody ρ body) ↔
    evalConstrainBody m w i (env ∘ ρ) (objEnv ∘ ρ) body := by
  induction body generalizing env objEnv with
  | nil => simp [evalConstrainBody, renameBody]
  | cons stmt body ih =>
    rename_i ih; cases stmt with
    | feltAdd dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) + env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) + env (ρ src2))) objEnv)
    | feltSub dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) - env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) - env (ρ src2))) objEnv)
    | feltMul dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (env (ρ src1) * env (ρ src2)) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) * env (ρ src2))) objEnv)
    | feltDiv dest src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]; intro hnz
      simpa [env_update_rename_comm env dest (env (ρ src1) * (env (ρ src2))⁻¹) ρ hρ_inj] using
        (ih (env.update (ρ dest) (env (ρ src1) * (env (ρ src2))⁻¹)) objEnv)
    | feltNeg dest src =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest (-(env (ρ src))) ρ hρ_inj] using
        (ih (env.update (ρ dest) (-(env (ρ src)))) objEnv)
    | feltConst dest c =>
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest c ρ hρ_inj] using
        (ih (env.update (ρ dest) c) objEnv)
    | readMember dest self member =>
      let path := objEnv (ρ self); let val := w (path, member.val)
      simp [evalConstrainBody, renameBody, renameStmt]
      simpa [env_update_rename_comm env dest val ρ hρ_inj,
        objEnv_update_rename_comm objEnv dest (path ++ [member.val]) ρ hρ_inj,
        Function.comp_apply] using
        (ih (env.update (ρ dest) val) (objEnv.update (ρ dest) (path ++ [member.val])))
    | constrainEq src1 src2 =>
      simp [evalConstrainBody, renameBody, renameStmt]; intro h_eq
      simpa [renameBody] using (ih env objEnv)
    | call target args =>
      simp [evalConstrainBody, renameBody, renameStmt]
      have h_callee_env_eq :
        (fun param : Nat => match Option.map ρ args[param]? with | some a => env a | none => 0) =
        (fun param : Nat => match args[param]? with | some a => (env ∘ ρ) a | none => 0) := by
        apply funext; intro n; apply get_map_lemma ρ args env n
      have h_callee_objEnv_eq :
        (fun param : Nat =>
          match Option.map ρ args[param]? with
          | some a => objEnv a
          | none => []) =
        (fun param : Nat =>
          match args[param]? with
          | some a => (objEnv ∘ ρ) a
          | none => []) := by
        apply funext; intro n; apply get_map_lemma_obj ρ args objEnv n
      constructor
      · rintro ⟨hcall, h⟩
        refine ⟨h_callee_objEnv_eq ▸ h_callee_env_eq ▸ hcall, (ih env objEnv).mp h⟩
      · rintro ⟨hcall, h⟩
        refine ⟨h_callee_objEnv_eq.symm ▸ h_callee_env_eq.symm ▸ hcall, (ih env objEnv).mpr h⟩

private lemma list_all_true_of_mem {α : Type}
    (xs : List α) (p : α → Bool) (x : α)
    (hall : xs.all p = true) (hx : x ∈ xs) : p x = true := by
  induction xs generalizing x with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.all, Bool.and_eq_true] at hall
    rcases hall with ⟨hy, hys⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hy
    · exact ih _ hys hx

/-- Generalized form: if two local envs agree on the SSA-init set, and the
    body type-checks under SSA with that init, then evaluation is identical.

    The init set grows monotonically: each statement with a `dest` adds it.
    Reads of each statement are always in `init`, so env1 and env2 agree there;
    after an update at `dest` to the same value, the new envs agree on the
    extended init. The `call` case is handled by definitional equality:
    `calleeEnv` only reads `env` at positions in `args`, all of which are reads
    of the call (hence in `init`), so calleeEnv1 = calleeEnv2 as functions. -/
private lemma evalConstrainBody_env_agree_on_init_aux
    (m : Module n F) (w : StructIR.Witness F) (i : Fin n) :
    ∀ (body : List (ConstrainStmt n i F (m.structs i).members.length))
      (init : LocalVar → Bool)
      (env1 env2 : LocalEnv F) (objEnv : ObjEnv),
      StructIR.isSSA init body = true →
      (∀ v, init v = true → env1 v = env2 v) →
      (evalConstrainBody m w i env1 objEnv body ↔
        evalConstrainBody m w i env2 objEnv body) := by
  intro body
  induction body with
  | nil =>
    intro init env1 env2 objEnv _ _
    simp [evalConstrainBody]
  | cons stmt rest ih =>
    intro init env1 env2 objEnv hSSA hAgree
    simp only [StructIR.isSSA, Bool.and_eq_true] at hSSA
    obtain ⟨hReads, hSSA'⟩ := hSSA
    -- Agreement on every variable read by `stmt`.
    have hReadsAgree : ∀ v ∈ stmt.reads, env1 v = env2 v := by
      intro v hv
      exact hAgree v (list_all_true_of_mem _ _ _ hReads hv)
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 + env2 src2)) v =
          (env2.update dest (env2 src1 + env2 src2)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      exact ih _ _ _ _ hSSA'' hext
    | feltSub dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 - env2 src2)) v =
          (env2.update dest (env2 src1 - env2 src2)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      exact ih _ _ _ _ hSSA'' hext
    | feltMul dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 * env2 src2)) v =
          (env2.update dest (env2 src1 * env2 src2)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      exact ih _ _ _ _ hSSA'' hext
    | feltDiv dest src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs1, hs2]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (env2 src1 * (env2 src2)⁻¹)) v =
          (env2.update dest (env2 src1 * (env2 src2)⁻¹)) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      constructor
      · rintro ⟨hnz, hrest⟩
        exact ⟨hnz, (ih _ _ _ _ hSSA'' hext).mp hrest⟩
      · rintro ⟨hnz, hrest⟩
        exact ⟨hnz, (ih _ _ _ _ hSSA'' hext).mpr hrest⟩
    | feltNeg dest src =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs : env1 src = env2 src := hReadsAgree src rfl
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      simp only [evalConstrainBody, hs, true_and]
      have hext : ∀ v, (init v || v == dest) = true →
          (env1.update dest (-(env2 src))) v =
          (env2.update dest (-(env2 src))) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      exact ih _ _ _ _ hSSA'' hext
    | feltConst dest c =>
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      have hext : ∀ v, (fun x => init x || x == dest) v = true →
          (env1.update dest c) v = (env2.update dest c) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      simp only [evalConstrainBody, true_and]
      exact ih _ _ _ _ hSSA'' hext
    | readMember dest self member =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hself : env1 self = env2 self := hReadsAgree self rfl
      simp only [ConstrainStmt.dest, Bool.and_eq_true] at hSSA'
      obtain ⟨_, hSSA''⟩ := hSSA'
      -- objEnv is the same for both, so the read value is identical.
      have hval : w (objEnv self, member.val) = w (objEnv self, member.val) := rfl
      have hext : ∀ v, (fun x => init x || x == dest) v = true →
          (env1.update dest (w (objEnv self, member.val))) v =
          (env2.update dest (w (objEnv self, member.val))) v := by
        intro v hv
        simp only [Bool.or_eq_true, beq_iff_eq] at hv
        simp only [LocalEnv.update]
        rcases hv with hv | hv
        · by_cases heq : v = dest
          · subst heq; simp
          · simp only [beq_iff_eq, heq, if_false]; exact hAgree _ hv
        · subst hv; simp
      simp only [evalConstrainBody, true_and]
      exact ih _ _ _ _ hSSA'' hext
    | constrainEq src1 src2 =>
      simp only [ConstrainStmt.reads, List.mem_cons, List.not_mem_nil, or_false] at hReadsAgree
      have hs1 : env1 src1 = env2 src1 := hReadsAgree src1 (Or.inl rfl)
      have hs2 : env1 src2 = env2 src2 := hReadsAgree src2 (Or.inr rfl)
      simp only [ConstrainStmt.dest] at hSSA'
      simp only [evalConstrainBody, hs1, hs2]
      constructor
      · rintro ⟨heq, hrest⟩
        exact ⟨heq, (ih _ _ _ _ hSSA' hAgree).mp hrest⟩
      · rintro ⟨heq, hrest⟩
        exact ⟨heq, (ih _ _ _ _ hSSA' hAgree).mpr hrest⟩
    | call target args =>
      -- All args are reads, so they're in `init`, so env1 and env2 agree on them.
      have hargs : ∀ a ∈ args, env1 a = env2 a := by
        intro a ha
        exact hReadsAgree a (by simpa [ConstrainStmt.reads] using ha)
      -- The callee env constructed from args is identical for env1 and env2.
      have hCalleeEnv :
          (fun param : Nat =>
            match args[param]? with | some arg => env1 arg | none => (0 : F)) =
          (fun param : Nat =>
            match args[param]? with | some arg => env2 arg | none => (0 : F)) := by
        funext param
        cases h : args[param]? with
        | none => rfl
        | some arg =>
          have : arg ∈ args := List.mem_of_getElem? h
          exact hargs arg this
      simp only [ConstrainStmt.dest] at hSSA'
      simp only [evalConstrainBody]
      constructor
      · rintro ⟨hcall, hrest⟩
        refine ⟨?_, (ih _ _ _ _ hSSA' hAgree).mp hrest⟩
        exact hCalleeEnv ▸ hcall
      · rintro ⟨hcall, hrest⟩
        refine ⟨?_, (ih _ _ _ _ hSSA' hAgree).mpr hrest⟩
        exact hCalleeEnv.symm ▸ hcall

/-- If two local-variable environments agree on all parameter variables (those
    below `numParams`), and the body is in SSA form, then evaluation with
    either env (and the same objEnv) yields the same result. -/
lemma evalConstrainBody_env_agree_on_init
    (m : Module n F) (w : StructIR.Witness F) (i : Fin n)
    (env1 env2 : LocalEnv F) (objEnv : ObjEnv)
    (body : List (ConstrainStmt n i F (m.structs i).members.length))
    (hSSA : StructIR.isSSA (fun v => v < (m.structs i).constrain.numParams) body = true)
    (hAgree : ∀ v,
      (fun v => v < (m.structs i).constrain.numParams) v = true → env1 v = env2 v) :
    evalConstrainBody m w i env1 objEnv body ↔ evalConstrainBody m w i env2 objEnv body := by
  refine evalConstrainBody_env_agree_on_init_aux m w i body _ env1 env2 objEnv hSSA ?_
  intro v hv
  exact hAgree v (by simpa using hv)

private lemma mem_dropVar_iff (v x : Nat) (xs : List Nat) :
    x ∈ StructIR.dropVar v xs ↔ x ∈ xs ∧ x ≠ v := by
  unfold StructIR.dropVar
  simp [List.mem_filter]

private lemma mem_dropVar_of_mem_of_ne (v x : Nat) (xs : List Nat)
    (hx : x ∈ xs) (hneq : x ≠ v) : x ∈ StructIR.dropVar v xs := by
  exact (mem_dropVar_iff v x xs).2 ⟨hx, hneq⟩

private lemma mem_collectNeededArgs_of_mem (args needed : List Nat) (p arg : Nat)
    (hp : p ∈ needed) (harg : args[p]? = some arg) :
    arg ∈ StructIR.collectNeededArgs args needed := by
  exact (List.mem_filterMap).2 ⟨p, hp, harg⟩

/-- Boolean-membership ↔ propositional membership for `List`s of `Nat`. -/
private lemma list_contains_iff_mem (xs : List Nat) (x : Nat) :
    xs.contains x = true ↔ x ∈ xs := by
  simp

lemma evalConstrainBody_objEnv_agree_on_init
    (m : Module n F) (w : StructIR.Witness F) :
    ∀ (i : Fin n) (env : LocalEnv F) (objEnv1 objEnv2 : ObjEnv)
      (body : List (ConstrainStmt n i F (m.structs i).members.length)),
      (StructIR.objectInfo m.structs i body).1 = true →
      (∀ v, v ∈ (StructIR.objectInfo m.structs i body).2 → objEnv1 v = objEnv2 v) →
      (evalConstrainBody m w i env objEnv1 body ↔
        evalConstrainBody m w i env objEnv2 body) := by
  -- Strong induction on `i.val`.
  intro i
  induction hk : i.val using Nat.strong_induction_on generalizing i with
  | _ k ih_struct =>
    subst hk
    intro env objEnv1 objEnv2 body
    -- Induction on the body itself.
    induction body generalizing env objEnv1 objEnv2 with
    | nil =>
      intro _ _
      simp [evalConstrainBody]
    | cons stmt rest ih_rest =>
      intro hSafe hAgreeO
      cases stmt with
      | feltAdd dest src1 src2 =>
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨hSafeRest, hNotDest⟩ := hSafe
        have hDestNotIn : dest ∉ (StructIR.objectInfo m.structs i rest).2 := by
          intro hmem
          simp [hmem] at hNotDest
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo]
          rcases Decidable.eq_or_ne v dest with hvd | hvd
          · exact absurd (hvd ▸ hv) hDestNotIn
          · exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        simp only [evalConstrainBody, true_and]
        exact ih_rest _ _ _ hSafeRest hAgreeO'
      | feltSub dest src1 src2 =>
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨hSafeRest, hNotDest⟩ := hSafe
        have hDestNotIn : dest ∉ (StructIR.objectInfo m.structs i rest).2 := by
          intro hmem
          simp [hmem] at hNotDest
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo]
          rcases Decidable.eq_or_ne v dest with hvd | hvd
          · exact absurd (hvd ▸ hv) hDestNotIn
          · exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        simp only [evalConstrainBody, true_and]
        exact ih_rest _ _ _ hSafeRest hAgreeO'
      | feltMul dest src1 src2 =>
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨hSafeRest, hNotDest⟩ := hSafe
        have hDestNotIn : dest ∉ (StructIR.objectInfo m.structs i rest).2 := by
          intro hmem
          simp [hmem] at hNotDest
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo]
          rcases Decidable.eq_or_ne v dest with hvd | hvd
          · exact absurd (hvd ▸ hv) hDestNotIn
          · exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        simp only [evalConstrainBody, true_and]
        exact ih_rest _ _ _ hSafeRest hAgreeO'
      | feltDiv dest src1 src2 =>
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨hSafeRest, hNotDest⟩ := hSafe
        have hDestNotIn : dest ∉ (StructIR.objectInfo m.structs i rest).2 := by
          intro hmem
          simp [hmem] at hNotDest
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo]
          rcases Decidable.eq_or_ne v dest with hvd | hvd
          · exact absurd (hvd ▸ hv) hDestNotIn
          · exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        simp only [evalConstrainBody]
        constructor
        · rintro ⟨hnz, hrest⟩
          exact ⟨hnz, (ih_rest _ _ _ hSafeRest hAgreeO').mp hrest⟩
        · rintro ⟨hnz, hrest⟩
          exact ⟨hnz, (ih_rest _ _ _ hSafeRest hAgreeO').mpr hrest⟩
      | feltNeg dest src =>
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨hSafeRest, hNotDest⟩ := hSafe
        have hDestNotIn : dest ∉ (StructIR.objectInfo m.structs i rest).2 := by
          intro hmem
          simp [hmem] at hNotDest
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo]
          rcases Decidable.eq_or_ne v dest with hvd | hvd
          · exact absurd (hvd ▸ hv) hDestNotIn
          · exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        simp only [evalConstrainBody, true_and]
        exact ih_rest _ _ _ hSafeRest hAgreeO'
      | feltConst dest c =>
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨hSafeRest, hNotDest⟩ := hSafe
        have hDestNotIn : dest ∉ (StructIR.objectInfo m.structs i rest).2 := by
          intro hmem
          simp [hmem] at hNotDest
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo]
          rcases Decidable.eq_or_ne v dest with hvd | hvd
          · exact absurd (hvd ▸ hv) hDestNotIn
          · exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        simp only [evalConstrainBody, true_and]
        exact ih_rest _ _ _ hSafeRest hAgreeO'
      | readMember dest self member =>
        simp only [StructIR.objectInfo] at hSafe
        -- needs = self :: dropVar dest needsRest
        have hSelfMem : self ∈
            (StructIR.objectInfo m.structs i (.readMember dest self member :: rest)).2 := by
          simp [StructIR.objectInfo]
        have hSelfEq : objEnv1 self = objEnv2 self := hAgreeO self hSelfMem
        simp only [evalConstrainBody, true_and, hSelfEq]
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            (objEnv1.update dest (objEnv2 self ++ [member.val])) v =
            (objEnv2.update dest (objEnv2 self ++ [member.val])) v := by
          intro v hv
          simp only [ObjEnv.update]
          by_cases hvd : v = dest
          · subst hvd; simp
          · simp only [beq_iff_eq, hvd, if_false]
            apply hAgreeO
            simp only [StructIR.objectInfo, List.mem_cons]
            right
            exact mem_dropVar_of_mem_of_ne dest v _ hv hvd
        exact ih_rest _ _ _ hSafe hAgreeO'
      | constrainEq src1 src2 =>
        simp only [StructIR.objectInfo] at hSafe
        have hAgreeO' : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp [StructIR.objectInfo, hv]
        simp only [evalConstrainBody]
        constructor
        · rintro ⟨heq, hrest⟩
          exact ⟨heq, (ih_rest _ _ _ hSafe hAgreeO').mp hrest⟩
        · rintro ⟨heq, hrest⟩
          exact ⟨heq, (ih_rest _ _ _ hSafe hAgreeO').mpr hrest⟩
      | call target args =>
        set j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩ with hj_def
        have hj_lt : j.val < i.val := target.isLt
        -- Extract pieces of objectInfo for the call case.
        simp only [StructIR.objectInfo, Bool.and_eq_true] at hSafe
        obtain ⟨⟨hSafeRest, hSafeCallee⟩, hNeededAvail⟩ := hSafe
        -- needs(head :: rest) = collectNeededArgs args calleeNeeds ++ needsRest
        have hAgreeO_rest : ∀ v, v ∈ (StructIR.objectInfo m.structs i rest).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo, List.mem_append]
          exact Or.inr hv
        have hAgreeO_args : ∀ v,
            v ∈ StructIR.collectNeededArgs args (StructIR.objectInfo m.structs j
              (m.structs j).constrain.body).2 →
            objEnv1 v = objEnv2 v := by
          intro v hv
          apply hAgreeO
          simp only [StructIR.objectInfo, List.mem_append]
          exact Or.inl hv
        -- Apply struct IH to the callee body with new agreement.
        have ih_callee :
            ∀ (calleeObjEnv1 calleeObjEnv2 : ObjEnv),
              (∀ v, v ∈ (StructIR.objectInfo m.structs j (m.structs j).constrain.body).2 →
                calleeObjEnv1 v = calleeObjEnv2 v) →
              (evalConstrainBody m w j
                (fun param => match args[param]? with | some arg => env arg | none => 0)
                calleeObjEnv1 (m.structs j).constrain.body ↔
              evalConstrainBody m w j
                (fun param => match args[param]? with | some arg => env arg | none => 0)
                calleeObjEnv2 (m.structs j).constrain.body) := by
          intro coe1 coe2 hCAgree
          exact ih_struct j.val hj_lt j rfl _ coe1 coe2
            (m.structs j).constrain.body hSafeCallee hCAgree
        -- Build calleeObjEnv₁ and calleeObjEnv₂ as functions of args and objEnvᵢ.
        -- Then show they agree on calleeNeeds.
        have hCalleeAgree :
            ∀ param,
              param ∈ (StructIR.objectInfo m.structs j (m.structs j).constrain.body).2 →
              (fun param : Nat => match args[param]? with
                | some arg => objEnv1 arg
                | none => ([] : List Nat)) param =
              (fun param : Nat => match args[param]? with
                | some arg => objEnv2 arg
                | none => ([] : List Nat)) param := by
          intro param hparam
          -- neededArgsAvailable says args[param]? is some
          have hAvail : (args[param]?).isSome = true := by
            apply list_all_true_of_mem _ _ _ hNeededAvail hparam
          cases hap : args[param]? with
          | none => simp [hap] at hAvail
          | some arg =>
            have harg_in : arg ∈ StructIR.collectNeededArgs args
                (StructIR.objectInfo m.structs j (m.structs j).constrain.body).2 :=
              mem_collectNeededArgs_of_mem _ _ _ _ hparam hap
            have heq : objEnv1 arg = objEnv2 arg := hAgreeO_args arg harg_in
            simp [hap, heq]
        simp only [evalConstrainBody]
        constructor
        · rintro ⟨hcall, hrest⟩
          refine ⟨?_, (ih_rest _ _ _ hSafeRest hAgreeO_rest).mp hrest⟩
          exact (ih_callee _ _ hCalleeAgree).mp hcall
        · rintro ⟨hcall, hrest⟩
          refine ⟨?_, (ih_rest _ _ _ hSafeRest hAgreeO_rest).mpr hrest⟩
          exact (ih_callee _ _ hCalleeAgree).mpr hcall

/-- Main lemma: checked substitution success ↔ direct semantics success. -/
private lemma evalConstrainBodyChecked_success_iff_evalConstrainBody
    [DecidableEq F] (m : Module n F) (w : Witness F) (i : Fin n)
    (σv : ValSubst F) (σo : PathSubst) (env : LocalEnv F) (objEnv : ObjEnv)
    (nextFresh : Nat) (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hInv : ∀ v, VTerm.interp w defaultValuation defaultPathValuation (σv v) = env v)
    (hInvO : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v) :
    Result.isSuccess ((evalConstrainBodyChecked m w i σv σo nextFresh stmts).res) ↔
    evalConstrainBody m w i env objEnv stmts := by
  -- well-founded induction on (i.val, stmts.length)
  revert σv σo env objEnv nextFresh stmts hInv hInvO
  refine (Nat.strongRecOn (motive := fun (k : Nat) =>
    ∀ (i : Fin n), i.val = k →
    ∀ (σv : ValSubst F) (σo : PathSubst) (env : LocalEnv F) (objEnv : ObjEnv)
      (nextFresh : Nat) (stmts : List (ConstrainStmt n i F (m.structs i).members.length)),
    (∀ v, VTerm.interp w defaultValuation defaultPathValuation (σv v) = env v) →
    (∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v) →
    (Result.isSuccess ((evalConstrainBodyChecked m w i σv σo nextFresh stmts).res) ↔
    evalConstrainBody m w i env objEnv stmts))) i.val ?_ i rfl
  intro k ih_k i hi σv σo env objEnv nextFresh stmts hInv hInvO
  subst hi
  induction stmts generalizing σv σo env objEnv nextFresh with
  | nil =>
    simp [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
  | cons stmt rest ih_rest =>
    rename_i ih_rest
    cases stmt with
    | feltAdd dest src1 src2 =>
      simp only [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
      have hsrc1 : VTerm.interp w defaultValuation defaultPathValuation (σv src1) = env src1 := by
        simpa using hInv src1
      have hsrc2 : VTerm.interp w defaultValuation defaultPathValuation (σv src2) = env src2 := by
        simpa using hInv src2
      have hadd : VTerm.interp w defaultValuation defaultPathValuation (.add (σv src1) (σv src2)) =
          env src1 + env src2 := by
        simp [VTerm.interp, hsrc1, hsrc2]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.add (σv src1) (σv src2)) v) =
          (env.update dest (env src1 + env src2)) v :=
        bindV_interp_update w σv env hInv dest (.add (σv src1) (σv src2))
          (env src1 + env src2) hadd
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [true_and]
      exact ih_rest (bindV σv dest (.add (σv src1) (σv src2))) σo
        (env.update dest (env src1 + env src2)) objEnv nextFresh hInv' hInvO'
    | feltSub dest src1 src2 =>
      simp only [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
      have hsrc1 : VTerm.interp w defaultValuation defaultPathValuation (σv src1) = env src1 := by
        simpa using hInv src1
      have hsrc2 : VTerm.interp w defaultValuation defaultPathValuation (σv src2) = env src2 := by
        simpa using hInv src2
      have hsub : VTerm.interp w defaultValuation defaultPathValuation (.sub (σv src1) (σv src2)) =
          env src1 - env src2 := by
        simp [VTerm.interp, hsrc1, hsrc2]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.sub (σv src1) (σv src2)) v) =
          (env.update dest (env src1 - env src2)) v :=
        bindV_interp_update w σv env hInv dest (.sub (σv src1) (σv src2))
          (env src1 - env src2) hsub
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [true_and]
      exact ih_rest (bindV σv dest (.sub (σv src1) (σv src2))) σo
        (env.update dest (env src1 - env src2)) objEnv nextFresh hInv' hInvO'
    | feltMul dest src1 src2 =>
      simp only [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
      have hsrc1 : VTerm.interp w defaultValuation defaultPathValuation (σv src1) = env src1 := by
        simpa using hInv src1
      have hsrc2 : VTerm.interp w defaultValuation defaultPathValuation (σv src2) = env src2 := by
        simpa using hInv src2
      have hmul : VTerm.interp w defaultValuation defaultPathValuation (.mul (σv src1) (σv src2)) =
          env src1 * env src2 := by
        simp [VTerm.interp, hsrc1, hsrc2]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.mul (σv src1) (σv src2)) v) =
          (env.update dest (env src1 * env src2)) v :=
        bindV_interp_update w σv env hInv dest (.mul (σv src1) (σv src2))
          (env src1 * env src2) hmul
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [true_and]
      exact ih_rest (bindV σv dest (.mul (σv src1) (σv src2))) σo
        (env.update dest (env src1 * env src2)) objEnv nextFresh hInv' hInvO'
    | feltDiv dest src1 src2 =>
      have hsrc2 : VTerm.interp w defaultValuation defaultPathValuation (σv src2) = env src2 := by
        simpa using hInv src2
      set nz : Atom F := CAtom.neZero (σv src2) with hnzDef
      have hcheck_iff : checkAtom w nz = true ↔ env src2 ≠ 0 := by
        rw [checkAtom_true_iff, hnzDef, CAtom.interp]; simp [hsrc2]
      have hdiv : VTerm.interp w defaultValuation defaultPathValuation (.div (σv src1) (σv src2)) =
          env src1 * (env src2)⁻¹ := by
        simp [VTerm.interp, hInv src1, hsrc2]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.div (σv src1) (σv src2)) v) =
          (env.update dest (env src1 * (env src2)⁻¹)) v :=
        bindV_interp_update w σv env hInv dest (.div (σv src1) (σv src2))
          (env src1 * (env src2)⁻¹) hdiv
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [evalConstrainBodyChecked, evalConstrainBody]
      by_cases hcheck : checkAtom w nz = true
      · -- divisor nonzero: both checked and direct semantics proceed to rest.
        have hnz : env src2 ≠ 0 := hcheck_iff.mp hcheck
        have hrest_iff := ih_rest (bindV σv dest (.div (σv src1) (σv src2))) σo
          (env.update dest (env src1 * (env src2)⁻¹)) objEnv nextFresh hInv' hInvO'
        have hcheck' : checkAtom w (CAtom.neZero (σv src2)) = true := by
          simpa [hnzDef] using hcheck
        rw [if_pos hcheck']
        simp only [prependIfSuccess_isSuccess]
        rw [hrest_iff]
        exact (and_iff_right hnz).symm
      · -- divisor zero: checked semantics fails, direct semantics has False ∧ _.
        have hnz0 : env src2 = 0 := by
          by_contra h
          exact hcheck (hcheck_iff.mpr h)
        have hcheck' : ¬ (checkAtom w (CAtom.neZero (σv src2)) = true) := by
          simpa [hnzDef] using hcheck
        rw [if_neg hcheck']
        simp [Result.isSuccess, hnz0]
    | feltNeg dest src =>
      simp only [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
      have hsrc : VTerm.interp w defaultValuation defaultPathValuation (σv src) = env src := by
        simpa using hInv src
      have hneg : VTerm.interp w defaultValuation defaultPathValuation
          (.neg (σv src)) = -(env src) := by
        simp [VTerm.interp, hsrc]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.neg (σv src)) v) = (env.update dest (-(env src))) v :=
        bindV_interp_update w σv env hInv dest (.neg (σv src)) (-(env src)) hneg
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [true_and]
      exact ih_rest (bindV σv dest (.neg (σv src))) σo
        (env.update dest (-(env src))) objEnv nextFresh hInv' hInvO'
    | feltConst dest c =>
      simp only [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.const c) v) = (env.update dest c) v :=
        bindV_interp_update w σv env hInv dest (.const c) c (by simp [VTerm.interp])
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [true_and]
      exact ih_rest (bindV σv dest (.const c)) σo (env.update dest c) objEnv nextFresh hInv' hInvO'
    | readMember dest self member =>
      simp only [evalConstrainBodyChecked, evalConstrainBody, Result.isSuccess]
      have hbase : PTerm.interp defaultPathValuation (σo self) = objEnv self := by
        simpa using hInvO self
      have hpath_val : VTerm.interp w defaultValuation defaultPathValuation
          (.witnessAt (σo self) member.val)
        = w (objEnv self, member.val) := by
        simp [VTerm.interp, hbase]
      have hInv' : ∀ v, VTerm.interp w defaultValuation defaultPathValuation
          (bindV σv dest (.witnessAt (σo self) member.val) v) =
          (env.update dest (w (objEnv self, member.val))) v :=
        bindV_interp_update w σv env hInv dest (.witnessAt (σo self) member.val)
          (w (objEnv self, member.val)) hpath_val
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation
          (bindO σo dest (.append (σo self) member.val) v) =
          (objEnv.update dest (objEnv self ++ [member.val])) v :=
        bindO_interp_update σo objEnv hInvO dest (.append (σo self) member.val)
          (objEnv self ++ [member.val]) (by simp [PTerm.interp, hbase])
      simp only [true_and]
      exact ih_rest (bindV σv dest (.witnessAt (σo self) member.val))
        (bindO σo dest (.append (σo self) member.val))
        (env.update dest (w (objEnv self, member.val)))
        (objEnv.update dest (objEnv self ++ [member.val])) nextFresh hInv' hInvO'
    | constrainEq src1 src2 =>
      have hsrc1 : VTerm.interp w defaultValuation defaultPathValuation (σv src1) = env src1 := by
        simpa using hInv src1
      have hsrc2 : VTerm.interp w defaultValuation defaultPathValuation (σv src2) = env src2 := by
        simpa using hInv src2
      set eqAtom : Atom F := CAtom.eq (σv src1) (σv src2) with heqAtomDef
      have hcheck_iff : checkAtom w eqAtom = true ↔ env src1 = env src2 := by
        rw [checkAtom_true_iff, heqAtomDef, CAtom.interp]
        simp only [hsrc1, hsrc2]
      have hInvO' : ∀ v, PTerm.interp defaultPathValuation (σo v) = objEnv v := hInvO
      simp only [evalConstrainBodyChecked, evalConstrainBody]
      by_cases hcheck : checkAtom w eqAtom = true
      · -- equality holds: both checked and direct semantics proceed to rest.
        have heq : env src1 = env src2 := hcheck_iff.mp hcheck
        have hrest_iff := ih_rest σv σo env objEnv nextFresh hInv hInvO'
        have hcheck' : checkAtom w (CAtom.eq (σv src1) (σv src2)) = true := by
          simpa [heqAtomDef] using hcheck
        rw [if_pos hcheck']
        simp only [prependIfSuccess_isSuccess]
        rw [hrest_iff]
        exact (and_iff_right heq).symm
      · -- equality fails: checked semantics fails, direct has False ∧ _.
        have hne : env src1 ≠ env src2 := by
          intro h
          exact hcheck (hcheck_iff.mpr h)
        have hcheck' : ¬ (checkAtom w (CAtom.eq (σv src1) (σv src2)) = true) := by
          simpa [heqAtomDef] using hcheck
        rw [if_neg hcheck']
        simp [Result.isSuccess, hne]
    | call target args =>
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      have hj_lt_i : j.val < i.val := target.isLt
      let calleeBody := (m.structs j).constrain.body
      let ρ : Nat → Nat := fun v => nextFresh + v
      let freshened := freshenBody nextFresh calleeBody
      let numParams := (m.structs j).constrain.numParams
      let calleePair := bindParams numParams args ρ σv σo
      let calleeσv := calleePair.1
      let calleeσo := calleePair.2
      let callOut := evalConstrainBodyChecked m w j calleeσv calleeσo freshened.2 freshened.1
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      have h_freshBody_eq : freshened.1 = renameBody ρ calleeBody := by rfl
      have hρ_inj : Function.Injective ρ := by
        intro a b h
        exact Nat.add_left_cancel h
      -- invariant for calleeσv, calleeσo
      let calleeEnv' : LocalEnv F := fun v =>
        VTerm.interp w defaultValuation defaultPathValuation (calleeσv v)
      let calleeObjEnv' : ObjEnv := fun v =>
        PTerm.interp defaultPathValuation (calleeσo v)
      have hCalleeInv' : ∀ v,
          VTerm.interp w defaultValuation defaultPathValuation (calleeσv v) = calleeEnv' v := by
        intro v; rfl
      have hCalleeInvO' : ∀ v,
          PTerm.interp defaultPathValuation (calleeσo v) = calleeObjEnv' v := by
        intro v; rfl
      have h_callee_iff := ih_k j.val hj_lt_i j rfl calleeσv calleeσo calleeEnv' calleeObjEnv'
        freshened.2 freshened.1 hCalleeInv' hCalleeInvO'
      have h_rename : evalConstrainBody m w j calleeEnv' calleeObjEnv' freshened.1 ↔
          evalConstrainBody m w j (calleeEnv' ∘ ρ) (calleeObjEnv' ∘ ρ) calleeBody := by
        rw [h_freshBody_eq]
        exact evalConstrainBody_rename m w j calleeEnv' calleeObjEnv' ρ hρ_inj calleeBody
      have h_param_agree : ∀ v, v < numParams → (calleeEnv' ∘ ρ) v = calleeEnv v := by
        intro v hv
        have hget := bindParams_get numParams args nextFresh σv σo v hv
        have hval : calleeσv (ρ v) =
            (match args[v]? with | some arg => σv arg | none => VTerm.const 0) := by
          simpa [calleeσv, calleePair, ρ, freshMap] using hget.1
        dsimp [Function.comp, calleeEnv']
        rw [hval]
        cases harg : args[v]? with
        | none =>
          simp [calleeEnv, harg, VTerm.interp]
        | some arg =>
          simp [calleeEnv, harg, hInv]
      have h_param_agreeO : ∀ v, v < numParams → (calleeObjEnv' ∘ ρ) v = calleeObjEnv v := by
        intro v hv
        have hget := bindParams_get numParams args nextFresh σv σo v hv
        have hpath : calleeσo (ρ v) =
            (match args[v]? with | some arg => σo arg | none => PTerm.const []) := by
          simpa [calleeσo, calleePair, ρ, freshMap] using hget.2
        dsimp [Function.comp, calleeObjEnv']
        rw [hpath]
        cases harg : args[v]? with
        | none =>
          simp [calleeObjEnv, harg, PTerm.interp]
        | some arg =>
          simp [calleeObjEnv, harg, hInvO]
      have hCalleeSSA : StructIR.isSSA (fun v => v < numParams) calleeBody = true := by
        simpa [numParams, calleeBody] using m.all_ssa j
      have hCalleeObj : StructIR.objectSafe m.structs j (fun v => v < numParams) calleeBody =
          true := by
        simpa [numParams, calleeBody] using m.all_objSafe j
      have hCalleeObjSafe : (StructIR.objectInfo m.structs j calleeBody).1 = true := by
        have h' : (StructIR.objectInfo m.structs j calleeBody).1 = true ∧
            (StructIR.objectInfo m.structs j calleeBody).2.all (fun v => v < numParams) = true := by
          simpa [StructIR.objectSafe, Bool.and_eq_true] using hCalleeObj
        exact h'.1
      have hCalleeObjAll : ∀ x ∈ (StructIR.objectInfo m.structs j calleeBody).2,
          x < numParams := by
        have h' : (StructIR.objectInfo m.structs j calleeBody).1 = true ∧
            (StructIR.objectInfo m.structs j calleeBody).2.all (fun v => v < numParams) = true := by
          simpa [StructIR.objectSafe, Bool.and_eq_true] using hCalleeObj
        intro x hx
        simpa using (list_all_true_of_mem _ _ x h'.2 hx)
      have h_env_agree : evalConstrainBody m w j (calleeEnv' ∘ ρ) (calleeObjEnv' ∘ ρ) calleeBody ↔
          evalConstrainBody m w j calleeEnv (calleeObjEnv' ∘ ρ) calleeBody := by
        apply evalConstrainBody_env_agree_on_init m w j
          (calleeEnv' ∘ ρ) calleeEnv (calleeObjEnv' ∘ ρ) calleeBody hCalleeSSA
        intro v hv
        exact h_param_agree v (by simpa [numParams] using hv)
      have h_obj_agree : evalConstrainBody m w j calleeEnv (calleeObjEnv' ∘ ρ) calleeBody ↔
          evalConstrainBody m w j calleeEnv calleeObjEnv calleeBody := by
        apply evalConstrainBody_objEnv_agree_on_init m w j
          calleeEnv (calleeObjEnv' ∘ ρ) calleeObjEnv
          calleeBody hCalleeObjSafe
        intro v hv
        have hv' : v < numParams := hCalleeObjAll v hv
        exact h_param_agreeO v hv'
      have h_callee_eval_iff : Result.isSuccess callOut.res ↔
          evalConstrainBody m w j calleeEnv calleeObjEnv calleeBody := by
        rw [h_callee_iff, h_rename, h_env_agree, h_obj_agree]
      have h_rest_iff : Result.isSuccess
          ((evalConstrainBodyChecked m w i σv σo freshened.2 rest).res) ↔
          evalConstrainBody m w i env objEnv rest :=
        ih_rest σv σo env objEnv freshened.2 hInv hInvO
      rw [evalConstrainBodyChecked_call_eq]
      dsimp [callOut, calleeσv, calleeσo, calleePair, calleeBody, freshened, numParams, ρ, j]
      simp only [evalConstrainBody]
      cases hCallRes : callOut.res with
      | failure checkedPrefix failed =>
        have hCallFail : ¬ Result.isSuccess callOut.res := by
          simp [hCallRes, Result.isSuccess]
        have hCallProp : ¬ evalConstrainBody m w j calleeEnv calleeObjEnv calleeBody := by
          intro h
          exact hCallFail (h_callee_eval_iff.mpr h)
        have hCallProp' : ¬ evalConstrainBody m w ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
            (fun param => match args[param]? with | some arg => env arg | none => 0)
            (fun param => match args[param]? with | some arg => objEnv arg | none => [])
            (m.structs ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩).constrain.body := by
          simpa [j, calleeEnv, calleeObjEnv, calleeBody] using hCallProp
        have hFalse : ¬ (
            evalConstrainBody m w ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
              (fun param => match args[param]? with | some arg => env arg | none => 0)
              (fun param => match args[param]? with | some arg => objEnv arg | none => [])
              (m.structs ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩).constrain.body ∧
            evalConstrainBody m w i env objEnv rest) := by
          intro h
          exact hCallProp' h.1
        simp only [Result.isSuccess]
        -- exact (iff_false_intro hFalse).symm
        simpa [Result.isSuccess] using (iff_false_intro hFalse).symm
      | success callTrace =>
        have hCallSucc : Result.isSuccess callOut.res := by
          simp [hCallRes, Result.isSuccess]
        have hCallProp : evalConstrainBody m w j calleeEnv calleeObjEnv calleeBody := by
          exact h_callee_eval_iff.mp hCallSucc
        have hCallProp' : evalConstrainBody m w ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
            (fun param => match args[param]? with | some arg => env arg | none => 0)
            (fun param => match args[param]? with | some arg => objEnv arg | none => [])
            (m.structs ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩).constrain.body := by
          simpa [j, calleeEnv, calleeObjEnv, calleeBody] using hCallProp
        rw [appendPrefix_isSuccess, h_rest_iff]
        constructor
        · intro h
          exact ⟨hCallProp', h⟩
        · intro h
          exact h.2

theorem checkedSuccess_iff_satisfies [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module (n + 1) F) :
    checkedSuccess w m ↔ StructIR.satisfies (n := n) w m := by
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainBody := (m.structs mainIdx).constrain.body
  let initNextFresh := maxVarBody mainBody + 1
  let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
  have hInitInv : ∀ v, VTerm.interp w defaultValuation defaultPathValuation (initValSubst v) =
      (fun k => w (VarIdEncoding.decode k)) v := by
    intro v
    simp [initValSubst, VTerm.interp, PTerm.interp, VarIdEncoding.decode]
  have hInitInvO : ∀ v, PTerm.interp defaultPathValuation (initPathSubst v) = initObjEnv v := by
    intro v
    simp [initPathSubst, initObjEnv, PTerm.interp, ObjEnv.update]
  constructor
  · intro ⟨trace, h⟩
    have h_success : Result.isSuccess
        ((evalConstrainBodyChecked m w mainIdx initValSubst initPathSubst
          initNextFresh mainBody).res) := by
      have h' : (evalConstrainBodyChecked m w mainIdx initValSubst initPathSubst
        initNextFresh mainBody).res = Result.success trace := by
        simpa [evalChecked] using h
      simp [h', Result.isSuccess]
    have h_main := (evalConstrainBodyChecked_success_iff_evalConstrainBody m w mainIdx
      initValSubst initPathSubst (fun k => w (VarIdEncoding.decode k)) initObjEnv
      initNextFresh mainBody hInitInv hInitInvO).mp h_success
    have h_satisfies : StructIR.satisfies (n := n) w m := by
      unfold StructIR.satisfies
      simpa [initObjEnv] using h_main
    exact h_satisfies
  · intro h_satisfies
    unfold StructIR.satisfies at h_satisfies
    have h_main : evalConstrainBody m w mainIdx (fun k => w (VarIdEncoding.decode k))
        initObjEnv mainBody := by
      simpa [initObjEnv] using h_satisfies
    have h_success : Result.isSuccess
        ((evalConstrainBodyChecked m w mainIdx initValSubst initPathSubst
          initNextFresh mainBody).res) :=
      (evalConstrainBodyChecked_success_iff_evalConstrainBody m w mainIdx
        initValSubst initPathSubst (fun k => w (VarIdEncoding.decode k)) initObjEnv
        initNextFresh mainBody hInitInv hInitInvO).mpr h_main
    have h_trace : ∃ trace, (evalConstrainBodyChecked m w mainIdx initValSubst initPathSubst
        initNextFresh mainBody).res = Result.success trace := by
      have h_success' := h_success
      cases h' : (evalConstrainBodyChecked m w mainIdx initValSubst initPathSubst
        initNextFresh mainBody).res with
      | success trace =>
        exact ⟨trace, rfl⟩
      | failure checkedPrefix failed =>
        simp [h', Result.isSuccess] at h_success'
    unfold checkedSuccess
    simpa [evalChecked] using h_trace

theorem checkedSuccess_of_satisfies [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module (n + 1) F)
    (h : StructIR.satisfies (n := n) w m) : checkedSuccess w m :=
  (checkedSuccess_iff_satisfies (n := n) w m).2 h

theorem satisfies_of_checkedSuccess [DecidableEq F]
    (w : StructIR.Witness F) (m : StructIR.Module (n + 1) F)
    (h : checkedSuccess w m) : StructIR.satisfies (n := n) w m :=
  (checkedSuccess_iff_satisfies (n := n) w m).1 h

def Language (n : Nat) (F : Type) [Field F] : _root_.Language StructIR.VarId F where
  Program := StructIR.Module (n + 1) F
  satisfies := fun w m => StructIR.satisfies (n := n) w m

end StructIRSubst
