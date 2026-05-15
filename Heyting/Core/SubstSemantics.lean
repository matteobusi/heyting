import Heyting.Core.Language

/-!
Core symbolic substitution machinery shared by substitution-based checked semantics.

The design separates:
- value terms (`VTerm`) for field expressions,
- path terms (`PTerm`) for instance-path expressions,
- atomic constraints (`CAtom`) for checked traces.

Interpretation functions map symbolic objects back to concrete values/paths under
a witness and concrete variable assignments.
-/
namespace SubstSemantics

/-- Local variable identifiers in substitution semantics. -/
abbrev LocalVar := Nat
/-- Struct instance paths. -/
abbrev InstancePath := List Nat
/-- Witness space used by path-based witness atoms. -/
abbrev Witness (F : Type) := (InstancePath × Nat) → F

/-- Symbolic path terms. -/
inductive PTerm where
  | var (v : LocalVar)
  | const (p : InstancePath)
  | append (base : PTerm) (member : Nat)
  deriving Repr, DecidableEq

/-- Path substitutions map locals to path terms. -/
abbrev PathSubst := LocalVar → PTerm

/-- Apply a path substitution to a symbolic path term. -/
def PTerm.subst (σo : PathSubst) : PTerm → PTerm
  | .var v => σo v
  | .const p => .const p
  | .append base member => .append (subst σo base) member

/-- Interpret a symbolic path term under a concrete object environment. -/
def PTerm.interp (ρo : LocalVar → InstancePath) : PTerm → InstancePath
  | .var v => ρo v
  | .const p => p
  | .append base member => interp ρo base ++ [member]

/-- Identity path substitution. -/
def PTerm.idSubst : PathSubst := fun v => .var v

/-- Compose two path substitutions left-to-right. -/
def PTerm.composeSubst (σo₁ σo₂ : PathSubst) : PathSubst :=
  fun v => (σo₁ v).subst σo₂

/-- Override a path substitution at one local variable. -/
def bindO (σo : PathSubst) (x : LocalVar) (t : PTerm) : PathSubst :=
  fun y => if y == x then t else σo y

theorem PTerm.subst_id (t : PTerm) : t.subst PTerm.idSubst = t := by
  induction t with
  | var v => rfl
  | const p => rfl
  | append base member ih => simp [PTerm.subst, ih]

theorem PTerm.subst_subst (σo₁ σo₂ : PathSubst) (t : PTerm) :
    (t.subst σo₁).subst σo₂ = t.subst (PTerm.composeSubst σo₁ σo₂) := by
  induction t with
  | var v => rfl
  | const p => rfl
  | append base member ih => simp [PTerm.subst, ih]

theorem PTerm.interp_subst (σo : PathSubst) (ρo ρo' : LocalVar → InstancePath)
    (hσo : ∀ v, PTerm.interp ρo (σo v) = ρo' v) (t : PTerm) :
    PTerm.interp ρo (t.subst σo) = PTerm.interp ρo' t := by
  induction t with
  | var v => simpa [PTerm.subst, PTerm.interp] using hσo v
  | const p => rfl
  | append base member ih => simp [PTerm.subst, PTerm.interp, ih]

/-! ## Symbolic value terms -/

/-- Symbolic value terms over field `F`. -/
inductive VTerm (F : Type) where
  | var (v : LocalVar)
  | const (c : F)
  | add (lhs rhs : VTerm F)
  | sub (lhs rhs : VTerm F)
  | mul (lhs rhs : VTerm F)
  | div (lhs rhs : VTerm F)
  | neg (arg : VTerm F)
  | witnessAt (path : PTerm) (member : Nat)
  deriving Repr, DecidableEq

/-- Value substitutions map locals to value terms. -/
abbrev ValSubst (F : Type) := LocalVar → VTerm F

/-- Apply value/path substitutions to a symbolic value term. -/
def VTerm.subst {F : Type} (σv : ValSubst F) (σo : PathSubst) : VTerm F → VTerm F
  | .var v => σv v
  | .const c => .const c
  | .add lhs rhs => .add (subst σv σo lhs) (subst σv σo rhs)
  | .sub lhs rhs => .sub (subst σv σo lhs) (subst σv σo rhs)
  | .mul lhs rhs => .mul (subst σv σo lhs) (subst σv σo rhs)
  | .div lhs rhs => .div (subst σv σo lhs) (subst σv σo rhs)
  | .neg arg => .neg (subst σv σo arg)
  | .witnessAt path member => .witnessAt (path.subst σo) member

/-- Interpret a symbolic value term under concrete value/object environments. -/
def VTerm.interp {F : Type} [Field F] (w : Witness F) (ρv : LocalVar → F)
    (ρo : LocalVar → InstancePath) : VTerm F → F
  | .var v => ρv v
  | .const c => c
  | .add lhs rhs => interp w ρv ρo lhs + interp w ρv ρo rhs
  | .sub lhs rhs => interp w ρv ρo lhs - interp w ρv ρo rhs
  | .mul lhs rhs => interp w ρv ρo lhs * interp w ρv ρo rhs
  | .div lhs rhs => interp w ρv ρo lhs * (interp w ρv ρo rhs)⁻¹
  | .neg arg => -(interp w ρv ρo arg)
  | .witnessAt path member => w (PTerm.interp ρo path, member)

/-- Identity value substitution. -/
def VTerm.idSubst {F : Type} : ValSubst F := fun v => .var v

/-- Compose value substitutions, threading the path substitution for witness reads. -/
def VTerm.composeValSubst {F : Type} (σv₁ : ValSubst F)
    (σv₂ : ValSubst F) (σo₂ : PathSubst) : ValSubst F :=
  fun v => (σv₁ v).subst σv₂ σo₂

/-- Override a value substitution at one local variable. -/
def bindV {F : Type} (σv : ValSubst F) (x : LocalVar) (t : VTerm F) : ValSubst F :=
  fun y => if y == x then t else σv y

theorem VTerm.subst_id {F : Type} (t : VTerm F) :
    t.subst VTerm.idSubst PTerm.idSubst = t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | add lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | sub lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | mul lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | div lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | neg arg ih => simp [VTerm.subst, ih]
  | witnessAt path member => simp [VTerm.subst, PTerm.subst_id]

theorem VTerm.subst_subst {F : Type} (σv₁ σv₂ : ValSubst F) (σo₁ σo₂ : PathSubst)
    (t : VTerm F) :
    (t.subst σv₁ σo₁).subst σv₂ σo₂ =
      t.subst (VTerm.composeValSubst σv₁ σv₂ σo₂) (PTerm.composeSubst σo₁ σo₂) := by
  induction t with
  | var v => rfl
  | const c => rfl
  | add lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | sub lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | mul lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | div lhs rhs ihL ihR => simp [VTerm.subst, ihL, ihR]
  | neg arg ih => simp [VTerm.subst, ih]
  | witnessAt path member =>
    simp [VTerm.subst, PTerm.subst_subst]

theorem VTerm.interp_subst {F : Type} [Field F] (w : Witness F)
    (σv : ValSubst F) (σo : PathSubst)
    (ρv ρv' : LocalVar → F) (ρo ρo' : LocalVar → InstancePath)
    (hσv : ∀ v, VTerm.interp w ρv ρo (σv v) = ρv' v)
    (hσo : ∀ v, PTerm.interp ρo (σo v) = ρo' v)
    (t : VTerm F) :
    VTerm.interp w ρv ρo (t.subst σv σo) = VTerm.interp w ρv' ρo' t := by
  induction t with
  | var v => simpa [VTerm.subst, VTerm.interp] using hσv v
  | const c => rfl
  | add lhs rhs ihL ihR => simp [VTerm.subst, VTerm.interp, ihL, ihR]
  | sub lhs rhs ihL ihR => simp [VTerm.subst, VTerm.interp, ihL, ihR]
  | mul lhs rhs ihL ihR => simp [VTerm.subst, VTerm.interp, ihL, ihR]
  | div lhs rhs ihL ihR => simp [VTerm.subst, VTerm.interp, ihL, ihR]
  | neg arg ih => simp [VTerm.subst, VTerm.interp, ih]
  | witnessAt path member =>
    simpa [VTerm.subst, VTerm.interp] using congrArg (fun p => w (p, member))
      (PTerm.interp_subst σo ρo ρo' hσo path)

/-! ## Atomic constraints -/

/-- Atomic checked constraints emitted by substitution execution. -/
inductive CAtom (F : Type) where
  | eq (lhs rhs : VTerm F)
  | neZero (term : VTerm F)
  deriving Repr, DecidableEq

/-- Apply substitutions to an atomic checked constraint. -/
def CAtom.subst {F : Type} (σv : ValSubst F) (σo : PathSubst) : CAtom F → CAtom F
  | .eq lhs rhs => .eq (lhs.subst σv σo) (rhs.subst σv σo)
  | .neZero term => .neZero (term.subst σv σo)

/-- Interpret an atomic checked constraint as a proposition. -/
def CAtom.interp {F : Type} [Field F] (w : Witness F) (ρv : LocalVar → F)
    (ρo : LocalVar → InstancePath) : CAtom F → Prop
  | .eq lhs rhs => VTerm.interp w ρv ρo lhs = VTerm.interp w ρv ρo rhs
  | .neZero term => VTerm.interp w ρv ρo term ≠ 0

theorem CAtom.interp_subst {F : Type} [Field F] (w : Witness F)
    (σv : ValSubst F) (σo : PathSubst)
    (ρv ρv' : LocalVar → F) (ρo ρo' : LocalVar → InstancePath)
    (hσv : ∀ v, VTerm.interp w ρv ρo (σv v) = ρv' v)
    (hσo : ∀ v, PTerm.interp ρo (σo v) = ρo' v)
    (a : CAtom F) :
    CAtom.interp w ρv ρo (a.subst σv σo) = CAtom.interp w ρv' ρo' a := by
  cases a with
  | eq lhs rhs =>
    simp [CAtom.subst, CAtom.interp, VTerm.interp_subst, hσv, hσo]
  | neZero term =>
    simp [CAtom.subst, CAtom.interp, VTerm.interp_subst, hσv, hσo]

end SubstSemantics
