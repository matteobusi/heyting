import Heyting.Core.StructuralPass
import Heyting.Dialects.CallSemantics
import Mathlib.Algebra.Field.Rat

namespace Dialect.StructuralPass.Tests

#check CallSemantics.structuralConstraintPass

open Dialect

abbrev F := ℚ
abbrev EmptySet : DialectSet := []

def emptyModule : Module EmptySet 0 F where
  structs i := Fin.elim0 i

abbrev unitStage : ModuleStage EmptySet 0 F where
  State := Unit
  satisfies _ _ := True

abbrev boolStage : ModuleStage EmptySet 0 F where
  State := Bool
  satisfies _ _ := True

abbrev natStage : ModuleStage EmptySet 0 F where
  State := Nat
  satisfies _ _ := True

def unitToBool : StructuralPass unitStage boolStage where
  lower m := .ok m
  stateRel _ _ _ _ := True
  preservation := by
    intro m out state hlower hsatisfies
    exact ⟨false, trivial, trivial⟩
  reflection := by
    intro m out state hlower hsatisfies
    exact ⟨(), trivial, trivial⟩

def boolToNat : StructuralPass boolStage natStage where
  lower m := .ok m
  stateRel _ _ _ _ := True
  preservation := by
    intro m out state hlower hsatisfies
    exact ⟨0, trivial, trivial⟩
  reflection := by
    intro m out state hlower hsatisfies
    exact ⟨false, trivial, trivial⟩

def composed : StructuralPass unitStage natStage :=
  unitToBool.compose boolToNat

def compositionRuns : Bool :=
  match composed.lower emptyModule with
  | .ok _ => true
  | .error _ => false

#guard compositionRuns

example : composed.stateRel emptyModule emptyModule () 0 := by
  exact ⟨emptyModule, false, rfl, trivial, trivial⟩

example : natStage.satisfies 0 emptyModule := by trivial

def rejecting : StructuralPass boolStage natStage where
  lower _ := .error "rejected"
  stateRel _ _ _ _ := False
  preservation := by
    intro m out state hlower hsatisfies
    simp at hlower
  reflection := by
    intro m out state hlower hsatisfies
    simp at hlower

def rejectionComposes : Bool :=
  match (unitToBool.compose rejecting).lower emptyModule with
  | .error "rejected" => true
  | _ => false

#guard rejectionComposes

/-! Witness-backed stages bridge to the existing correctness framework. -/

def witnessSat (_ : Witness Unit F) (_ : Module EmptySet 0 F) : Prop := True

def witnessIdentity : PresReflPass
    (ModuleStage.language Unit witnessSat)
    (ModuleStage.language Unit witnessSat) where
  compile m := m
  witnessRel _ _ _ := True
  preservation := by
    intro sourceState m hsatisfies
    exact ⟨sourceState, trivial, trivial⟩
  reflection := by
    intro targetState m hsatisfies
    exact ⟨targetState, trivial, trivial⟩

def lifted := StructuralPass.ofPresReflPass witnessIdentity

def liftedRuns : Bool :=
  match lifted.lower emptyModule with
  | .ok _ => true
  | .error _ => false

#guard liftedRuns

def liftedTotal : StructuralPass.TotalStructural lifted where
  run m := ⟨m, rfl⟩

def loweredBack : PresReflPass
    (ModuleStage.language Unit witnessSat)
    (ModuleStage.language Unit witnessSat) :=
  StructuralPass.toPresReflPass lifted liftedTotal

example : loweredBack.compile emptyModule = emptyModule := rfl

example :
    (StructuralPass.ofPresReflPass
      (PresReflPass.compose witnessIdentity witnessIdentity)).lower emptyModule =
    ((StructuralPass.ofPresReflPass witnessIdentity).compose
      (StructuralPass.ofPresReflPass witnessIdentity)).lower emptyModule := by
  exact StructuralPass.ofPresReflPass_compose_lower
    witnessIdentity witnessIdentity emptyModule

/-! Local views express reusable rename and frame obligations without exposing
the rest of a stage's state. -/

structure RichState where
  locals : Nat → F
  tag : Nat

def richView : LocalStateView RichState F := { read := RichState.locals }

def rich₀ : RichState := { locals := fun v => v, tag := 7 }
def rich₁ : RichState := { locals := fun v => v - 1, tag := 99 }

example : StateAgreesUnder richView (fun v => v + 1) rich₀ rich₁ := by
  intro v
  simp [richView, rich₀, rich₁]

example : PreservesLocalsOutside richView (some 2) rich₀
    { rich₀ with locals := fun v => if v = 2 then 100 else rich₀.locals v } := by
  intro v hv
  have hne : v ≠ 2 := by
    intro h
    apply hv
    simp [h]
  simp [richView, rich₀, hne]

end Dialect.StructuralPass.Tests
