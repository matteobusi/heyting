/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Dialect

/-!
# Struct-object dialect

Typed syntax for LLZK object allocation and member access. Unlike local Felt
operations, these instructions need object-path and witness-store state in
addition to the generic field-local environment. `State` and `apply` provide
that executable semantics explicitly; integration into generic `DialectSem`
is intentionally deferred until its state model can represent these effects.
-/

namespace Dialect.StructObject

open Dialect

abbrev InstancePath := List Nat
abbrev Witness (F : Type) := InstancePath × Nat → F
abbrev ObjEnv := LocalVar → InstancePath

inductive Op (γ : OpCtx) (F : Type) : Type where
  | newStruct (dest : LocalVar)
  | readMember (dest self : LocalVar) (member : Fin γ.numMembers)
  | writeMember (self : LocalVar) (member : Fin γ.numMembers) (src : LocalVar)
  deriving Repr

def dest : Op γ F → Option LocalVar
  | .newStruct d | .readMember d _ _ => some d
  | .writeMember _ _ _ => none

def reads : Op γ F → List LocalVar
  | .newStruct _ => []
  | .readMember _ self _ => [self]
  | .writeMember self _ src => [self, src]

def cap : Op γ F → Capability
  | .readMember _ _ _ => .pure
  | .newStruct _ | .writeMember _ _ _ => .witness

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .newStruct d => .newStruct (ρ d)
  | .readMember d self member => .readMember (ρ d) (ρ self) member
  | .writeMember self member src => .writeMember (ρ self) member (ρ src)

def sig : OpSig where
  Op := Op
  dest := dest
  reads := reads
  mapVars := mapVars
  cap := cap
  mapVars_id := by intro γ F op; cases op <;> simp [mapVars]
  mapVars_comp := by intro γ F ρ σ op; cases op <;> simp [mapVars, Function.comp_apply]
  dest_mapVars := by intro γ F ρ op; cases op <;> simp [mapVars, dest]
  reads_mapVars := by intro γ F ρ op; cases op <;> simp [mapVars, reads]
  cap_mapVars := by intro γ F ρ op; cases op <;> simp [mapVars, cap]

def ObjEnv.update (env : ObjEnv) (v : LocalVar) (path : InstancePath) : ObjEnv :=
  fun x => if x = v then path else env x

def ValueEnv.update (env : LocalVar → F) (v : LocalVar) (value : F) : LocalVar → F :=
  fun x => if x = v then value else env x

def Witness.update (witness : Witness F) (key : InstancePath × Nat)
    (value : F) : Witness F :=
  fun x => if x = key then value else witness x

/-- State required by struct-object operations. -/
structure State (F : Type) where
  values : LocalVar → F
  objects : ObjEnv
  witness : Witness F
  nextPath : Nat

/-- Execute one object operation. The first allocation receives the root path
`[]`; subsequent allocations receive singleton paths `[k]`. -/
def apply (op : Op γ F) (state : State F) : State F :=
  match op with
  | .newStruct d =>
    let path := if state.nextPath == 0 then [] else [state.nextPath]
    { state with
      objects := ObjEnv.update state.objects d path
      nextPath := state.nextPath + 1 }
  | .readMember d self member =>
    let selfPath := state.objects self
    { state with
      values := ValueEnv.update state.values d (state.witness (selfPath, member.val))
      objects := ObjEnv.update state.objects d (selfPath ++ [member.val]) }
  | .writeMember self member src =>
    let key := (state.objects self, member.val)
    { state with witness := Witness.update state.witness key (state.values src) }

@[simp] theorem apply_newStruct_nextPath (d : LocalVar) (state : State F) :
    (apply (.newStruct d : Op γ F) state).nextPath = state.nextPath + 1 := by
  simp [apply]

@[simp] theorem apply_readMember_value (d self : LocalVar)
    (member : Fin γ.numMembers) (state : State F) :
    (apply (.readMember d self member : Op γ F) state).values d =
      state.witness (state.objects self, member.val) := by
  simp [apply, ValueEnv.update]

@[simp] theorem apply_writeMember_value (self src : LocalVar)
    (member : Fin γ.numMembers) (state : State F) :
    (apply (.writeMember self member src : Op γ F) state).witness
        (state.objects self, member.val) = state.values src := by
  simp [apply, Witness.update]

end Dialect.StructObject
