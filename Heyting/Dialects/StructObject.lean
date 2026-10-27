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

## Object model

Objects form a tree. A member `m` of the object at path `p` is the coordinate `(p, m)`, and a
sub-component stored in member `m` is the object at path `p ++ [m]`. Both `@constrain` and
`@compute` use this tree:

* `readMember` reads `(p, m)` and gives the result the path `p ++ [m]`;
* `newStruct` creates a fresh object at a singleton path `[k]` (one per allocation);
* `writeMember` stores a field value at `(p, m)`;
* `writeObject` stores a sub-component: it copies the subtree of the source object to
  `p ++ [m]`, as upstream LLZK value semantics store a struct value in a member.

Member indices are plain naturals: an index refers to the struct type of the object operand,
not to the enclosing struct, so reads of another struct's members are representable.
Frontends resolve and bound them against that struct type.
-/

namespace Dialect.StructObject

open Dialect

abbrev InstancePath := List Nat
abbrev Witness (F : Type) := InstancePath × Nat → F
abbrev ObjEnv := LocalVar → InstancePath

/-- Object operations. `γ` is kept for uniformity with other dialects; member indices are
relative to the struct type of the object operand. -/
inductive Op (γ : OpCtx) (F : Type) : Type where
  | newStruct (dest : LocalVar)
  | readMember (dest self : LocalVar) (member : Nat)
  | writeMember (self : LocalVar) (member : Nat) (src : LocalVar)
  | writeObject (self : LocalVar) (member : Nat) (src : LocalVar)
  deriving Repr

def dest : Op γ F → Option LocalVar
  | .newStruct d | .readMember d _ _ => some d
  | .writeMember _ _ _ | .writeObject _ _ _ => none

def reads : Op γ F → List LocalVar
  | .newStruct _ => []
  | .readMember _ self _ => [self]
  | .writeMember self _ src | .writeObject self _ src => [self, src]

def cap : Op γ F → Capability
  | .readMember _ _ _ => .pure
  | .newStruct _ | .writeMember _ _ _ | .writeObject _ _ _ => .witness

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .newStruct d => .newStruct (ρ d)
  | .readMember d self member => .readMember (ρ d) (ρ self) member
  | .writeMember self member src => .writeMember (ρ self) member (ρ src)
  | .writeObject self member src => .writeObject (ρ self) member (ρ src)

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

/-- Copy the subtree rooted at `src` to the subtree rooted at `dst`: every coordinate below
`dst` takes the value of the corresponding coordinate below `src`; others are unchanged. -/
def Witness.copySubtree (witness : Witness F) (src dst : InstancePath) : Witness F :=
  fun (path, member) =>
    if dst.isPrefixOf path then witness (src ++ path.drop dst.length, member)
    else witness (path, member)

/-- State required by struct-object operations. -/
structure State (F : Type) where
  values : LocalVar → F
  objects : ObjEnv
  witness : Witness F
  nextPath : Nat

/-- Path of the `k`-th allocated object: a fresh singleton root. -/
def allocatePath (k : Nat) : InstancePath := [k]

/-- Execute one object operation (see the module documentation for the object model). -/
def apply (op : Op γ F) (state : State F) : State F :=
  match op with
  | .newStruct d =>
    { state with
      objects := ObjEnv.update state.objects d (allocatePath state.nextPath)
      nextPath := state.nextPath + 1 }
  | .readMember d self member =>
    let selfPath := state.objects self
    { state with
      values := ValueEnv.update state.values d (state.witness (selfPath, member))
      objects := ObjEnv.update state.objects d (selfPath ++ [member]) }
  | .writeMember self member src =>
    let key := (state.objects self, member)
    { state with witness := Witness.update state.witness key (state.values src) }
  | .writeObject self member src =>
    let copied := Witness.copySubtree state.witness (state.objects src)
      (state.objects self ++ [member])
    { state with witness := copied }

@[simp] theorem apply_newStruct_nextPath (d : LocalVar) (state : State F) :
    (apply (.newStruct d : Op γ F) state).nextPath = state.nextPath + 1 := by
  simp [apply]

@[simp] theorem apply_readMember_value (d self : LocalVar)
    (member : Nat) (state : State F) :
    (apply (.readMember d self member : Op γ F) state).values d =
      state.witness (state.objects self, member) := by
  simp [apply, ValueEnv.update]

@[simp] theorem apply_writeMember_value (self src : LocalVar)
    (member : Nat) (state : State F) :
    (apply (.writeMember self member src : Op γ F) state).witness
        (state.objects self, member) = state.values src := by
  simp [apply, Witness.update]

/-- After `writeObject`, the stored member subtree reads as the source object's subtree. -/
theorem apply_writeObject_witness (self src : LocalVar) (member : Nat) (state : State F)
    (path : InstancePath) (field : Nat) :
    (apply (.writeObject self member src : Op γ F) state).witness
        (state.objects self ++ [member] ++ path, field) =
      state.witness (state.objects src ++ path, field) := by
  simp [apply, Witness.copySubtree]

end Dialect.StructObject
