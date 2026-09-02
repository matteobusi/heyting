/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Dialect

/-!
# Module Structure

Generic typed module over a `DialectSet`.

Layers:
- `MemberType n` — a member is either a felt or reference to another
  struct (`substruct`, by index `Fin n`).
- `MemberDecl n` — one struct member declaration.
- `FuncDef Δ n i F kind` — a function body with capability `kind`,
  well-formed by `capsLE` and `isSSA`.
- `StructDef Δ n i F` — one struct: member list, `@compute` body
  (capability `.witness`), `@constrain` body (capability `.constraint`).
- `Module Δ n F` — a complete module: array of `n` structs in topological order.

Call constructs live in a dedicated call dialect and are erased by normal
dialect passes.
-/

namespace Dialect

/-! ## Member types -/

/-- A struct member is either a field element or reference to another struct by index. -/
inductive MemberType (n : Nat) where
  | felt      : MemberType n
  | substruct : Fin n → MemberType n
  deriving Repr

/-- Declaration of one struct member. -/
structure MemberDecl (n : Nat) where
  name     : String
  type     : MemberType n
  isPublic : Bool
  deriving Repr

/-! ## Function definitions -/

/--
A function body with well-formedness proofs.

`kind : Capability` is a *type-level* index, not a runtime field, so
`FuncDef ... .witness` and `FuncDef ... .constraint` are distinct types
and cannot be confused at callsites.

Well-formedness:
- `wf_caps`: every op in `body` fits within `kind` (`capsLE kind body`).
- `wf_ssa`: `body` is in SSA form with `numParams` initially-defined locals.
-/
structure FuncDef
    (Δ : DialectSet) (n i : Nat) (F : Type) (kind : Capability)
    (numMembers : Nat) where
  numParams : Nat
  body      : List (Stmt Δ ⟨n, i, numMembers⟩ F)
  /-- For `.witness` funcs: the local holding the return value. -/
  returnVar : Option LocalVar
  wf_caps   : capsLE kind body = true
  wf_ssa    : isSSA (fun v => decide (v < numParams)) body = true

/-! ## Struct definitions -/

/--
A struct definition at index `i` in a module of `n` callables.

- `members` determines the witness-space width (`members.length` = `numMembers`).
- `compute` is the `@compute` / witness-generating body (`kind = .witness`).
- `constrain` is the `@constrain` / constraint-generating body (`kind = .constraint`).

Call dialect ops may only target structs `j < i` via `Fin i`.
-/
structure StructDef (Δ : DialectSet) (n : Nat) (i : Fin n) (F : Type) where
  name      : String
  members   : List (MemberDecl n)
  compute   : FuncDef Δ n i.val F .witness   members.length
  constrain : FuncDef Δ n i.val F .constraint members.length

/-! ## Module -/

/--
A complete module: `n` structs in topological order.

`n` is a type parameter (not a field) so Σ-types like `Σ n, Module Δ (n + 1) F`
compose naturally with pipeline.
-/
structure Module (Δ : DialectSet) (n : Nat) (F : Type) where
  structs : (i : Fin n) → StructDef Δ n i F

namespace Module

variable {Δ : DialectSet} {n : Nat} {F : Type}

/-- Number of callables in the module (convenient alias). -/
abbrev size (_ : Module Δ n F) : Nat := n

/-- Retrieve the struct at index `i`. -/
abbrev struct (m : Module Δ n F) (i : Fin n) : StructDef Δ n i F :=
  m.structs i

/-- Member count of struct `i`. -/
abbrev numMembers (m : Module Δ n F) (i : Fin n) : Nat :=
  (m.structs i).members.length

end Module

/-! ## Free functions

`function.def @f(felts) → felt` at module level (outside any struct) is not
yet a first-class type in this module structure, so AST lowering rejects free
functions. Future callable model may replace homogeneous `structs` array with
named callable space. Call selector field remains placeholder for this upgrade.
-/

end Dialect
