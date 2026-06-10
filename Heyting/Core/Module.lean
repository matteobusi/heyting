/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Dialect

/-!
# Module Structure

Generic typed module over a `DialectSet`.

Mirrors `StructIR.{StructDef,Module}` but generalized: statements use the
generic `Stmt Δ calls γ F` type instead of `ConstrainStmt`/`ComputeStmt`.

Layers:
- `MemberType n` — a member is either a felt or a reference to another
  struct (`substruct`, by index `Fin n`). Matches `StructIR.MemberType`.
- `MemberDecl n` — one struct member declaration.
- `FuncDef Δ calls n i F kind` — a function body with capability `kind`,
  well-formed by `capsLE` and `isSSA`.
- `StructDef Δ calls n i F` — one struct: member list, `@compute` body
  (capability `.witness`), `@constrain` body (capability `.constraint`).
- `Module Δ calls n F` — a complete module: array of `n` structs in
  topological order.

The type parameter `calls : Bool` gates the `Stmt.call` constructor.
Middle-layer dialect erasure passes are `calls = true` → `calls = true`
(skeleton-preserving). `EraseCalls` is the pass that flips to `calls = false`.
-/

namespace Dialect

/-! ## Member types -/

/-- A struct member is either a field element or a reference to another
    struct by index. Matches `StructIR.MemberType`. -/
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
    (Δ : DialectSet) (calls : Bool) (n i : Nat) (F : Type) (kind : Capability)
    (numMembers : Nat) where
  numParams : Nat
  body      : List (Stmt Δ calls ⟨n, i, numMembers⟩ F)
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

Calls may only target structs `j < i` (enforced by `Fin i` in `Stmt.call`).
-/
structure StructDef (Δ : DialectSet) (calls : Bool) (n : Nat) (i : Fin n) (F : Type) where
  name      : String
  members   : List (MemberDecl n)
  compute   : FuncDef Δ calls n i.val F .witness   members.length
  constrain : FuncDef Δ calls n i.val F .constraint members.length

/-! ## Module -/

/--
A complete module: `n` structs in topological order.

`n` is a type parameter (not a field) so Σ-types like `Σ n, Module Δ calls (n + 1) F`
compose naturally with the pipeline (mirrors `StructIR.Module n F`).
-/
structure Module (Δ : DialectSet) (calls : Bool) (n : Nat) (F : Type) where
  structs : (i : Fin n) → StructDef Δ calls n i F

namespace Module

variable {Δ : DialectSet} {calls : Bool} {n : Nat} {F : Type}

/-- Number of callables in the module (convenient alias). -/
abbrev size (_ : Module Δ calls n F) : Nat := n

/-- Retrieve the struct at index `i`. -/
abbrev struct (m : Module Δ calls n F) (i : Fin n) : StructDef Δ calls n i F :=
  m.structs i

/-- Member count of struct `i`. -/
abbrev numMembers (m : Module Δ calls n F) (i : Fin n) : Nat :=
  (m.structs i).members.length

end Module

/-! ## Free functions

`function.def @f(felts) → felt` at module level (outside any struct) is not
yet a first-class type in this module structure. Current encoding (usable
now): represent a free function as a `StructDef` with `members = []` and a
trivial `constrain` body. `Stmt.call target sel args` with `sel` selecting
the compute body reaches it. This encoding is provably correct — the
isomorphism is trivial — and is what Phase 1's iso-bridging will use.

Phase 3 will introduce a unified `Callable` sum type (struct | free function)
replacing the homogeneous `structs` array, with `sel : Nat` in `Stmt.call`
selecting which body of the target callable is invoked. The `sel` field is
already present as a placeholder for this upgrade.
-/

end Dialect
