/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Basic

/-!
# Composable Dialects — Core Encoding

Phase 0 of the dialect re-architecture (`docs/ROADMAP.md`).

## Key design choices

**Flat sum of leaf ops.** No recursion through subterms. The only recursion
in the language is `call`, resolved through the module's topological callable
index. This keeps the generic evaluator's termination measure identical to
today's StructIR measure `(i, stmts.length)`.

**`Fin Δ.length` dialect index.** Membership is computable, so handler
dispatch reduces by `simp` and `fin_cases` gives exact case splits in proofs.

**Type-level `calls : Bool`.** "Function dialect erased" = `calls = false`,
which makes the `call` constructor uninhabitable. No code changes needed in
the generic evaluator.

**Shared `VarId` / `LocalVar`.** All dialect ops live inside the same module
skeleton, so all middle-layer passes share one variable-id type. Witness
relations in middle-layer passes are near-equalities on shared variables.
The heterogeneous (path × slot) → Nat → R1CS encoding lives only in the
fixed bottom passes, which already exist and are proved.
-/

namespace Dialect

/-- Local variables in statement bodies are natural numbers. -/
abbrev LocalVar := Nat

/-! ## Op context -/

/--
The typing context an op is indexed by:
- `n` — total number of callables in the module (topological order);
- `i` — index of the enclosing callable (calls may only target `j < i`);
- `numMembers` — member count of the enclosing struct.
-/
structure OpCtx where
  n          : Nat
  i          : Nat
  numMembers : Nat
  deriving Repr, DecidableEq

/-! ## Capabilities -/

/--
Where an op may appear. Mirrors LLZK's `WitnessGen`/`ConstraintGen` traits.

- `pure`       — allowed in any function body kind.
- `witness`    — only in `@compute` / witness-generation bodies.
- `constraint` — only in `@constrain` / constraint-generation bodies.

A `FuncDef` carries a `Capability` kind and a well-formedness proof that
every op in its body satisfies `op.cap ≤ kind`.
-/
inductive Capability where
  | pure
  | witness
  | constraint
  deriving Repr, DecidableEq

/-- `a ≤ b` iff an op with capability `a` is allowed in a body of kind `b`.
    `pure` ops are universally allowed. -/
def Capability.le (a b : Capability) : Prop := a = .pure ∨ a = b

instance : LE Capability := ⟨Capability.le⟩

instance (a b : Capability) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a = .pure ∨ a = b))

theorem Capability.pure_le (b : Capability) : Capability.pure ≤ b :=
  Or.inl rfl

theorem Capability.le_refl (a : Capability) : a ≤ a := Or.inr rfl

theorem Capability.le_trans {a b c : Capability} (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  rcases hab with h | h
  · exact Or.inl h
  · rcases hbc with h' | h'
    · exact Or.inl (h ▸ h')
    · exact Or.inr (h ▸ h')

/-! ## Dialect signatures -/

/--
The syntactic signature of one dialect.

Each dialect provides an op type `Op : OpCtx → Type → Type` (context- and
field-indexed) together with the metadata the generic statement layer needs
for SSA checking, variable renaming, and capability tracking.

Semantics (`constrainStep` / `computeStep` and their laws) live in a
separate `DialectSem` structure, keeping `OpSig` proof-obligation-free and
usable before committing to a particular field.
-/
structure OpSig where
  /-- Ops of this dialect in context `γ` over field `F`. -/
  Op : OpCtx → Type → Type

  /-- Destination local written by the op, if any. -/
  dest : ∀ {γ : OpCtx} {F : Type}, Op γ F → Option LocalVar

  /-- Locals read by the op. -/
  reads : ∀ {γ : OpCtx} {F : Type}, Op γ F → List LocalVar

  /-- Rename all locals (reads and dest) through `ρ`. -/
  mapVars : ∀ {γ : OpCtx} {F : Type}, (LocalVar → LocalVar) → Op γ F → Op γ F

  /-- Capability of the op. -/
  cap : ∀ {γ : OpCtx} {F : Type}, Op γ F → Capability

  /-- `mapVars` with the identity is the identity. -/
  mapVars_id : ∀ {γ : OpCtx} {F : Type} (op : Op γ F), mapVars id op = op

  /-- `mapVars` composes. -/
  mapVars_comp : ∀ {γ : OpCtx} {F : Type} (ρ σ : LocalVar → LocalVar)
      (op : Op γ F), mapVars ρ (mapVars σ op) = mapVars (ρ ∘ σ) op

  /-- `dest` commutes with renaming. -/
  dest_mapVars : ∀ {γ : OpCtx} {F : Type} (ρ : LocalVar → LocalVar)
      (op : Op γ F), dest (mapVars ρ op) = (dest op).map ρ

  /-- `reads` commutes with renaming. -/
  reads_mapVars : ∀ {γ : OpCtx} {F : Type} (ρ : LocalVar → LocalVar)
      (op : Op γ F), reads (mapVars ρ op) = (reads op).map ρ

  /-- Capability is invariant under renaming. -/
  cap_mapVars : ∀ {γ : OpCtx} {F : Type} (ρ : LocalVar → LocalVar)
      (op : Op γ F), cap (mapVars ρ op) = cap op

/-- A dialect set is a list of dialect signatures in canonical (pipeline) order. -/
abbrev DialectSet := List OpSig

/-! ## Core statements -/

/--
A statement over dialect set `Δ` in context `γ` over field `F`.

- `op d payload` — a leaf op of dialect `d ∈ Δ`.
- `call` — a call into a callable earlier in topological order, gated by
  `calls = true`. `dest = none` for void (constraint-kind) calls.
  `sel` selects which body of the target callable is invoked — Phase 3
  unifies free functions, `@compute`, `@constrain`, and helper functions
  into one topologically ordered callable space.
-/
inductive Stmt (Δ : DialectSet) (calls : Bool) (γ : OpCtx) (F : Type) where
  | op   (d : Fin Δ.length) (payload : (Δ.get d).Op γ F)
  | call (h : calls = true) (dest : Option LocalVar) (target : Fin γ.i)
         (sel : Nat) (args : List LocalVar)

namespace Stmt

variable {Δ : DialectSet} {calls : Bool} {γ : OpCtx} {F : Type}

/-- Destination local written by a statement, if any. -/
def dest : Stmt Δ calls γ F → Option LocalVar
  | .op d p          => (Δ.get d).dest p
  | .call _ dst _ _ _ => dst

/-- Locals read by a statement. -/
def reads : Stmt Δ calls γ F → List LocalVar
  | .op d p           => (Δ.get d).reads p
  | .call _ _ _ _ args => args

/-- Rename all locals through `ρ`. -/
def mapVars (ρ : LocalVar → LocalVar) : Stmt Δ calls γ F → Stmt Δ calls γ F
  | .op d p            => .op d ((Δ.get d).mapVars ρ p)
  | .call h dst t s args => .call h (dst.map ρ) t s (args.map ρ)

/--
Capability of a statement. `call` is `pure` at the statement layer; the
callee's body kind determines what the call site actually constrains.
-/
def cap : Stmt Δ calls γ F → Capability
  | .op d p         => (Δ.get d).cap p
  | .call _ _ _ _ _ => .pure

theorem mapVars_id (s : Stmt Δ calls γ F) : s.mapVars id = s := by
  cases s with
  | op d p           => simp [mapVars, OpSig.mapVars_id]
  | call h dst t sel args => simp [mapVars]

theorem mapVars_comp (ρ σ : LocalVar → LocalVar) (s : Stmt Δ calls γ F) :
    (s.mapVars σ).mapVars ρ = s.mapVars (ρ ∘ σ) := by
  cases s with
  | op d p           => simp [mapVars, OpSig.mapVars_comp]
  | call h dst t sel args => simp [mapVars, Option.map_map, List.map_map]

theorem dest_mapVars (ρ : LocalVar → LocalVar) (s : Stmt Δ calls γ F) :
    (s.mapVars ρ).dest = s.dest.map ρ := by
  cases s with
  | op d p           => simp [mapVars, dest, OpSig.dest_mapVars]
  | call h dst t sel args => simp [mapVars, dest]

theorem reads_mapVars (ρ : LocalVar → LocalVar) (s : Stmt Δ calls γ F) :
    (s.mapVars ρ).reads = s.reads.map ρ := by
  cases s with
  | op d p           => simp [mapVars, reads, OpSig.reads_mapVars]
  | call h dst t sel args => simp [mapVars, reads]

theorem cap_mapVars (ρ : LocalVar → LocalVar) (s : Stmt Δ calls γ F) :
    (s.mapVars ρ).cap = s.cap := by
  cases s with
  | op d p           => simp [mapVars, cap, OpSig.cap_mapVars]
  | call h dst t sel args => simp [mapVars, cap]

/-- A `call`-free statement embeds into a call-enabled one. -/
def liftCalls : Stmt Δ false γ F → Stmt Δ calls γ F
  | .op d p               => .op d p
  | .call h _ _ _ _       => absurd h (by simp)

end Stmt

/-! ## Generic SSA and capability discipline -/

/--
SSA check for statement lists, parameterized by the initially-defined local set.
Identical shape to `StructIR.isSSA`; stated once generically.
-/
def isSSA {Δ : DialectSet} {calls : Bool} {γ : OpCtx} {F : Type} :
    (LocalVar → Bool) → List (Stmt Δ calls γ F) → Bool
  | _,    []      => true
  | init, s :: sl =>
    s.reads.all init &&
    match s.dest with
    | some d => !init d && isSSA (fun x => init x || x == d) sl
    | none   => isSSA init sl

/-- All statements in `body` fit within function-kind `k`. -/
def capsLE {Δ : DialectSet} {calls : Bool} {γ : OpCtx} {F : Type}
    (k : Capability) (body : List (Stmt Δ calls γ F)) : Bool :=
  body.all (fun s => decide (s.cap ≤ k))

end Dialect
