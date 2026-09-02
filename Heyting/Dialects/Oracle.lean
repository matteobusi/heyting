/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Dialect

/-!
# Oracle dialect

Typed syntax for witness-only nondeterministic field values.  Execution consumes
one value from an explicit stream; the stream cursor is part of the interpreter
state, so calls cannot duplicate or silently reset oracle input.

The constraint compiler erases these operations from compute bodies.  Oracle
operations are rejected by capability checking in constraint bodies.
-/

namespace Dialect.Oracle

open Dialect

inductive Op (γ : OpCtx) (F : Type) where
  | next (dest : LocalVar)
  deriving Repr, DecidableEq

def dest : Op γ F → Option LocalVar
  | .next d => some d

def reads : Op γ F → List LocalVar
  | .next _ => []

def cap : Op γ F → Capability
  | .next _ => .witness

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .next d => .next (ρ d)

def sig : OpSig where
  Op := Op
  dest := dest
  reads := reads
  mapVars := mapVars
  cap := cap
  mapVars_id := by intro γ F op; cases op; rfl
  mapVars_comp := by intro γ F ρ σ op; cases op; rfl
  dest_mapVars := by intro γ F ρ op; cases op; rfl
  reads_mapVars := by intro γ F ρ op; cases op; rfl
  cap_mapVars := by intro γ F ρ op; cases op; rfl

/-- Runtime oracle stream. `read` remains a total low-level accessor for
inspection; modular witness execution uses checked indexing and reports
`oracleUnderflow` rather than calling `read` on an exhausted stream. -/
structure Stream (F : Type) where
  values : List F
  cursor : Nat := 0
  deriving Repr

def Stream.read [OfNat F 0] (stream : Stream F) : F :=
  stream.values[stream.cursor]?.getD 0

def Stream.advance (stream : Stream F) : Stream F :=
  { stream with cursor := stream.cursor + 1 }

def Stream.next [OfNat F 0] (stream : Stream F) : F × Stream F :=
  (stream.read, stream.advance)

end Dialect.Oracle
