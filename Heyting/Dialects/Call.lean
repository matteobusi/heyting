/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Dialect

/-!
# Call Dialect

Callable invocation syntax as ordinary dialect ops.
-/

namespace Dialect.Call

open Dialect

inductive Op (γ : OpCtx) (F : Type) : Type where
  | call (dest : Option LocalVar) (target : Fin γ.i) (sel : Nat) (args : List LocalVar) : Op γ F
  deriving Repr

def dest : Op γ F → Option LocalVar
  | .call dst _ _ _ => dst

def reads : Op γ F → List LocalVar
  | .call _ _ _ args => args

def cap : Op γ F → Capability
  | _ => .pure

def mapVars (ρ : LocalVar → LocalVar) : Op γ F → Op γ F
  | .call dst target sel args => .call (dst.map ρ) target sel (args.map ρ)

def sig : OpSig where
  Op      := Op
  dest    := dest
  reads   := reads
  mapVars := mapVars
  cap     := cap
  mapVars_id    := by intro γ F op; cases op; simp [mapVars]
  mapVars_comp  := by intro γ F ρ σ op; cases op; simp [mapVars, Option.map_map, List.map_map]
  dest_mapVars  := by intro γ F ρ op; cases op; simp [mapVars, dest]
  reads_mapVars := by intro γ F ρ op; cases op; simp [mapVars, reads]
  cap_mapVars   := by intro γ F ρ op; cases op; simp [cap]

end Dialect.Call
