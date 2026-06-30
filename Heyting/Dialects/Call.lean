/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.ModuleSemantics

/-!
# Call Dialect

Callable invocation syntax as ordinary dialect ops.

Initial Phase-4 semantics policy:
- `target : Fin γ.i` enforces topological calls to earlier callables.
- `sel = 0` selects the target struct's existing compute/constrain body.
- other selectors are reserved for Phase 3 first-class callable space.
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

/-- Initial selector policy: selector `0` chooses the existing compute/constrain body. -/
def selectorSupported (sel : Nat) : Bool := sel == 0

/-- Bind call arguments into a callee-local environment. -/
def bindArgs (callerEnv : LocalVar → F) (args : List LocalVar) (default : F) : LocalVar → F :=
  bindParams (args.map callerEnv) default

@[simp] theorem bindArgs_lt (callerEnv : LocalVar → F) (args : List LocalVar) (default : F)
    {v : LocalVar} (h : v < args.length) :
    bindArgs callerEnv args default v = callerEnv (args.get ⟨v, h⟩) := by
  simp [bindArgs, bindParams, h]

@[simp] theorem bindArgs_ge (callerEnv : LocalVar → F) (args : List LocalVar) (default : F)
    {v : LocalVar} (h : args.length ≤ v) :
    bindArgs callerEnv args default v = default := by
  simp [bindArgs, bindParams_ge, List.length_map, h]

/-- Lift a topological call target `Fin γ.i` into the enclosing module index. -/
def moduleTarget {n i : Nat} (target : Fin i) (hi : i < n) : Fin n :=
  ⟨target.val, Nat.lt_trans target.isLt hi⟩

/-- Lookup the target struct for a call target, given the current index is in bounds. -/
def targetStruct {Δ : DialectSet} {n : Nat} {F : Type} [Field F] {γ : OpCtx}
    (ctx : SemCtx Δ n F)
    (target : Fin γ.i)
    (hi : γ.i < n) : StructDef Δ n (moduleTarget target hi) F :=
  ctx.module.structs (moduleTarget target hi)

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
