/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Module

/-!
# Modular compute-side dialect semantics

Witness generation selects one concrete runtime state for the complete source
language, but delegates each non-structural operation to the handler belonging
to its dialect.  Structural dialects such as `Call` remain evaluators over a
handler family; they are not encoded as a dynamically typed effect list.
-/

namespace Dialect.WitnessSemantics

open Dialect

variable {Δ : DialectSet} {State F : Type} {ctx : OpCtx}

/-- Named failures at the source witness-execution boundary. -/
inductive RuntimeFault where
  | oracleUnderflow
  | divisionByZero (denominator : LocalVar)
  | unsupportedCallSelector (selector : Nat)
  | invalidCallTarget
  deriving Repr, DecidableEq

def RuntimeFault.message : RuntimeFault → String
  | .oracleUnderflow => "oracle input exhausted"
  | .divisionByZero v => s!"division by zero at local {v}"
  | .unsupportedCallSelector selector =>
      s!"unsupported call selector {selector}"
  | .invalidCallTarget => "invalid call target"

/-- Compute semantics contributed by one leaf dialect. -/
structure DialectHandler (sig : OpSig) (State F : Type) where
  step : {ctx : OpCtx} → sig.Op ctx F → State → Except RuntimeFault State

/-- Statically assembled handlers for a dialect set. -/
abbrev HandlerFamily (Δ : DialectSet) (State F : Type) :=
  (d : Fin Δ.length) → DialectHandler (Δ.get d) State F

def evalStmt (handlers : HandlerFamily Δ State F)
    (stmt : Stmt Δ ctx F) (state : State) : Except RuntimeFault State :=
  match stmt with
  | .op d payload => (handlers d).step payload state

def evalBody (handlers : HandlerFamily Δ State F) :
    List (Stmt Δ ctx F) → State → Except RuntimeFault State
  | [], state => .ok state
  | stmt :: rest, state => do
      let state' ← evalStmt handlers stmt state
      evalBody handlers rest state'

end Dialect.WitnessSemantics
