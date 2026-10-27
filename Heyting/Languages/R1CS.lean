/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Language

/-!
# Rank-1 Constraint Systems

Core R1CS syntax and semantics used as the final verified target language.

An R1CS system consists of constraints of form `A * B = C` over wire-indexed
linear combinations, together with a distinguished constant wire `varOne`.
-/

namespace R1CS
  variable (F : Type) [Field F]

  /--
  Wire identifiers in R1CS.

  `varOne` is distinguished constant wire 1, `var` stores user/compiled wires,
  `aux` stores auxiliary inverse witnesses for `assignDiv` (holds `src⁻¹`), and
  `auxIsZero` stores auxiliary is-zero witnesses for `assignInv` (holds `1 - src·src⁻¹`).
  -/
  inductive VarId
    | varOne : VarId
    | var : ℕ → VarId
    | aux : ℕ → VarId
    | auxIsZero : ℕ → VarId
    deriving Repr, DecidableEq

  /-- A linear combination over R1CS wires. -/
  abbrev LinComb (F : Type) := List (VarId × F)

  /-- A single R1CS constraint `A * B = C`. -/
  structure Constraint (F : Type) where
    A : LinComb F
    B : LinComb F
    C : LinComb F
    deriving Repr

  /-- A full R1CS system together with its statement wires.

  `publicOutputs ++ publicInputs` lists, in order, the wires whose values form the public
  statement. Serializers place them at wires `1..k` (Circom: outputs first, then inputs). -/
  structure System (F : Type) where
    constraints   : List (Constraint F)
    publicOutputs : List VarId := []
    publicInputs  : List VarId := []
    deriving Repr

  /-- Number of public output wires. -/
  def System.numPublicOutputs {F : Type} (r1cs : System F) : Nat := r1cs.publicOutputs.length

  /-- Number of public input wires. -/
  def System.numPublicInputs {F : Type} (r1cs : System F) : Nat := r1cs.publicInputs.length

  /-- Statement wires in statement order: public outputs, then public inputs. -/
  def System.statementVars {F : Type} (r1cs : System F) : List VarId :=
    r1cs.publicOutputs ++ r1cs.publicInputs

  /-- An R1CS witness assigns a field element to every wire identifier. -/
  abbrev Witness (F : Type) := VarId → F

  /-- Evaluate a linear combination under a witness. -/
  def evalLinComb {F : Type} [Field F] (w : Witness F) (vec : LinComb F) : F :=
    vec.foldl (fun acc (var, coeff) => acc + coeff * w var) 0

  /-- Satisfaction of a single R1CS constraint. -/
  def satisfiesLinComb {F : Type} [Field F] (w : Witness F) (c : Constraint F) : Prop :=
    (evalLinComb w c.A) * (evalLinComb w c.B) = (evalLinComb w c.C)

  /-- Satisfaction of an R1CS system, including the distinguished `varOne = 1` invariant. -/
  def satisfies {F : Type} [Field F] (w : Witness F) (r1cs : System F) : Prop :=
    w .varOne = 1 ∧ ∀ c ∈ r1cs.constraints, satisfiesLinComb w c

  /-- Public statement exposed by a witness: the values of the statement wires. -/
  def statement {F : Type} (r1cs : System F) (w : Witness F) : List F :=
    r1cs.statementVars.map w

  /-- NP relation of an R1CS system: `w` satisfies it and exposes statement `x`. -/
  def Relation {F : Type} [Field F] (r1cs : System F) (x : List F) (w : Witness F) : Prop :=
    satisfies w r1cs ∧ statement r1cs w = x

  /-- Satisfaction ignores which wires are public. -/
  @[simp] theorem satisfies_withStatement {F : Type} [Field F] (w : Witness F)
      (r1cs : System F) (outputs inputs : List VarId) :
      satisfies w { r1cs with publicOutputs := outputs, publicInputs := inputs } ↔
        satisfies w r1cs := Iff.rfl

  /-- R1CS as an instance of the generic `Language` interface. -/
  instance Language (F : Type) [Field F] : Language VarId F where
    Program := System F
    satisfies := satisfies
end R1CS
