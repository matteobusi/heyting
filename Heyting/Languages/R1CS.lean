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
  and `aux` stores auxiliary witnesses such as inverses for division.
  -/
  inductive VarId
    | varOne : VarId
    | var : ℕ → VarId
    | aux : ℕ → VarId
    deriving Repr

  /-- A linear combination over R1CS wires. -/
  abbrev LinComb (F : Type) := List (VarId × F)

  /-- A single R1CS constraint `A * B = C`. -/
  structure Constraint (F : Type) where
    A : LinComb F
    B : LinComb F
    C : LinComb F
    deriving Repr

  /-- A full R1CS system together with its public-input count. -/
  structure System (F : Type) where
    constraints     : List (Constraint F)
    numPublicInputs : Nat               -- number of public wires (signals 1..numPublicInputs)
    deriving Repr

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

  /-- R1CS as an instance of the generic `Language` interface. -/
  instance Language (F : Type) [Field F] : Language VarId F where
    Program := System F
    satisfies := satisfies
end R1CS
