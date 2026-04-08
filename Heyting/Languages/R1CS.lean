import Mathlib.Algebra.Field.Basic
import Heyting.Core.Language

namespace R1CS
  variable (F : Type) [Field F]
  inductive VarId
    | varOne : VarId
    | var : ℕ → VarId
    | aux : ℕ → VarId
    deriving Repr

  abbrev LinComb (F : Type) := List (VarId × F)

  structure Constraint (F : Type) where
    A : LinComb F
    B : LinComb F
    C : LinComb F
    deriving Repr

  structure System (F : Type) where
    constraints : List (Constraint F)
    deriving Repr

  abbrev Witness (F : Type) := VarId → F

  def evalLinComb {F : Type} [Field F] (w : Witness F) (vec : LinComb F) : F :=
    vec.foldl (fun acc (var, coeff) => acc + coeff * w var) 0

  def satisfiesLinComb {F : Type} [Field F] (w : Witness F) (c : Constraint F) : Prop :=
    (evalLinComb w c.A) * (evalLinComb w c.B) = (evalLinComb w c.C)

  def satisfies {F : Type} [Field F] (w : Witness F) (r1cs : System F) : Prop :=
    w .varOne = 1 ∧ ∀ c ∈ r1cs.constraints, satisfiesLinComb w c

  instance Language (F : Type) [Field F] : Language VarId F where
    Program := System F
    satisfies := satisfies
end R1CS
