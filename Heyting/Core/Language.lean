import Mathlib.Algebra.Field.Basic

-- A witness is an assignment of field values to variables
abbrev Witness (V : Type) (F : Type) := V → F

-- A language is defined by its syntax and semantics
class Language (V : Type) (F : Type) [Field F] where
  -- The syntax of the language, typically defined inductively
  Program : Type

  -- For ZKP languages, it suffices to know that a witness [w] satisfies the
  -- constraints of [p]
  satisfies : Witness V F -> Program -> Prop
