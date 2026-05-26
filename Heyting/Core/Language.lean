/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Basic

/-!
# Generic Constraint Languages

Core abstraction for constraint languages used throughout Heyting.

`Language` packages:
- a program syntax type, and
- a satisfaction relation between witnesses and programs.

Compiler passes, checked semantics, and correctness statements are all phrased
against this interface.
-/

/-- A witness assigns field values to variables of a language. -/
abbrev Witness (V : Type) (F : Type) := V → F

/--
A formal constraint language over variables `V` and field `F`.

`Program` is the syntax of the language, while `satisfies w p` gives its
semantic validity predicate for witness `w` and program `p`.
-/
class Language (V : Type) (F : Type) [Field F] where
  /-- The program type of the language. -/
  Program : Type

  /-- Semantic satisfaction of program `p` by witness `w`. -/
  satisfies : Witness V F -> Program -> Prop
