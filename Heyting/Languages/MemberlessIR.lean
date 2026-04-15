/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Language

/-!
# MemberlessIR — Memberless Intermediate Representation

An intermediate IR that sits between `StructIR` and `FlatIR`.

## Purpose

`MemberlessIR` is the output of Pass 1 (struct flattening). It is identical to
`StructIR` except:
- All struct member accesses (`readMember`, `writeMember`, `newStruct`) are gone.
- All struct-typed variables have been replaced by flat felt variables.
- The `call` statement is still present (call inlining happens in Pass 2).
- The witness type is `Nat → F` (a flat assignment of field values to variable IDs).

## Witness and satisfiability

A witness `w : Nat → F` satisfies a program `p` when evaluating the main
function's constrain body with `env k = w k` for all `k` yields `True` (the
conjunction of all emitted `constrainEq` checks holds).

The first `numParams` variable slots are seeded from `w` directly — this is
what makes satisfiability non-vacuous for circuits with felt inputs.

## Design

Each `Func` in `MemberlessIR` has:
- `numParams : Nat` — number of felt parameters (slots `0..numParams-1` in `env`)
- `body : List Stmt` — sequence of felt-arithmetic and call statements

Termination of evaluation is guaranteed by the same topological index as
`StructIR`: struct `i` can only call struct `j < i`.
-/

namespace MemberlessIR

abbrev LocalVar := Nat

/-! ## Statements -/

/-- A statement in a `MemberlessIR` function body.
    Parameterized by `n` (module size) and `i` (owning struct index) so that
    cross-struct calls are statically bounded. -/
inductive Stmt (n : Nat) (i : Fin n) (F : Type) where
  /-- `dest := src1 + src2` -/
  | feltAdd (dest src1 src2 : LocalVar)
  /-- `dest := src1 - src2` -/
  | feltSub (dest src1 src2 : LocalVar)
  /-- `dest := src1 * src2` -/
  | feltMul (dest src1 src2 : LocalVar)
  /-- `dest := src1 / src2` (requires `src2 ≠ 0` at runtime) -/
  | feltDiv (dest src1 src2 : LocalVar)
  /-- `dest := -src` -/
  | feltNeg (dest src : LocalVar)
  /-- `dest := c` -/
  | feltConst (dest : LocalVar) (c : F)
  /-- Emit the constraint `src1 = src2` -/
  | constrainEq (src1 src2 : LocalVar)
  /-- Inline a call to function `target` (index `< i`) with given arguments -/
  | call (target : Fin i) (args : List LocalVar)
  deriving Repr

/-! ## Functions and programs -/

/-- A function in `MemberlessIR`: felt parameters and a constrain body. -/
structure Func (n : Nat) (i : Fin n) (F : Type) where
  /-- Number of felt parameters (occupying slots `0..numParams-1`). -/
  numParams : Nat
  /-- The body of the `@constrain`-equivalent function. -/
  body      : List (Stmt n i F)
  deriving Repr

/-- A `MemberlessIR` module: `n` functions, topologically ordered (leaves first).
    The main function is at index `n - 1`. -/
abbrev Module (n : Nat) (F : Type) := (i : Fin n) → Func n i F

/-! ## Semantics -/

/-- Local variable environment: maps `LocalVar → F`. -/
abbrev LocalEnv (F : Type) := LocalVar → F

/-- Update a `LocalEnv` at a single variable. -/
def LocalEnv.update (env : LocalEnv F) (v : LocalVar) (val : F) : LocalEnv F :=
  fun w => if w == v then val else env w

variable {F : Type} [Field F] {n : Nat}

/-- Evaluate a `MemberlessIR` constrain body for function at index `i`.

    The `env` maps each local variable to its current felt value.
    Returns the conjunction of all `constrainEq` constraints encountered,
    together with the `feltDiv` non-zero side conditions. -/
def evalBody (m : Module n F) (i : Fin n) (env : LocalEnv F)
    (stmts : List (Stmt n i F)) : Prop :=
  match stmts with
  | [] => True
  | stmt :: rest =>
    let (env', prop) :=
      match stmt with
      | .feltAdd dest src1 src2 =>
        (env.update dest (env src1 + env src2), True)
      | .feltSub dest src1 src2 =>
        (env.update dest (env src1 - env src2), True)
      | .feltMul dest src1 src2 =>
        (env.update dest (env src1 * env src2), True)
      | .feltDiv dest src1 src2 =>
        (env.update dest (env src1 * (env src2)⁻¹), env src2 ≠ 0)
      | .feltNeg dest src =>
        (env.update dest (-(env src)), True)
      | .feltConst dest c =>
        (env.update dest c, True)
      | .constrainEq src1 src2 =>
        (env, env src1 = env src2)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let calleeEnv : LocalEnv F := fun param =>
          match args[param]? with
          | some arg => env arg
          | none     => 0
        let callProp := evalBody m j calleeEnv (m j).body
        (env, callProp)
    prop ∧ evalBody m i env' rest
  termination_by (i, stmts.length)

/-- Top-level satisfiability for a `MemberlessIR` module.

    The witness `w : Nat → F` seeds the main function's initial environment:
    `env k = w k` for all `k`.  This makes satisfiability non-vacuous —
    felt inputs appear directly in the initial environment. -/
def satisfies (w : Nat → F) (m : Module (n + 1) F) : Prop :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  evalBody m mainIdx w (m mainIdx).body

/-! ## Language instance -/

instance instLanguage (n : Nat) (F : Type) [Field F] :
    Language Nat F where
  Program  := Module (n + 1) F
  satisfies := fun w m => satisfies w m

end MemberlessIR
