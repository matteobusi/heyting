/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Heyting.Languages.R1CS

/-!
# R1CS JSON Rendering

JSON serializers and human-readable renderers for `R1CS` variables, linear
combinations, constraints, and whole systems.
-/

namespace R1CSJSON

open R1CS Lean

variable {F : Type} [Field F] [Repr F]

/-- Serialize a variable identifier with an explicit constructor tag. -/
def varIdToJson (v : R1CS.VarId) : Json :=
  match v with
  | .varOne => Json.mkObj [("tag", "varOne")]
  | .var n => Json.mkObj [("tag", "var"), ("index", n)]
  | .aux n => Json.mkObj [("tag", "aux"), ("index", n)]
  | .auxIsZero n => Json.mkObj [("tag", "auxIsZero"), ("index", n)]

/-- Pretty-print an `R1CS.VarId` using witness-style names. -/
def varIdToString (v : R1CS.VarId) : String :=
  match v with
  | .varOne => "ONE"
  | .var n => s!"v{n}"
  | .aux n => s!"aux{n}"
  | .auxIsZero n => s!"auxIsZero{n}"

/-- Render a field element using its `repr`. -/
def fieldRepr (c : F) : String :=
  toString (repr c)

/-- Serialize a field element as its `repr` string. -/
def fieldToJson (c : F) : Json :=
  Json.str (fieldRepr c)

/-- Serialize a linear combination as a JSON array of `(var, coeff)` objects. -/
def linCombToJson (lc : R1CS.LinComb F) : Json :=
  Json.arr <| lc.toArray.map fun (v, c) =>
    Json.mkObj [("var", varIdToJson v), ("coeff", fieldToJson c)]

/-- Pretty-print a linear combination in readable algebraic form. -/
def linCombToHuman (lc : R1CS.LinComb F) : String :=
  match lc with
  | [] => "0"
  | [(v, c)] =>
    let cv := fieldRepr c
    match v with
    | .varOne => cv
    | _ => s!"{cv}*{varIdToString v}"
  | _ =>
    String.intercalate " + " <| lc.map fun (v, c) =>
      let cv := fieldRepr c
      match v with
      | .varOne => cv
      | _ => s!"{cv}*{varIdToString v}"

/-- Serialize one R1CS constraint as JSON object with `A`, `B`, and `C` entries. -/
def constraintToJson (c : R1CS.Constraint F) : Json :=
  Json.mkObj [
    ("A", linCombToJson c.A),
    ("B", linCombToJson c.B),
    ("C", linCombToJson c.C)
  ]

/-- Pretty-print one R1CS constraint as `A * B = C`. -/
def constraintToHuman (c : R1CS.Constraint F) : String :=
  s!"({linCombToHuman c.A}) * ({linCombToHuman c.B}) = ({linCombToHuman c.C})"

/-- Count regular (`.var n`) wire slots: one past the maximum `.var` index seen, or 0. -/
def countRegVars (constraints : List (R1CS.Constraint F)) : Nat :=
  let sumLC : R1CS.LinComb F → Nat → Nat := fun lc acc =>
    lc.foldl (fun a (v, _) =>
      match v with
      | .var n => max a (n + 1)
      | _      => a) acc
  let sumC : R1CS.Constraint F → Nat → Nat := fun c acc =>
    sumLC c.A (sumLC c.B (sumLC c.C acc))
  constraints.foldl (fun acc c => sumC c acc) 0

/-- Count auxiliary `.aux n` wire slots: `max (.aux n) + 1` across all constraints. -/
def countAuxVars (constraints : List (R1CS.Constraint F)) : Nat :=
  let sumLC : R1CS.LinComb F → Nat → Nat := fun lc acc =>
    lc.foldl (fun a (v, _) =>
      match v with
      | .aux n => max a (n + 1)
      | _ => a) acc
  let sumC : R1CS.Constraint F → Nat → Nat := fun c acc =>
    sumLC c.A (sumLC c.B (sumLC c.C acc))
  constraints.foldl (fun acc c => sumC c acc) 0

/-- Count auxiliary `.auxIsZero n` wire slots: `max (.auxIsZero n) + 1` across all constraints. -/
def countAuxIsZeroVars (constraints : List (R1CS.Constraint F)) : Nat :=
  let sumLC : R1CS.LinComb F → Nat → Nat := fun lc acc =>
    lc.foldl (fun a (v, _) =>
      match v with
      | .auxIsZero n => max a (n + 1)
      | _ => a) acc
  let sumC : R1CS.Constraint F → Nat → Nat := fun c acc =>
    sumLC c.A (sumLC c.B (sumLC c.C acc))
  constraints.foldl (fun acc c => sumC c acc) 0

/-- Total number of wire slots (including `varOne`): `1 + numRegVars + numAuxVars`. -/
def countTotalVars (constraints : List (R1CS.Constraint F)) : Nat :=
  1 + countRegVars constraints + countAuxVars constraints

/-- Summary of constraint and wire counts for a serialized R1CS system. -/
structure SystemSummary (F : Type) where
  /-- Total number of R1CS constraints. -/
  numConstraints  : Nat
  /-- Number of regular `.var n` wire slots. -/
  numRegVars      : Nat
  /-- Number of auxiliary `.aux n` wire slots. -/
  numAuxVars      : Nat
  /-- Number of public input wires. -/
  numPublicInputs : Nat
  /-- The constraint list. -/
  constraints     : List (R1CS.Constraint F)

/-- Summarize constraint and wire counts for JSON and human-readable output. -/
def summarize [Repr F] (sys : R1CS.System F) : SystemSummary F :=
  { numConstraints  := sys.constraints.length
    numRegVars      := countRegVars sys.constraints
    numAuxVars      := countAuxVars sys.constraints
    numPublicInputs := sys.numPublicInputs
    constraints     := sys.constraints }

/-- Serialize a summarized R1CS system to JSON. -/
def summaryToJson [Repr F] (s : SystemSummary F) : Json :=
  Json.mkObj [
    ("numConstraints",  s.numConstraints),
    ("numWires",        1 + s.numRegVars + s.numAuxVars),
    ("numRegVars",      s.numRegVars),
    ("numAuxVars",      s.numAuxVars),
    ("numPublicInputs", s.numPublicInputs),
    ("constraints",     Json.arr <| s.constraints.toArray.map constraintToJson)
  ]

/-- Serialize an R1CS system to JSON after computing its summary counts. -/
def systemToJson [Repr F] (sys : R1CS.System F) : Json :=
  summaryToJson (summarize sys)

/-- Pretty-print whole R1CS system with summary header and numbered constraints. -/
def ppSystem [Repr F] (sys : R1CS.System F) : String :=
  let s := summarize sys
  let numWires := 1 + s.numRegVars + s.numAuxVars
  let header := s!"R1CS System: {s.numConstraints} constraints, " ++
                s!"{numWires} wires ({s.numRegVars} regular, {s.numAuxVars} aux), " ++
                s!"{s.numPublicInputs} public inputs"
  let body : List String := s.constraints.toArray.mapIdx (fun i c =>
    s!"  [{i}] {constraintToHuman c}") |>.toList
  String.intercalate "\n" (header :: body)

/-- Write JSON serialization of an R1CS system to `path`. -/
def saveR1CSJson [Repr F] (sys : R1CS.System F) (path : String) : IO Unit := do
  let json := systemToJson sys
  IO.FS.writeFile path (Json.pretty json)

end R1CSJSON
