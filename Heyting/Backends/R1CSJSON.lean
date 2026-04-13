import Lean.Data.Json
import Heyting.Languages.R1CS

namespace R1CSJSON

open R1CS Lean

variable {F : Type} [Field F] [Repr F]

def varIdToJson (v : R1CS.VarId) : Json :=
  match v with
  | .varOne => Json.mkObj [("tag", "varOne")]
  | .var n => Json.mkObj [("tag", "var"), ("index", n)]
  | .aux n => Json.mkObj [("tag", "aux"), ("index", n)]

def varIdToString (v : R1CS.VarId) : String :=
  match v with
  | .varOne => "ONE"
  | .var n => s!"v{n}"
  | .aux n => s!"aux{n}"

def fieldRepr (c : F) : String :=
  toString (repr c)

def fieldToJson (c : F) : Json :=
  Json.str (fieldRepr c)

def linCombToJson (lc : R1CS.LinComb F) : Json :=
  Json.arr <| lc.toArray.map fun (v, c) =>
    Json.mkObj [("var", varIdToJson v), ("coeff", fieldToJson c)]

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

def constraintToJson (c : R1CS.Constraint F) : Json :=
  Json.mkObj [
    ("A", linCombToJson c.A),
    ("B", linCombToJson c.B),
    ("C", linCombToJson c.C)
  ]

def constraintToHuman (c : R1CS.Constraint F) : String :=
  s!"({linCombToHuman c.A}) * ({linCombToHuman c.B}) = ({linCombToHuman c.C})"

def countVars (constraints : List (R1CS.Constraint F)) : Nat :=
  let goVar : R1CS.VarId → Nat → Nat := fun v acc =>
    match v with
    | .varOne => acc
    | .var n => max acc (n + 1)
    | .aux n => max acc (n + 1)
  let goLC : R1CS.LinComb F → Nat → Nat := fun lc acc =>
    lc.foldl (fun a (v, _) => goVar v a) acc
  let goC : R1CS.Constraint F → Nat → Nat := fun c acc =>
    goLC c.A (goLC c.B (goLC c.C acc))
  constraints.foldl (fun acc c => goC c acc) 0

def countAuxVars (constraints : List (R1CS.Constraint F)) : Nat :=
  let goLC : R1CS.LinComb F → Nat → Nat := fun lc acc =>
    lc.foldl (fun a (v, _) =>
      match v with
      | .aux n => max a (n + 1)
      | _ => a) acc
  let goC : R1CS.Constraint F → Nat → Nat := fun c acc =>
    goLC c.A (goLC c.B (goLC c.C acc))
  constraints.foldl (fun acc c => goC c acc) 0

structure SystemSummary (F : Type) where
  numConstraints  : Nat
  numVars         : Nat
  numAuxVars      : Nat
  numPublicInputs : Nat
  constraints     : List (R1CS.Constraint F)

def summarize [Repr F] (sys : R1CS.System F) : SystemSummary F :=
  { numConstraints  := sys.constraints.length
    numVars         := countVars sys.constraints
    numAuxVars      := countAuxVars sys.constraints
    numPublicInputs := sys.numPublicInputs
    constraints     := sys.constraints }

def summaryToJson [Repr F] (s : SystemSummary F) : Json :=
  Json.mkObj [
    ("numConstraints",  s.numConstraints),
    ("numVars",         s.numVars),
    ("numAuxVars",      s.numAuxVars),
    ("numPublicInputs", s.numPublicInputs),
    ("constraints",     Json.arr <| s.constraints.toArray.map constraintToJson)
  ]

def systemToJson [Repr F] (sys : R1CS.System F) : Json :=
  summaryToJson (summarize sys)

def ppConstraint (c : R1CS.Constraint F) : String :=
  constraintToHuman c

def ppSystem [Repr F] (sys : R1CS.System F) : String :=
  let s := summarize sys
  let header := s!"R1CS System: {s.numConstraints} constraints, " ++
                s!"{s.numVars} variables ({s.numAuxVars} aux), " ++
                s!"{s.numPublicInputs} public inputs"
  let body : List String := s.constraints.toArray.mapIdx (fun i c =>
    s!"  [{i}] {ppConstraint c}") |>.toList
  String.intercalate "\n" (header :: body)

def saveR1CSJson [Repr F] (sys : R1CS.System F) (path : String) : IO Unit := do
  let json := systemToJson sys
  IO.FS.writeFile path (Json.pretty json)

end R1CSJSON