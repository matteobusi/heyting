import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Parser.Main
import Heyting.CLIArgs
import Heyting.Passes.Lowering
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRToR1CS
import Heyting.Passes.Pipeline
import Heyting.Backends.R1CSJSON
import Heyting.Backends.InputJSON
import Heyting.Languages.StructIR

namespace Heyting.CLI

open CLIArgs

/-
  Default supported prime fields, taken from llzk-lin/lin/Util/Field.cpp
-/

-- bn128/254, default for circom
private def BN128_p := 21888242871839275222246405745257275088696311157297823662689037894645226208583
private axiom BN128_prime : Fact (Nat.Prime BN128_p)
attribute [instance] BN128_prime

private def BN254_p := 21888242871839275222246405745257275088696311157297823662689037894645226208583
private axiom BN254_prime : Fact (Nat.Prime BN254_p)
attribute [instance] BN254_prime

-- 15 * 2^27 + 1, default for zirgen
private def BABYBEAR_p := 2013265921
private axiom BABYBEAR_prime : Fact (Nat.Prime BABYBEAR_p)
attribute [instance] BABYBEAR_prime

-- 2^64 - 2^32 + 1, used for plonky2
private def GOLDILOCKS_p := 18446744069414584321
private axiom GOLDILOCKS_prime : Fact (Nat.Prime GOLDILOCKS_p)
attribute [instance] GOLDILOCKS_prime

-- 2^31 - 1, used for Plonky3
private def MERSENNE31_p := 2147483647
private axiom MERSENNE31_prime : Fact (Nat.Prime MERSENNE31_p)
attribute [instance] MERSENNE31_prime

-- 2^31 - 2^24 + 1, also for Plonky3
private def KOALABEAR_p := 2130706433
private axiom KOALABEAR_prime : Fact (Nat.Prime KOALABEAR_p)
attribute [instance] KOALABEAR_prime

inductive Command where
  | compile (llzk : String) (output : String) (json : Bool)
      (auto : Bool) (input : Option String) (prime : Option String)
  | help
  deriving Repr

def usage : String :=
  "Usage: hey compile [options] <input.llzk> <output>\n" ++
  "       hey help\n" ++
  "\n" ++
  "Compile an LLZK circuit file to R1CS.\n" ++
  "\n" ++
  "Options:\n" ++
  "  --json             produce human-readable R1CS JSON\n" ++
  "  --auto             auto-generate witness from compute bodies\n" ++
  "                       (writes <output>.witness.json alongside R1CS)\n" ++
  "  --input <path>     JSON file of public circuit inputs (field elements)\n" ++
  "                       (keys are signal names; missing signals default to 0)\n" ++
  "  --prime-field <p>  use a specific prime field, " ++
    " supported: bn128, bn254 (default), babybear, goldilocks, mersenne31, and koalabear\n" ++
  "  --output <path>    alternative way to specify output path\n"

def parseArgs (args : List String) : Except String Command :=
  match CLIArgs.parse args with
  | .error e => .error e
  | .ok opts =>
    if opts.cmd == "" then
      .error "no command given; try 'hey help'"
    else if opts.cmd == "help" then
      .ok .help
    else if opts.cmd == "compile" then
      match opts.llzk?, opts.output? with
      | some i, some o =>
        .ok (.compile i o opts.json opts.auto opts.input? opts.prime?)
      | some _, none => .error "compile requires an output path"
      | none, _ => .error "compile requires an input file"
    else
      .error s!"unknown command: {opts.cmd}. Try 'hey help'."


def compileToJson
  (F : Type) [Field F] [DecidableEq F] [IntCast F] [Repr F]
  (fieldName : String)
  (inputPath : String) (outputPath : String) (autoWitness : Bool)
  (inputsPath : Option String) : IO Unit := do
  let (mod, _warnings) ← LLZK.parseFile inputPath
  -- Extract param names from the original AST before lowering discards them.
  -- The main struct is the last in topological order; its @compute params are
  -- [self, signal_1, signal_2, ...].  We skip index 0 (%self).
  let computeParamNames : List String :=
    match LLZK.Lowering.topoSort mod.structs with
    | .error _ => []
    | .ok sorted =>
      match sorted.getLast? with
      | none => []
      | some mainSd =>
        match mainSd.funcs.find? (fun f => f.name == "compute") with
        | none => []
        | some computeFn => (computeFn.params.drop 1).map (·.name)
  match LLZK.Lowering.LLZK.lower (F:=F) mod with
  | .error e => throw (IO.userError s!"Lowering failed: {e}")
  | .ok ⟨_, sirMod⟩ =>
    -- Use the pipeline pass to compile StructIR → FlatIR → R1CS in one step.
    let r1csSystem := Pipeline.compileProgram (F:=F) sirMod
    R1CSJSON.saveR1CSJson (F:=F) r1csSystem outputPath
    IO.println s!"Wrote R1CS JSON to {outputPath} (field: {fieldName})"
    IO.println s!"  Constraints: {r1csSystem.constraints.length}"
    IO.println s!"  Variables: {R1CSJSON.countVars r1csSystem.constraints}"
    -- Determine inputs for witness generation (--auto or --input).
    let witnessInputs : Option (List F) ←
      if let some jsonPath := inputsPath then
        -- --input: load and parse the JSON inputs file
        let jsonStr ← IO.FS.readFile jsonPath
        match InputJSON.parseInputsJson F computeParamNames jsonStr with
        | .error e => throw (IO.userError s!"Failed to parse inputs JSON: {e}")
        | .ok inputs => pure (some (0 :: inputs))  -- prepend 0 for %self at index 0
      else if autoWitness then
        -- --auto: run with empty inputs (all signals default to 0)
        pure (some ([] : List F))
      else
        pure none
    if let some inputs := witnessInputs then
      let witnessPath := outputPath ++ ".witness.json"
      match Pipeline.pipelineWitness (F:=F) sirMod inputs with
      | none =>
        IO.eprintln "Warning: witness generation failed (division by zero in @compute body)"
        IO.eprintln "  Skipping witness output."
      | some _wr =>
        -- `_wr : R1CS.Witness F` is the fully-threaded R1CS witness.
        -- Serialization of the R1CS witness is pending; emit a placeholder for now.
        let placeholder : Lean.Json := Lean.Json.mkObj [
          ("status", Lean.Json.str "generated"),
          ("note",   Lean.Json.str
            "R1CS witness produced by Pipeline.pipelineWitness; serialization pending.")]
        IO.FS.writeFile witnessPath (Lean.Json.pretty placeholder)
        IO.println s!"Wrote witness JSON to {witnessPath}"

def runCommand : Command → Except String (IO Unit)
  | .help => .ok (IO.println usage)
  | .compile llzk output _json auto inputs field => .ok do
    match field with
    | none => compileToJson (F:=ZMod BN254_p) "bn254" llzk output auto inputs
    | some field =>
      if field == "bn128" then
        compileToJson (F:=ZMod BN128_p) field llzk output auto inputs
      else if field == "bn254" then
        compileToJson (F:=ZMod BN254_p) field llzk output auto inputs
      else if field == "babybear" then
        compileToJson (F:=ZMod BABYBEAR_p) field llzk output auto inputs
      else if field == "goldilocks" then
        compileToJson (F:=ZMod GOLDILOCKS_p) field llzk output auto inputs
      else if field == "mersenne31" then
        compileToJson (F:=ZMod MERSENNE31_p) field llzk output auto inputs
      else if field == "koalabear" then
        compileToJson (F:=ZMod KOALABEAR_p) field llzk output auto inputs
      else
        throw (.userError s!"unsupported prime field: {field}. \
          Supported: bn128, bn254 (default), babybear, goldilocks, mersenne31, and koalabear")

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .ok cmd =>
    (match runCommand cmd with
    | .ok res => res
    | .error e => do
      IO.eprintln s!"Error: {e}"
      IO.eprintln usage)
  | .error e => do
    IO.eprintln s!"Error: {e}"
    IO.eprintln usage

end Heyting.CLI
