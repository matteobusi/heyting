/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Parsers.Main
import Heyting.CLIArgs
import Heyting.Passes.Lowering
import Heyting.Legacy.Pipeline
import Heyting.Passes.DialectPipeline
import Heyting.Backends.R1CSJSON
import Heyting.Backends.WitnessJSON
import Heyting.Backends.R1CSBinary
import Heyting.Backends.WitnessBinary
import Heyting.Parsers.InputJSON
import Heyting.Languages.StructIR

/-!
# Command-Line Interface

Executable entry point for `hey`.

The CLI parses LLZK source files and selects either the primary dialect-native
pipeline or the quarantined `Legacy.Pipeline` reference path. Both produce
constraints and witnesses independently.
-/

namespace Heyting.CLI

open CLIArgs FieldBytes

/-
  Default supported prime fields, taken from llzk-lin/lin/Util/Field.cpp
-/

-- bn128/254, default for circom/snarkjs. Use BN128 scalar field `r`, which is
-- the modulus expected by Circom `.r1cs` / `.wtns` tooling.
private def BN128_p := 21888242871839275222246405745257275088548364400416034343698204186575808495617
private axiom BN128_prime : Fact (Nat.Prime BN128_p)
attribute [instance] BN128_prime

-- fieldSize = 32 bytes (256 bits, rounded to multiple of 8)
private instance : FieldBytes (ZMod BN128_p) where
  fieldSize    := 32
  toLeBytes    := fun x => natLeBytes x.val 32
  primeLeBytes := natLeBytes BN128_p 32

private def BN254_p := 21888242871839275222246405745257275088548364400416034343698204186575808495617
private axiom BN254_prime : Fact (Nat.Prime BN254_p)
attribute [instance] BN254_prime

private instance : FieldBytes (ZMod BN254_p) where
  fieldSize    := 32
  toLeBytes    := fun x => natLeBytes x.val 32
  primeLeBytes := natLeBytes BN254_p 32

-- 15 * 2^27 + 1, default for zirgen (31-bit prime, stored in 4 bytes)
private def BABYBEAR_p := 2013265921
private axiom BABYBEAR_prime : Fact (Nat.Prime BABYBEAR_p)
attribute [instance] BABYBEAR_prime

private instance : FieldBytes (ZMod BABYBEAR_p) where
  fieldSize    := 4
  toLeBytes    := fun x => natLeBytes x.val 4
  primeLeBytes := natLeBytes BABYBEAR_p 4

-- 2^64 - 2^32 + 1, used for plonky2 (64-bit prime, stored in 8 bytes)
private def GOLDILOCKS_p := 18446744069414584321
private axiom GOLDILOCKS_prime : Fact (Nat.Prime GOLDILOCKS_p)
attribute [instance] GOLDILOCKS_prime

private instance : FieldBytes (ZMod GOLDILOCKS_p) where
  fieldSize    := 8
  toLeBytes    := fun x => natLeBytes x.val 8
  primeLeBytes := natLeBytes GOLDILOCKS_p 8

-- 2^31 - 1, used for Plonky3 (31-bit prime, stored in 4 bytes)
private def MERSENNE31_p := 2147483647
private axiom MERSENNE31_prime : Fact (Nat.Prime MERSENNE31_p)
attribute [instance] MERSENNE31_prime

private instance : FieldBytes (ZMod MERSENNE31_p) where
  fieldSize    := 4
  toLeBytes    := fun x => natLeBytes x.val 4
  primeLeBytes := natLeBytes MERSENNE31_p 4

-- 2^31 - 2^24 + 1, also for Plonky3 (31-bit prime, stored in 4 bytes)
private def KOALABEAR_p := 2130706433
private axiom KOALABEAR_prime : Fact (Nat.Prime KOALABEAR_p)
attribute [instance] KOALABEAR_prime

private instance : FieldBytes (ZMod KOALABEAR_p) where
  fieldSize    := 4
  toLeBytes    := fun x => natLeBytes x.val 4
  primeLeBytes := natLeBytes KOALABEAR_p 4

/-! ## Commands and argument handling -/

/-- Explicit compiler architecture selection. -/
inductive PipelineMode where
  | legacy
  | dialect
  deriving Repr, DecidableEq

/-- Supported top-level CLI commands. -/
inductive Command where
  | compile (llzk : String) (output : String) (json : Bool)
      (auto : Bool) (input oracle : Option String) (prime : Option String)
      (pipeline : PipelineMode)
  | help
  deriving Repr

/-- Human-readable usage text for `hey`. -/
def usage : String :=
  "Usage: hey compile [options] <input.llzk> <output>\n" ++
  "       hey help\n" ++
  "\n" ++
  "Compile an LLZK circuit file to R1CS.\n" ++
  "\n" ++
  "Options:\n" ++
  "  --json             produce human-readable R1CS JSON (default: Circom binary .r1cs)\n" ++
  "  --auto             auto-generate witness from compute bodies\n" ++
  "                       (writes <output>.wtns binary, or .witness.json with --json)\n" ++
  "  --input <path>     JSON file of public circuit inputs (field elements)\n" ++
  "                       (keys are signal names; missing signals default to 0)\n" ++
  "  --oracle <path>    JSON array of values consumed by llzk.nondet\n" ++
  "  --dialect          explicitly use the dialect-native pipeline (default)\n" ++
  "  --legacy           explicitly use the StructIR reference pipeline\n" ++
  "                       (verified reference escape hatch)\n" ++
  "  --prime-field <p>  use a specific prime field, " ++
    " supported: bn128, bn254 (default), babybear, goldilocks, mersenne31, and koalabear\n" ++
  "  --output <path>    alternative way to specify output path\n"

/-- Interpret parsed option structure as a top-level CLI command. -/
def parseArgs (args : List String) : Except String Command :=
  match CLIArgs.parse args with
  | .error e => .error e
  | .ok opts =>
    if opts.cmd == "" then
      .error "no command given; try 'hey help'"
    else if opts.cmd == "help" then
      .ok .help
    else if opts.cmd == "compile" then
      if opts.dialect && opts.legacy then
        .error "--dialect and --legacy are mutually exclusive"
      else
        let pipeline := if opts.legacy then PipelineMode.legacy else PipelineMode.dialect
        match opts.llzk?, opts.output? with
        | some i, some o =>
          .ok (.compile i o opts.json opts.auto opts.input? opts.oracle? opts.prime? pipeline)
        | some _, none => .error "compile requires an output path"
        | none, _ => .error "compile requires an input file"
    else
      .error s!"unknown command: {opts.cmd}. Try 'hey help'."


/-- Write an R1CS system in the selected format. -/
private def saveR1CS
    (F : Type) [Field F] [Repr F] [FieldBytes F]
    (fieldName outputPath : String) (useJson : Bool)
    (system : R1CS.System F) : IO Unit := do
  let pathParts := outputPath.splitOn "/"
  let outDir := String.intercalate "/" pathParts.dropLast
  if outDir != "" then
    IO.FS.createDirAll outDir
  if useJson then
    let r1csPath := outputPath ++ ".r1cs.json"
    R1CSJSON.saveR1CSJson (F := F) system r1csPath
    IO.println s!"Wrote R1CS JSON to {r1csPath} (field: {fieldName})"
  else
    let r1csPath := outputPath ++ ".r1cs"
    R1CSBinary.saveR1CSBinary (F := F) system r1csPath
    IO.println s!"Wrote R1CS binary to {r1csPath} (field: {fieldName})"
  IO.println s!"  Constraints: {system.constraints.length}"
  IO.println s!"  Wires: {R1CSJSON.countTotalVars system.constraints}"

/-- Compile one LLZK input file under a chosen field and write requested outputs. -/
def compileAndSave
    (F : Type) [Field F] [DecidableEq F] [IntCast F] [Repr F] [FieldBytes F]
    (fieldName : String)
    (inputPath : String) (outputPath : String)
    (useJson : Bool) (autoWitness : Bool) (inputsPath : Option String)
    (oraclePath : Option String)
    (pipeline : PipelineMode) : IO Unit := do
  let (mod, _warnings) ← LLZK.parseFile inputPath
  -- Extract param names from the original AST before lowering discards them.
  -- The main struct is the last in topological order; its @compute params are
  -- [ signal_1, signal_2, ...].  Differently from @constrain we do not skip index 0.
  let computeParamNames : List String :=
    match LLZK.Lowering.topoSort mod.structs with
    | .error _ => []
    | .ok sorted =>
      match sorted.getLast? with
      | none => []
      | some mainSd =>
        match mainSd.funcs.find? (fun f => f.name == "compute") with
        | none => []
        | some computeFn => computeFn.params.map (·.name)
  -- Determine inputs for witness generation (--auto or --input).
  let witnessInputs : Option (List F) ←
    if let some jsonPath := inputsPath then
      let jsonStr ← IO.FS.readFile jsonPath
      match InputJSON.parseInputsJson F computeParamNames jsonStr with
      | .error e => throw (IO.userError s!"Failed to parse inputs JSON: {e}")
      | .ok inputs =>
        IO.eprintln s!"inputs: { repr inputs }"
        pure (some inputs)
    else if autoWitness then
      pure (some ([] : List F))
    else
      pure none
  let oracleValues : List F ←
    if let some jsonPath := oraclePath then
      let jsonStr ← IO.FS.readFile jsonPath
      match InputJSON.parseOracleJson F jsonStr with
      | .error e => throw (IO.userError s!"Failed to parse oracle JSON: {e}")
      | .ok values => pure values
    else pure []
  if oraclePath.isSome && pipeline == .legacy then
    throw (IO.userError "--oracle is supported only by the dialect pipeline")
  if oraclePath.isSome && witnessInputs.isNone then
    throw (IO.userError "--oracle requires --auto or --input")
  if pipeline == .dialect then
    let artifact ← match witnessInputs with
      | none =>
        match Dialect.Pipeline.compileAST (F := F) mod with
        | .error e => throw (IO.userError s!"Dialect lowering failed: {e}")
        | .ok system => pure (system, none)
      | some inputs =>
        match Dialect.Pipeline.witnessAST (F := F) mod inputs oracleValues with
        | .error e => throw (IO.userError s!"Dialect witness generation failed: {e}")
        | .ok (system, witness) => pure (system, some witness)
    saveR1CS F fieldName outputPath useJson artifact.1
    if let some witness := artifact.2 then
      if useJson then
        let witnessPath := outputPath ++ ".witness.json"
        WitnessJSON.saveWitnessJson (F:=F) artifact.1 witness witnessPath
        IO.println s!"Wrote witness JSON to {witnessPath}"
      else
        let witnessPath := outputPath ++ ".wtns"
        WitnessBinary.saveWitnessBinary (F:=F) artifact.1 witness witnessPath
        IO.println s!"Wrote witness binary to {witnessPath}"
  else
    match LLZK.Lowering.LLZK.lower (F:=F) mod with
    | .error e => throw (IO.userError s!"Lowering failed: {e}")
    | .ok ⟨_, sirMod⟩ =>
    -- Use the pipeline pass to compile StructIR → FlatIR → R1CS in one step.
      let r1csSystem := Legacy.Pipeline.compileProgram (F:=F) sirMod
      saveR1CS F fieldName outputPath useJson r1csSystem
      if let some inputs := witnessInputs then
        match Legacy.Pipeline.pipelineWitness (F:=F) sirMod inputs with
        | none =>
          IO.eprintln "Warning: witness generation failed (division by zero in @compute body)"
          IO.eprintln "  Skipping witness output."
        | some wr =>
          if useJson then
            let witnessPath := outputPath ++ ".witness.json"
            WitnessJSON.saveWitnessJson (F:=F) r1csSystem wr witnessPath
            IO.println s!"Wrote witness JSON to {witnessPath}"
          else
            let witnessPath := outputPath ++ ".wtns"
            WitnessBinary.saveWitnessBinary (F:=F) r1csSystem wr witnessPath
            IO.println s!"Wrote witness binary to {witnessPath}"

/-- Resolve a parsed command to its executable `IO` action. -/
def runCommand : Command → Except String (IO Unit)
  | .help => .ok (IO.println usage)
  | .compile llzk output json auto inputs oracle field pipeline => .ok do
    match field with
    | none => compileAndSave (F:=ZMod BN254_p) "bn254" llzk output json auto inputs oracle pipeline
    | some field =>
      if field == "bn128" then
        compileAndSave (F:=ZMod BN128_p) field llzk output json auto inputs oracle pipeline
      else if field == "bn254" then
        compileAndSave (F:=ZMod BN254_p) field llzk output json auto inputs oracle pipeline
      else if field == "babybear" then
        compileAndSave (F:=ZMod BABYBEAR_p) field llzk output json auto inputs oracle pipeline
      else if field == "goldilocks" then
        compileAndSave (F:=ZMod GOLDILOCKS_p) field llzk output json auto inputs oracle pipeline
      else if field == "mersenne31" then
        compileAndSave (F:=ZMod MERSENNE31_p) field llzk output json auto inputs oracle pipeline
      else if field == "koalabear" then
        compileAndSave (F:=ZMod KOALABEAR_p) field llzk output json auto inputs oracle pipeline
      else
        throw (.userError s!"unsupported prime field: {field}. \
          Supported: bn128, bn254 (default), babybear, goldilocks, mersenne31, and koalabear")

/-- Process command-line arguments and run `hey`. -/
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
