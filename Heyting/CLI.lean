import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Parser.Main
import Heyting.CLIArgs
import Heyting.Passes.Lowering
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRToR1CS
import Heyting.Backends.R1CSJSON

namespace Heyting.CLI

open CLIArgs

inductive Command where
  | compile (input : String) (output : String) (json : Bool)
      (auto : Bool) (witness : Option String)
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
  "                       (not yet implemented)\n" ++
  "  --witness <path>   use user-supplied witness JSON\n" ++
  "                       (not yet implemented)\n" ++
  "  --input <path>     alternative way to specify input file\n" ++
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
      match opts.input?, opts.output? with
      | some i, some o =>
        .ok (.compile i o opts.json opts.auto opts.witness?)
      | some _, none => .error "compile requires an output path"
      | none, _ => .error "compile requires an input file"
    else
      .error s!"unknown command: {opts.cmd}. Try 'hey help'."

private instance : Fact (Nat.Prime 1993) := ⟨by norm_num⟩

def compileToJson (inputPath : String) (outputPath : String) : IO Unit := do
  let (mod, _warnings) ← LLZK.parseFile inputPath
  match LLZK.Lowering.LLZK.lower (F := ZMod 1993) mod with
  | .error e => throw (.userError s!"Lowering failed: {e}")
  | .ok ⟨_, sirMod⟩ =>
    let flatProg := StructIRToFlatIR.compileProgram sirMod
    let r1csSystem := FlatIRToR1CS.compileProgram (F := ZMod 1993) flatProg
    R1CSJSON.saveR1CSJson r1csSystem outputPath
    IO.println s!"Wrote R1CS JSON to {outputPath}"
    IO.println s!"  Constraints: {r1csSystem.constraints.length}"
    IO.println s!"  Variables: {R1CSJSON.countVars r1csSystem.constraints}"

def runCommand : Command → Except String (IO Unit)
  | .help => .ok (IO.println usage)
  | .compile input output _json auto witness => .ok do
    if auto then
      throw (.userError
        "--auto is not yet implemented: witness generation from compute \
         bodies is under development")
    if witness.isSome then
      throw (.userError
        "--witness is not yet implemented: user-supplied witness loading \
         is under development")
    compileToJson input output

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