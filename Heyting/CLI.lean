import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Heyting.Parser.Main
import Heyting.Passes.Lowering
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRToR1CS
import Heyting.Backends.R1CSJSON

namespace Heyting.CLI

inductive Command where
  | json (input : String) (output : String)
  | help
  deriving Repr

def usage : String :=
  "Usage: heytingc <command> [options]\n" ++
  "\n" ++
  "Commands:\n" ++
  "  json <input.llzk> <output.json>  Compile LLZK file to R1CS JSON\n" ++
  "  help                              Show this help message\n" ++
  "\n" ++
  "Options:\n" ++
  "  --field <prime>  Use the given prime for the field (default: 1993)"

def parseArgs (args : List String) : Except String Command :=
  match args with
  | [] => .error "No command given. Use 'heytingc help' for usage."
  | ["help"] => .ok .help
  | ["json", input, output] => .ok (.json input output)
  | "json" :: _ => .error "json command requires <input.llzk> <output.json>"
  | cmd :: _ => .error s!"Unknown command: {cmd}. Use 'heytingc help' for usage."

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

def runCommand : Command → IO Unit
  | .help => IO.println usage
  | .json input output => compileToJson input output

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .ok cmd => runCommand cmd
  | .error e => do
    IO.eprintln s!"Error: {e}"
    IO.eprintln usage

end Heyting.CLI