import Mathlib.Algebra.Field.ZMod
import Heyting.CLI

/-!
# R1CS Output Examples

This file demonstrates JSON serialization of R1CS systems produced by the
Heyting compiler pipeline.

It uses `ZMod 1993` (a small prime field) for fast `#eval` turnaround.
Production use goes through `hey compile --prime-field <name>`.
-/

section
set_option linter.style.nativeDecide false

namespace OutputExamples

private def p : ℕ := 1993
private instance : Fact (Nat.Prime p) := ⟨by native_decide⟩

#eval do
  IO.println "=== Example 1: JSON Output for emit_pass.llzk (ZMod 1993) ==="
  let inPath := "llzk-lib/test/Dialect/Constrain/emit_pass.llzk"
  let outPath := "out/emit_pass.json"
  IO.FS.createDirAll "out"
  Heyting.CLI.compileToJson (F := ZMod p) "F1993" inPath outPath

#eval do
  IO.println "\n=== Example 2: JSON Output for circom_isZero.llzk (ZMod 1993) ==="
  let inPath := "llzk-lib/test/Conversions/circom_isZero.llzk"
  let outPath := "out/circom_isZero.json"
  IO.FS.createDirAll "out"
  Heyting.CLI.compileToJson (F := ZMod p) "F1993" inPath outPath

end OutputExamples
end
