import Heyting.CLI

/-!
# R1CS Output Examples

This file demonstrates JSON and (later) binary serialization of R1CS systems
produced by the Heyting compiler pipeline.

It serves as a visual check that the serialization produces the expected output.
-/

namespace OutputExamples

/- We execute the CLI's compileToJson function directly.
   In practice, this would be run via the `heytingc json` command line. -/

#eval do
  IO.println "=== Example 1: JSON Output for emit_pass.llzk ==="
  let inPath := "llzk-lib/test/Dialect/Constrain/emit_pass.llzk"
  let outPath := "out/emit_pass.json"
  IO.FS.createDirAll "out"
  Heyting.CLI.compileToJson inPath outPath

#eval do
  IO.println "\n=== Example 2: JSON Output for circom_isZero.llzk ==="
  let inPath := "llzk-lib/test/Conversions/circom_isZero.llzk"
  let outPath := "out/circom_isZero.json"
  IO.FS.createDirAll "out"
  Heyting.CLI.compileToJson inPath outPath

end OutputExamples