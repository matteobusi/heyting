import Heyting.Parser.Main

/-!
# Parser Examples

Demonstrates parsing real LLZK circuit files from `llzk-lib/test/Dialect/`
using `LLZK.parseFile`. Each example reads a file, parses it into the
untyped `LLZK.Module` AST, and pretty-prints the result.

These are the same files used to validate the parser during development.
-/

namespace Parser.Examples

/-!
## Example 1: Constraint emission (`emit_pass.llzk`)

5 structs (ComponentA–E), each with a `@constrain` function containing
`constrain.eq` and/or `constrain.in` (the latter is skipped with a warning).
-/

#eval do
  let (mod, warnings) ← LLZK.parseFile "llzk-lib/test/Dialect/Constrain/emit_pass.llzk"
  IO.println "=== emit_pass.llzk ==="
  IO.println (LLZK.countStmts mod)
  IO.println (LLZK.ppModule mod)
  if !warnings.isEmpty then
    IO.println s!"\nWarnings ({warnings.length}):"
    for w in warnings do IO.println s!"  ⚠ {w}"

/-!
## Example 2: Nondet + constraints (`nondet_preservation.llzk`)

1 struct with `@compute` (using `llzk.nondet` and felt ops) and
`@constrain` (using `constrain.eq`). This is the simplest complete
circuit: compute a witness value nondeterministically, then constrain it.
-/

#eval do
  let (mod, warnings) ← LLZK.parseFile
    "llzk-lib/test/Dialect/LLZK_and_Builtin/nondet_preservation.llzk"
  IO.println "=== nondet_preservation.llzk ==="
  IO.println (LLZK.countStmts mod)
  IO.println (LLZK.ppModule mod)
  if !warnings.isEmpty then
    IO.println s!"\nWarnings ({warnings.length}):"
    for w in warnings do IO.println s!"  ⚠ {w}"

/-!
## Example 3: Circom circuits (`circomlib.llzk`)

2 structs (IsZero, IsEqual) with qualified cross-struct calls like
`function.call @IsZero::@constrain(...)`. Demonstrates parsing of
nested modules, felt arithmetic, and struct operations. Array and
arith ops are skipped with warnings.
-/

#eval do
  let (mod, warnings) ← LLZK.parseFile
    "llzk-lib/test/FrontendLang/Circom/circomlib.llzk"
  IO.println "=== circomlib.llzk ==="
  IO.println (LLZK.countStmts mod)
  IO.println (LLZK.ppModule mod)
  if !warnings.isEmpty then
    IO.println s!"\nWarnings ({warnings.length}):"
    for w in warnings do IO.println s!"  ⚠ {w}"

/-!
## Example 4: Felt arithmetic (`felt_arith_pass.llzk`)

Multi-section file with free functions testing felt ops (add, sub, mul,
div, neg, inv) and unsupported ops (shr, shl, pow, bit_*). All content
is in free functions (no structs), so the parser correctly produces an
empty module — free functions outside structs are not representable
in StructIR.
-/

#eval do
  let (mod, warnings) ← LLZK.parseFile
    "llzk-lib/test/Dialect/Felt/felt_arith_pass.llzk"
  IO.println "=== felt_arith_pass.llzk ==="
  IO.println (LLZK.countStmts mod)
  IO.println s!"(Empty module — {warnings.length} free functions skipped)"

/-!
## Example 5: Struct operations (`structs_pass.llzk`)

25 structs across multiple sections, testing struct.new, struct.readm,
struct.writem, and qualified function calls. Some structs have template
parameters (skipped with warnings). Largest test file for the parser.
-/

#eval do
  let (mod, warnings) ← LLZK.parseFile
    "llzk-lib/test/Dialect/Struct/structs_pass.llzk"
  IO.println "=== structs_pass.llzk ==="
  IO.println (LLZK.countStmts mod)
  let names := mod.structs.map LLZK.StructDef.name
  IO.println s!"Parsed structs: {names}"
  if !warnings.isEmpty then
    IO.println s!"\nWarnings ({warnings.length}):"
    for w in warnings do IO.println s!"  ⚠ {w}"

end Parser.Examples
