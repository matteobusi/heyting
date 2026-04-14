import Mathlib.Algebra.Field.ZMod
import Heyting.Parsers.Main
import Heyting.Passes.Lowering
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRToR1CS

/-!
# Lowering Examples

Demonstrates the full LLZK → StructIR lowering pipeline using
`LLZK.Lowering.LLZK.lower` on real circuit files from `llzk-lib/test/`.

## Field

All examples use `ZMod 1993` (a prime field), same as `StructIRExamples.lean`.
-/

section
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.style.nativeDecide false

namespace Lowering.Examples

private abbrev lowerMod := @LLZK.Lowering.LLZK.lower

def p : ℕ := 1993
instance hp : Fact (Nat.Prime p) := ⟨by native_decide⟩
abbrev F := ZMod p

/-! ## Example 1: Simple lowering (emit_pass.llzk)

Parse a 5-struct circuit (`emit_pass.llzk`) where each struct has a simple
`@constrain` body with `constrain.eq`. Lower to StructIR and print a summary.
This is the simplest real-world case: no `nondet`, no arrays.
-/
#eval do
  let (mod, _warnings) ← LLZK.parseFile
    "llzk-lib/test/Dialect/Constrain/emit_pass.llzk"
  match lowerMod (F := F) mod with
  | .error e => IO.println s!"Lowering failed: {e}"
  | .ok ⟨m, sirMod⟩ =>
    IO.println "=== emit_pass.llzk: LLZK → StructIR ==="
    IO.println s!"Structs: {m + 1}"
    IO.println s!"Main struct name: {sirMod.structs ⟨m, Nat.lt_succ_self m⟩ |>.name}"
    IO.println s!"Main struct members: {(sirMod.structs ⟨m, Nat.lt_succ_self m⟩).members.length}"

/-! ## Example 2: Multi-struct lowering (emit_pass.llzk — all structs)

Parse `emit_pass.llzk`, lower to StructIR, and print all struct names
with their member counts and constrain body sizes.
-/
#eval do
  let (mod, _warnings) ← LLZK.parseFile
    "llzk-lib/test/Dialect/Constrain/emit_pass.llzk"
  match lowerMod (F := F) mod with
  | .error e => IO.println s!"Lowering failed: {e}"
  | .ok ⟨m, sirMod⟩ =>
    IO.println "=== emit_pass.llzk: all structs ==="
    for i in List.range (m + 1) do
      if h : i < m + 1 then
        let sd := sirMod.structs ⟨i, h⟩
        IO.println s!"  [{i}] {sd.name}: {sd.members.length} members, \
{sd.constrain.body.length} constrain stmts"

/-! ## Example 3: Full pipeline emit_pass.llzk → R1CS

Parse → lower → StructIR → FlatIR → R1CS.
Print the number of R1CS constraints produced. This demonstrates
the complete end-to-end pipeline from a real LLZK file to R1CS.
`emit_pass.llzk` (ComponentA–ComponentE) yields 4 R1CS constraints.
-/
#eval do
  let (mod, _warnings) ← LLZK.parseFile
    "llzk-lib/test/Dialect/Constrain/emit_pass.llzk"
  match lowerMod (F := F) mod with
  | .error e => IO.println s!"Lowering failed: {e}"
  | .ok ⟨_, sirMod⟩ =>
    let flatProg := StructIRToFlatIR.compileProgram sirMod
    let r1csSystem := FlatIRToR1CS.compileProgram F flatProg
    IO.println "=== Full pipeline: emit_pass.llzk → R1CS ==="
    IO.println s!"R1CS constraints: {r1csSystem.constraints.length}"

end Lowering.Examples
end -- section
