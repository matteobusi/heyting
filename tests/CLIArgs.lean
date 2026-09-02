import Heyting.CLIArgs

namespace Heyting.CLIArgs.Tests

def parsedOracle : Bool :=
  match parse ["compile", "input.llzk", "out", "--auto", "--oracle", "oracle.json"] with
  | .ok opts => opts.auto && opts.oracle? == some "oracle.json"
  | .error _ => false

#guard parsedOracle

def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard failed (parse ["compile", "input.llzk", "out", "--legacy"])
#guard failed (parse ["compile", "input.llzk", "out", "--dialect"])

end Heyting.CLIArgs.Tests
