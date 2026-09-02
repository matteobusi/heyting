import Heyting.CLI

namespace Heyting.CLI.Tests

def isLegacy : Except String Command → Bool
  | .ok (.compile _ _ _ _ _ _ _ .legacy) => true
  | _ => false

def isDialect : Except String Command → Bool
  | .ok (.compile _ _ _ _ _ _ _ .dialect) => true
  | _ => false

def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard isDialect (parseArgs ["compile", "in.llzk", "out"])
#guard isLegacy (parseArgs ["compile", "in.llzk", "out", "--legacy"])
#guard isDialect (parseArgs ["compile", "in.llzk", "out", "--dialect"])
#guard failed (parseArgs
  ["compile", "in.llzk", "out", "--legacy", "--dialect"])

end Heyting.CLI.Tests
