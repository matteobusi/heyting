import Heyting.CLI

namespace Heyting.CLI.Tests

def isCompile : Except String Command → Bool
  | .ok (.compile "in.llzk" "out" false false none none none) => true
  | _ => false

def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard isCompile (parseArgs ["compile", "in.llzk", "out"])
#guard failed (parseArgs ["compile", "in.llzk", "out", "--legacy"])
#guard failed (parseArgs ["compile", "in.llzk", "out", "--dialect"])

end Heyting.CLI.Tests
