import Heyting.Test.R1CSJSONTest
import Heyting.Test.InputJSONTest
import Heyting.Test.BinaryTest

import Heyting.Examples.StructIRExamples
import Heyting.Examples.ParserExamples
import Heyting.Examples.LoweringExamples
import Heyting.Examples.OutputExamples

/-!
# Test entry point

Importing the test and example modules above causes their `#eval` blocks
to run at elaboration time. `main` itself does nothing; all output is
produced by those blocks.

Run with:
  lake exe tests
-/

def main : IO Unit := pure ()
