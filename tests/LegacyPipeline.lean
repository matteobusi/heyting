import Heyting.Legacy.Pipeline
import Mathlib.Algebra.Field.Rat

namespace Legacy.Pipeline.Tests

-- The verified reference API remains available through its quarantined name.
#check Legacy.Pipeline.compileProgram
#check Legacy.Pipeline.compileFlatIR
#check Legacy.Pipeline.pipelineWitness

example : PresReflPass (StructIR.Language 0 ℚ) (R1CS.Language ℚ) := inferInstance

end Legacy.Pipeline.Tests
