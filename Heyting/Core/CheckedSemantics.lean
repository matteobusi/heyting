import Heyting.Core.Language

/-!
# Checked Semantics Infrastructure

Generic datatypes and relations for deterministic checked execution.

These definitions let a semantics return either a full successful trace or the
first failing step together with the checked prefix. They are reused by the
substitution-based checked semantics for `StructIR` and `FlatIR`.
-/

namespace CheckedSemantics

/--
Result of checked execution: either a full successful trace, or the checked
prefix together with the first failed step.
-/
inductive Result (Step : Type u) where
  | success (trace : List Step)
  | failure (checkedPrefix : List Step) (failed : Step)
  deriving Repr

namespace Result

variable {Step : Type u}

/-- Prefix one already-checked step to a checked result. -/
def prepend (step : Step) : Result Step → Result Step
  | .success trace => .success (step :: trace)
  | .failure checkedPrefix failed => .failure (step :: checkedPrefix) failed

/-- Prefix a list of already-checked steps to a checked result. -/
def appendPrefix (checkedPrefix : List Step) : Result Step → Result Step
  | .success trace => .success (checkedPrefix ++ trace)
  | .failure checkedPrefix' failed => .failure (checkedPrefix ++ checkedPrefix') failed

/-- Sequential composition of checked results with first-failure behavior. -/
def seq : Result Step → Result Step → Result Step
  | .failure checkedPrefix failed, _ => .failure checkedPrefix failed
  | .success left, .success right => .success (left ++ right)
  | .success left, .failure checkedPrefix failed => .failure (left ++ checkedPrefix) failed

end Result

variable {α β : Type}

/-- One-sided stuttering simulation between step traces. -/
inductive TraceStutter (R : α → β → Prop) : List α → List β → Prop where
  | nil : TraceStutter R [] []
  | step {a as b bs} : R a b → TraceStutter R as bs → TraceStutter R (a :: as) (b :: bs)
  | stutterTarget {as b bs} : TraceStutter R as bs → TraceStutter R as (b :: bs)

/-- Bidirectional stuttering simulation between traces. -/
def BiTraceStutter (R : α → β → Prop) (as : List α) (bs : List β) : Prop :=
  TraceStutter R as bs ∧ TraceStutter (fun b a => R a b) bs as

/-- Relation between checked execution results, split into trace and failed-step parts. -/
def ResultRel (traceRel : List α → List β → Prop) (stepRel : α → β → Prop) :
    Result α → Result β → Prop
  | .success srcTrace, .success tgtTrace => traceRel srcTrace tgtTrace
  | .failure srcPrefix srcFailed, .failure tgtPrefix tgtFailed =>
      traceRel srcPrefix tgtPrefix ∧ stepRel srcFailed tgtFailed
  | _, _ => False

end CheckedSemantics
