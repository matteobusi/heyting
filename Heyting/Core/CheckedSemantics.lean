import Heyting.Core.Language

namespace CheckedSemantics

inductive Result (Step : Type u) where
  | success (trace : List Step)
  | failure (checkedPrefix : List Step) (failed : Step)
  deriving Repr

namespace Result

variable {Step : Type u}

def prepend (step : Step) : Result Step → Result Step
  | .success trace => .success (step :: trace)
  | .failure checkedPrefix failed => .failure (step :: checkedPrefix) failed

def appendPrefix (checkedPrefix : List Step) : Result Step → Result Step
  | .success trace => .success (checkedPrefix ++ trace)
  | .failure checkedPrefix' failed => .failure (checkedPrefix ++ checkedPrefix') failed

def seq : Result Step → Result Step → Result Step
  | .failure checkedPrefix failed, _ => .failure checkedPrefix failed
  | .success left, .success right => .success (left ++ right)
  | .success left, .failure checkedPrefix failed => .failure (left ++ checkedPrefix) failed

end Result

variable {α β : Type}

inductive TraceStutter (R : α → β → Prop) : List α → List β → Prop where
  | nil : TraceStutter R [] []
  | step {a as b bs} : R a b → TraceStutter R as bs → TraceStutter R (a :: as) (b :: bs)
  | stutterTarget {as b bs} : TraceStutter R as bs → TraceStutter R as (b :: bs)

def BiTraceStutter (R : α → β → Prop) (as : List α) (bs : List β) : Prop :=
  TraceStutter R as bs ∧ TraceStutter (fun b a => R a b) bs as

def ResultRel (traceRel : List α → List β → Prop) (stepRel : α → β → Prop) :
    Result α → Result β → Prop
  | .success srcTrace, .success tgtTrace => traceRel srcTrace tgtTrace
  | .failure srcPrefix srcFailed, .failure tgtPrefix tgtFailed =>
      traceRel srcPrefix tgtPrefix ∧ stepRel srcFailed tgtFailed
  | _, _ => False

end CheckedSemantics
