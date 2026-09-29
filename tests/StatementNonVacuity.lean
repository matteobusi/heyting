import Heyting.Passes.DialectPipeline
import Mathlib.Algebra.Field.Rat

/-!
# Non-vacuity of the user-level entry theorems

`typed_entry_correct` and its corollaries quantify over compiled entries and source
observations. This file instantiates them on a concrete circuit (`a * b = 6`, reserved
`self` slot) to show that:

* the hypotheses are inhabited: a real typed module compiles to an artifact;
* the source predicate discriminates: some canonical observations satisfy it and some do not;
* the conclusions carry information: a satisfying observation yields a concrete satisfying
  R1CS witness, an unsatisfying one is rejected by *every* R1CS assignment reading back to it.
-/

namespace Dialect.StatementNonVacuity

open Dialect.Pipeline

abbrev SourceSet := TypedSourceSemantics.SourceSet

def entry : Fin 1 := ⟨0, by decide⟩

def product : StructDef SourceSet 1 entry ℚ where
  name := "product"
  members := []
  compute := { numParams := 2, body := [], returnVar := none,
               wf_caps := by rfl, wf_ssa := by rfl }
  constrain := {
    numParams := 3
    body := [.op ⟨3, by decide⟩ (.mul 3 1 2), .op ⟨3, by decide⟩ (.const 4 6),
             .op ⟨4, by decide⟩ (.eq 3 4)]
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def module : Module SourceSet 1 ℚ where
  structs
    | ⟨0, _⟩ => product

def good : SourceWitness ℚ := { inputs := [2, 3], objects := [] }
def bad : SourceWitness ℚ := { inputs := [2, 4], objects := [] }

/-! ## Concrete facts about the compiled entry

The certified compiler is executable but its `Except`-valued result is not reducible by the
kernel, so the finite facts below are decided by compiled evaluation (`native_decide`). Only
the theorems that use `facts_true` depend on `Lean.ofReduceBool`; everything downstream is a
theorem about an arbitrary artifact `c` with `compileTypedEntryArtifact module entry = .ok c`. -/

def facts : Bool :=
  match compileTypedEntryArtifact module entry with
  | .error _ => false
  | .ok c =>
    (good.inputs.length == c.artifact.computeParams &&
      good.objects.length == c.artifact.witnessSpan) &&
    (bad.inputs.length == c.artifact.computeParams &&
      bad.objects.length == c.artifact.witnessSpan) &&
    (c.artifact.forward good).isOk && (c.artifact.forward bad).isOk &&
    decide (c.artifact.paramOffset = 1) && decide (c.artifact.target.constraints.length ≥ 4)

theorem facts_true : facts = true := by native_decide

/-- The hypothesis of every entry theorem is inhabited by a real module. -/
theorem compiles : ∃ c, compileTypedEntryArtifact module entry = .ok c := by
  have h := facts_true
  unfold facts at h
  cases hc : compileTypedEntryArtifact module entry with
  | error e => simp [hc] at h
  | ok c => exact ⟨c, rfl⟩

/-- Source semantics discriminates: `2 * 3 = 6` holds. -/
theorem good_satisfies : TypedSourceSatisfies module entry good := by
  rw [← checkTypedSource_true_iff]; native_decide

/-- Source semantics discriminates: `2 * 4 = 6` fails. -/
theorem bad_unsatisfies : ¬ TypedSourceSatisfies module entry bad := by
  rw [← checkTypedSource_true_iff]; native_decide

variable {c : TypedEntryCompilationArtifact module entry}
  (hc : compileTypedEntryArtifact module entry = .ok c)
include hc

private theorem facts_of_compiled :
    c.artifact.CanonicalSource good ∧ c.artifact.CanonicalSource bad ∧
    (c.artifact.forward good).isOk = true ∧ (c.artifact.forward bad).isOk = true ∧
    c.artifact.paramOffset = 1 ∧ c.artifact.target.constraints.length ≥ 4 := by
  have h := facts_true
  unfold facts at h
  rw [hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7, h8⟩

/-- Preservation is informative: the satisfying observation is transported by the executable
`forward` to a witness that the compiled R1CS accepts and that reads back exactly. -/
theorem good_transported :
    ∃ t, c.artifact.forward good = .ok t ∧ R1CS.satisfies t c.artifact.target ∧
      c.artifact.readback t = good :=
  (typed_entry_correct module entry c).preservation good (facts_of_compiled hc).1
    good_satisfies

/-- Reflection is informative: no R1CS assignment at all, forwarded or adversarial, that reads
back to the unsatisfying observation satisfies the compiled target. -/
theorem bad_never_accepted :
    ¬ ∃ t, R1CS.satisfies t c.artifact.target ∧ c.artifact.readback t = bad :=
  fun h ↦ bad_unsatisfies
    ((typed_source_iff_exists_r1cs module entry c bad (facts_of_compiled hc).2.1).mpr h)

/-- The forwarded witness for the unsatisfying observation exists (equality failure is not a
transport failure) and is rejected by the target, as the pointwise iff demands. -/
theorem bad_forwarded_rejected :
    ∃ t, c.artifact.forward bad = .ok t ∧ ¬ R1CS.satisfies t c.artifact.target := by
  cases h : c.artifact.forward bad with
  | error e =>
    have hf := (facts_of_compiled hc).2.2.2.1
    rw [h] at hf
    exact absurd hf (by simp [Except.isOk, Except.toBool])
  | ok t =>
    refine ⟨t, rfl, fun hsat ↦ bad_unsatisfies ?_⟩
    exact (typed_source_r1cs_iff module entry c bad t h).mpr hsat

/-- The compiled target is a nontrivial constraint system (`a * b = 6` plus zero-prefix and
constant constraints). -/
theorem target_nonempty : c.artifact.target.constraints.length ≥ 4 :=
  (facts_of_compiled hc).2.2.2.2.2

end Dialect.StatementNonVacuity

#print axioms Dialect.StatementNonVacuity.good_transported
#print axioms Dialect.StatementNonVacuity.bad_never_accepted
#print axioms Dialect.StatementNonVacuity.bad_forwarded_rejected
