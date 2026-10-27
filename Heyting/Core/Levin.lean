/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Levin reductions

A Levin reduction from an NP relation `RS` to an NP relation `RT` consists of a statement
map, a forward witness map, and a backward witness map (the extractor), such that

* completeness: `RS x w → RT (stmt x) (fwd x w)`;
* extraction: `RT (stmt x) w' → RS x (ext x w')`.

Unlike `PresReflPass`, the relations are indexed by a public statement and both witness maps
are functions, not existential witnesses. A proof system that is complete, knowledge-sound,
and zero-knowledge for `RT` therefore gives one for `RS`: the prover runs `fwd`, the
knowledge extractor is `ext x ∘ E_T`, and the simulator is `S_T ∘ stmt`. That transfer
theorem needs a model of adversaries and probability and is not formalized here; this file
provides the relation-level object it consumes.

Lean functions are computable but carry no cost bound. Instances in this project state
separately that their extractor is a reindexing of target wires.
-/

/-- A Levin reduction from `RS` to `RT`. -/
structure LevinReduction {Xs Ws Xt Wt : Type} (RS : Xs → Ws → Prop)
    (RT : Xt → Wt → Prop) where
  /-- Statement map. -/
  stmt : Xs → Xt
  /-- Forward witness map, run by the prover. -/
  fwd : Xs → Ws → Wt
  /-- Backward witness map, the extractor. -/
  ext : Xs → Wt → Ws
  /-- Every source instance maps to a target instance. -/
  completeness : ∀ x w, RS x w → RT (stmt x) (fwd x w)
  /-- Every target witness for a mapped statement extracts to a source witness. -/
  extraction : ∀ x w', RT (stmt x) w' → RS x (ext x w')

namespace LevinReduction

variable {Xs Ws Xm Wm Xt Wt : Type}
  {RS : Xs → Ws → Prop} {RM : Xm → Wm → Prop} {RT : Xt → Wt → Prop}

/-- Identity reduction. -/
def id (R : Xs → Ws → Prop) : LevinReduction R R where
  stmt x := x
  fwd _ w := w
  ext _ w := w
  completeness _ _ h := h
  extraction _ _ h := h

/-- Sequential composition. The statement and forward maps compose in order; the extractor
composes in reverse order, each stage extracting at its own statement.

Proof sketch: completeness applies the two completeness laws in order; extraction applies
the second extraction law at `r.stmt x`, then the first. -/
def comp (r : LevinReduction RS RM) (s : LevinReduction RM RT) : LevinReduction RS RT where
  stmt x := s.stmt (r.stmt x)
  fwd x w := s.fwd (r.stmt x) (r.fwd x w)
  ext x w := r.ext x (s.ext (r.stmt x) w)
  completeness x w h := s.completeness _ _ (r.completeness x w h)
  extraction x _ h := r.extraction x _ (s.extraction _ _ h)

/-- Witness-free consequence: a statement is in the language of `RS` iff its image is in the
language of `RT`. -/
theorem language_iff (r : LevinReduction RS RT) (x : Xs) :
    (∃ w, RS x w) ↔ ∃ w', RT (r.stmt x) w' :=
  ⟨fun ⟨w, h⟩ => ⟨r.fwd x w, r.completeness x w h⟩,
    fun ⟨w', h⟩ => ⟨r.ext x w', r.extraction x w' h⟩⟩

end LevinReduction
