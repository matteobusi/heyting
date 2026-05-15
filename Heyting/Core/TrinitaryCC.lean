import Mathlib.Data.Set.Basic

import Heyting.Core.Language
import Heyting.Core.Pass

/-!
# Trinitarian Compiler Correctness for Witness Semantics

This file adapts results from Abate et al., "Trace-Relating Compiler
Correctness and Secure Compilation" (ESORICS 2020), to Heyting's ZKP setting.

Here, traces are replaced by witnesses, so a program's behavior is its
satisfaction set `{ w | satisfies w p }`. The file restates the `τ`, `σ`,
`TPσ`, `TPτ`, and `CC~` viewpoint in terms of witness relations.
-/

/-
  τ is the existential image of the witness relation on properties.
  Given a source property πS, τ(πS) collects all target witnesses related to
  some source witness in πS.
  (Definition 2.5 of TRCCCS)
-/
/-! ## Property transformers and correctness notions -/

/-
  τ is the existential image of the witness relation on properties.
  Given a source property πS, τ(πS) collects all target witnesses related to
  some source witness in πS.
  (Definition 2.5 of TRCCCS)
-/
/-- Existential image of a source witness property along the pass witness relation. -/
def τ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} [P : Pass S T]
  (p : S.Program) (πS : Set (Witness Vs Fs)) : Set (Witness Vt Ft) :=
  { wt | ∃ ws ∈ πS, P.witnessRel p ws wt }

/-- Universal preimage of a target witness property along the pass witness relation. -/
def σ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} [P : Pass S T]
  (p : S.Program) (πT : Set (Witness Vt Ft)) : Set (Witness Vs Fs) :=
  { ws | ∀ wt, P.witnessRel p ws wt → wt ∈ πT }

/-- Witness-property preservation stated through `σ`. -/
def WPσ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) [P : Pass S T] : Prop :=
  ∀ (p : S.Program) (πT : Set (Witness Vt Ft)),
    (∀ ws, S.satisfies ws p → ws ∈ σ (S := S) (T := T) p πT) →
    (∀ wt, T.satisfies wt (P.compile p) → wt ∈ πT)

/-- Witness-property preservation stated through `τ`. -/
def WPτ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) [P : Pass S T] : Prop :=
  ∀ (p : S.Program) (πS : Set (Witness Vs Fs)),
    (∀ ws, S.satisfies ws p → ws ∈ πS) →
    (∀ wt, T.satisfies wt (P.compile p) →
      wt ∈ τ (S := S) (T := T) p πS)

/-- Trace-relating compiler correctness specialized to witness semantics. -/
def cc
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) [P : Pass S T] : Prop :=
    ∀ (p : S.Program) (wt : Witness Vt Ft),
      T.satisfies wt (P.compile p) →
        ∃ ws, P.witnessRel p ws wt ∧ S.satisfies ws p

/-- Passes satisfying witness-property preservation through `σ`. -/
class TPσPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  witness_preservation : WPσ S T

/-- Passes satisfying witness-property preservation through `τ`. -/
class TPτPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  witness_preservation : WPτ S T

/-- `TPσ` coincides with `CC~` in witness semantics. -/
lemma TPσ_iff_CC
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} :
    ∀ (P : Pass S T), WPσ S T ↔ cc (P := P) S T := by
  intro P
  constructor
  · -- WPσ → CC~: instantiate πT with the "reachable" target property
    intro h p wt h_sat
    have := h p { wt | ∃ ws, P.witnessRel p ws wt ∧ S.satisfies ws p }
              (fun ws h_s _t h_rel => ⟨ws, h_rel, h_s⟩) wt h_sat
    simp only [Set.mem_setOf_eq] at this
    exact this
  · -- CC~ → WPσ: use CC~ to get related source witness, then apply hypothesis
    intro h p πT h_sub wt h_sat
    obtain ⟨ws, h_rel, h_sat_s⟩ := h p wt h_sat
    exact h_sub ws h_sat_s wt h_rel

/-- `TPτ` coincides with `CC~` in witness semantics. -/
lemma TPτ_iff_CC
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} :
    ∀ (P : Pass S T), WPτ S T ↔ cc (P := P) S T := by
  intro P
  constructor
  · -- WPτ → CC~: instantiate πS with the source satisfaction set
    intro h p wt h_sat
    have := h p { ws | S.satisfies ws p } (fun _ws h => h) wt h_sat
    simp only [τ, Set.mem_setOf_eq] at this
    obtain ⟨ws, h_sat_s, h_rel⟩ := this
    exact ⟨ws, h_rel, h_sat_s⟩
  · -- CC~ → WPτ: use CC~ to get related source witness, lift to πS
    intro h p πS h_sub wt h_sat
    simp only [τ, Set.mem_setOf_eq]
    obtain ⟨ws, h_rel, h_sat_s⟩ := h p wt h_sat
    exact ⟨ws, h_sub ws h_sat_s, h_rel⟩

/-- `TPσ` and `TPτ` are equivalent formulations of witness-property preservation. -/
lemma TPσ_iff_TPτ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} :
    ∀ (P : Pass S T), WPσ S T (P:=P) ↔ WPτ S T (P:=P) := by
  intro P
  exact (TPσ_iff_CC P).trans (TPτ_iff_CC P).symm
