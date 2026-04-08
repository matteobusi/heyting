import Mathlib.Data.Set.Basic

import Heyting.Core.Language
import Heyting.Core.Pass

/-
  This is a re-adapted version of the ESORICS 2020 paper
    "Trace-Relating Compiler Correctness and Secure Compilation" by Abate et al.
  We'll refer to it as TRCCCS from now onwards.

  We limit ourselves to re-stating and proving their results in the ZKP setting
  and within our framework.

  In the ZKP setting:
    - "traces" correspond to witnesses, thus
    - the "behavior" of a program p is its satisfaction set { w | satisfies w p }.
-/

/-
  τ is the existential image of the witness relation on properties.
  Given a source property πS, τ(πS) collects all target witnesses related to
  some source witness in πS.
  (Definition 2.5 of TRCCCS)
-/
def τ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} [P : Pass S T]
  (p : S.Program) (πS : Set (Witness Vs Fs)) : Set (Witness Vt Ft) :=
  { wt | ∃ ws ∈ πS, P.witnessRel p ws wt }

/-
  σ is the universal image of the witness relation on properties.
  Given a target property πT, σ(πT) collects all source witnesses whose
  related target witnesses all fall within πT.
  (Definition 2.5 of TRCCCS)
-/
def σ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} [P : Pass S T]
  (p : S.Program) (πT : Set (Witness Vt Ft)) : Set (Witness Vs Fs) :=
  { ws | ∀ wt, P.witnessRel p ws wt → wt ∈ πT }

/-
  WPσ is witness-property preservation through σ.
  For all target properties πT: if the source program's satisfaction set is
  contained in σ(πT), then the target program's satisfaction set is contained
  in πT.
-/
def WPσ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) [P : Pass S T] : Prop :=
  ∀ (p : S.Program) (πT : Set (Witness Vt Ft)),
    (∀ ws, S.satisfies ws p → ws ∈ σ (S := S) (T := T) p πT) →
    (∀ wt, T.satisfies wt (P.compile p) → wt ∈ πT)

/-
  WPτ is witness-property preservation through τ.
  For all source properties πS: if the source program's satisfaction set is
  contained in πS, then the target program's satisfaction set is contained
  in τ̃(πS).
-/
def WPτ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) [P : Pass S T] : Prop :=
  ∀ (p : S.Program) (πS : Set (Witness Vs Fs)),
    (∀ ws, S.satisfies ws p → ws ∈ πS) →
    (∀ wt, T.satisfies wt (P.compile p) →
      wt ∈ τ (S := S) (T := T) p πS)

/-
  cc is trace-relating compiler correctness (CC~ from Def. 1.2 of TRCCCS).
  For every target witness satisfying the compiled program, there exists a
  related source witness satisfying the source program.
-/
def cc
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft) [P : Pass S T] : Prop :=
    ∀ (p : S.Program) (wt : Witness Vt Ft),
      T.satisfies wt (P.compile p) →
        ∃ ws, P.witnessRel p ws wt ∧ S.satisfies ws p

/-
  This class specifies when a pass is trace property preserving via σ
-/
class TPσPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  witness_preservation : WPσ S T

/-
  This class specifies when a pass is trace property preserving via τ̃
-/
class TPτPass
  {Vs Vt : Type} {Fs Ft : Type}
  [Field Fs] [Field Ft]
  (S : Language Vs Fs) (T : Language Vt Ft)
extends Pass S T where
  witness_preservation : WPτ S T

/-
  TPσ ↔ CC~ (part of the trinitarian view, Theorem 2.6 of TRCCCS)
-/
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

/-
  TPτ ↔ CC~ (part of the trinitarian view, Theorem 2.6 of TRCCCS)
-/
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

/-
  TPσ ↔ TPτ (corollary of the trinitarian view, Theorem 2.6 of TRCCCS)
-/
lemma TPσ_iff_TPτ
  {Vs Vt : Type} {Fs Ft : Type} [Field Fs] [Field Ft]
  {S : Language Vs Fs} {T : Language Vt Ft} :
    ∀ (P : Pass S T), WPσ S T (P:=P) ↔ WPτ S T (P:=P) := by
  intro P
  exact (TPσ_iff_CC P).trans (TPτ_iff_CC P).symm
