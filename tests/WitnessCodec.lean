import Heyting.Core.WitnessCodec
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace WitnessCodec.Tests

open WitnessCodec

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

def natLanguage : Language Nat (ZMod 17) where
  Program := Nat
  satisfies w p := w 0 = p

def plusOne (p : Nat) : CompilationArtifact natLanguage natLanguage p where
  target := p
  forward ws := .ok ws
  readback := id
  witnessRel ws wt := ws = wt
  forward_rel := by intro ws wt h; exact Except.ok.inj h
  satisfies_iff := by
    intro ws wt h
    have hwt : ws = wt := Except.ok.inj h
    subst wt
    rfl
  readback_forward := by
    intro ws wt h
    have hwt : ws = wt := Except.ok.inj h
    subst wt
    rfl

def twice (p : Nat) := (plusOne p).compose (plusOne p)

example : (twice (3 : Nat)).target = (3 : Nat) := rfl

example (ws : Witness Nat (ZMod 17)) : (twice 3).forward ws = .ok ws := rfl
example (ws : Witness Nat (ZMod 17)) : (twice 3).readback ws = ws := rfl

end WitnessCodec.Tests
