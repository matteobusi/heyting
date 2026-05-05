# Pipeline Composition Complete

**Date**: 2025-05-02

## Summary

The Heyting compiler pipeline now uses **generic composition of `PresReflPass` instances** to 
automatically prove end-to-end correctness. All pipeline preservation and reflection theorems
are derived mechanically from the individual pass proofs.

## Architecture

### Pass.lean: Generic Composition Operator

Added `PresReflPass.compose` to `Heyting/Core/Pass.lean`:

```lean
def PresReflPass.compose
  {S M T : Language} (pass1 : PresReflPass S M) (pass2 : PresReflPass M T) :
  PresReflPass S T where
  compile := pass2.compile ∘ pass1.compile
  witnessRel p ws wt := 
    ∃ wm, pass1.witnessRel p ws wm ∧ pass2.witnessRel (pass1.compile p) wm wt
  preservation := by
    intro ws p hs
    obtain ⟨wm, hwrel1, hsat1⟩ := pass1.preservation ws p hs
    obtain ⟨wt, hwrel2, hsat2⟩ := pass2.preservation wm (pass1.compile p) hsat1
    exact ⟨wt, ⟨wm, hwrel1, hwrel2⟩, hsat2⟩
  reflection := by
    intro wt p hs
    obtain ⟨wm, hwrel2, hsat2⟩ := pass2.reflection wt (pass1.compile p) hs
    obtain ⟨ws, hwrel1, hsat1⟩ := pass1.reflection wm p hsat2
    exact ⟨ws, ⟨wm, hwrel1, hwrel2⟩, hsat1⟩
```

**Key properties**:
- **Composed witness relation**: Chains through intermediate witness `wm`
- **Preservation proof**: Forward chain using individual pass preservation theorems
- **Reflection proof**: Backward chain using individual pass reflection theorems
- **Fully generic**: Works for any two `PresReflPass` instances

### Pipeline.lean: 4-Pass Composition

Reduced `Heyting/Passes/Pipeline.lean` from **268 lines with 4 sorries** to 
**90 lines with 0 theorem sorries**:

```lean
instance instPresReflPass : PresReflPass (StructIR.Language n F) (R1CS.Language F) :=
  let pass12 := PresReflPass.compose 
    (StructIRToStructInlineIR.CorrectPass n F)
    (StructInlineIRToMemberlessIR.PresReflPass n F)
  let pass34 := PresReflPass.compose
    (MemberlessIRToFlatIR.PresReflPass n F)
    (FlatIRToR1CS.CorrectPass F)
  PresReflPass.compose pass12 pass34
```

**What this gives us**:
- **Automatic preservation**: `(StructIR.satisfies ws m) → (R1CS.satisfies wr (compile m))`
- **Automatic reflection**: `(R1CS.satisfies wr (compile m)) → (StructIR.satisfies ws m)`
- **Explicit witness relation**: 
  ```lean
  witnessRel m ws wr := 
    ∃ (wi : StructInlineIR.Witness) (wm : MemberlessIR.Witness) (wf : FlatIR.Witness),
      witnessRel₁ m ws wi ∧ 
      witnessRel₂ (compile₁ m) wi wm ∧
      witnessRel₃ (compile₂ m) wm wf ∧
      witnessRel₄ (compile₃ m) wf wr
  ```

## Sorry Count Impact

| File | Before | After | Change |
|------|--------|-------|--------|
| `Pipeline.lean` (theorems) | 4 | **0** | **-4** |
| `Pipeline.lean` (utility) | 0 | **0** | **0** |
| **Total project** | **13** | **9** | **-4** |

**Notes**:
- The 4 theorem sorries in Pipeline are **eliminated** by using composition
- The utility function `pipelineWitness` is now **fully implemented** by chaining the individual 
  pass `compileWitness` functions
- Pipeline now has **0 sorries** — all code is either proven or constructively defined
- The remaining 9 sorries are in individual passes (Pass 1: 2, Pass 2: 4, Pass 3: 3)

## Benefits

### 1. **Proof Automation**
The composition operator automatically chains preservation and reflection proofs. When an 
individual pass is proven, the pipeline correctness follows immediately.

### 2. **Modularity**
Each pass can be developed independently. As long as it provides a `PresReflPass` instance,
it composes automatically.

### 3. **Extensibility**
Adding a 5th pass is trivial:
```lean
let pass1234 := compose (compose pass12 pass34)
let pass5 := MyNewPass.PresReflPass
compose pass1234 pass5
```

### 4. **Maintainability**
Pipeline.lean reduced from 268 lines to 90 lines (66% reduction). No manual witness chaining,
no manual proof composition.

### 5. **Type Safety**
The compiler verifies that passes compose correctly at the type level. Mismatched intermediate
languages cause type errors.

## Remaining Work

### Individual Pass Proofs
To make the pipeline fully proven, we need to complete:

1. **Pass 1 (StructIR → StructInlineIR)**: 2 sorries
   - Module well-formedness conditions
   
2. **Pass 2 (StructInlineIR → MemberlessIR)**: 4 sorries  
   - Module well-formedness (1 sorry)
   - Reflection theorems (3 sorries) - open semantic question

3. **Pass 3 (MemberlessIR → FlatIR)**: 3 sorries
   - `preservation`, `reflection`, `witnessRel_compileModuleWitness`

4. **Pass 4 (FlatIR → R1CS)**: ✅ **COMPLETE** (0 sorries)

### Utility Function
The `pipelineWitness` function is **fully implemented** by chaining the individual pass witness 
compilation functions:
```lean
def pipelineWitness (m : StructIR.Module (n + 1) F) (inputs : List F) :
    Option (R1CS.Witness F) :=
  StructIR.computeWitness m inputs |>.map fun ws =>
    let wi := ws  -- Pass 1: identity
    let wm := StructInlineIRToMemberlessIR.compileWitness (compileInline m) wi
    let wf := MemberlessIRToFlatIR.compileModuleWitness (compileMemberless m) wm
    FlatIRToR1CS.compileWitness wf
```
This provides end-to-end witness generation from inputs to R1CS witness in a single call.

## Conclusion

The pipeline now demonstrates **proof by composition**: we build complex correctness guarantees
from simple building blocks. The `PresReflPass.compose` operator is a reusable proof combinator
that will work for any future compiler extensions.

**Key achievement**: Pipeline preservation and reflection are no longer "to be proved" — they
are **proven automatically** from the individual pass instances. The remaining work is entirely
in the individual passes, which are smaller and more manageable proof obligations.

## Files Modified

- `Heyting/Core/Pass.lean`: Added `PresReflPass.compose` (33 lines)
- `Heyting/Passes/Pipeline.lean`: Complete rewrite using composition (90 lines, down from 268)

## Verification

```bash
$ lake build Heyting.Passes.Pipeline
Build completed successfully (779 jobs).
```

All builds pass. The pipeline now has a clean, compositional structure.
