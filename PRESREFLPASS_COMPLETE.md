# PresReflPass Requirement Complete ✅

**Date:** 2026-05-01

## Achievement

All passes and the end-to-end pipeline now have `PresReflPass` instances, 
fulfilling the fundamental design requirement that every compilation stage 
must be equipped with preservation and reflection proofs (even if sorried).

## What Changed

### 1. Pass 2: StructInlineIR → MemberlessIR
- **Before:** `Pass` instance only
- **After:** Full `PresReflPass` instance
- Added preservation (wraps proven theorem with WellFormedForCompile assumption)
- Added reflection (sorried - documented open question)
- Added witness relation helpers in typeclass instance

### 2. Pass 3: MemberlessIR → FlatIR
- **Before:** No typeclass instance at all
- **After:** Full `PresReflPass` instance
- Added `preservation` theorem (sorried)
- Added `reflection` theorem (sorried)
- Added witness relation helper
- Added typeclass instance with all infrastructure

### 3. Pipeline: StructIR → R1CS (End-to-End)
- **Before:** `Pass` instance only
- **After:** Full `PresReflPass` instance
- Added `preservation` theorem (sorried - will compose 4 sub-pass proofs)
- Added `reflection` theorem (sorried - will compose 4 sub-pass proofs)
- Witness relation chains through all intermediate languages
- Typeclass instance with existential witness quantification

## Design Decision Updated

Added to `AGENTS.md` Key Invariants #1:

> **All passes must implement `PresReflPass`.** Every pass must have a 
> `PresReflPass` instance with `compile`, `witnessRel`, `preservation`, 
> and `reflection`. If proofs are not complete, use `sorry` — but the 
> typeclass instance must exist. This is fundamental to the compiler's 
> correctness framework.

## Current State

| Component | PresReflPass | Sorries | Notes |
|-----------|:------------:|:-------:|-------|
| Pass 1: StructIR → StructInlineIR | ✅ | 2 | Module well-formedness only |
| Pass 2: StructInlineIR → MemberlessIR | ✅ | 4 | Preservation ✅ proven |
| Pass 3: MemberlessIR → FlatIR | ✅ | 3 | All theorems need proofs |
| Pass 4: FlatIR → R1CS | ✅ | 0 | ✅ Fully proven |
| Pipeline: StructIR → R1CS | ✅ | 4 | Composition theorems |

**Total: 13 sorries** (up from 9 before Pipeline was added)

## Why This Matters

### Architectural Consistency
Every compilation stage now follows the same correctness pattern:
- Witness relation defines semantic correspondence
- Preservation proves forward correctness (completeness)
- Reflection proves backward correctness (soundness)
- Together: equisatisfiability guarantees

### Compositional Reasoning
The Pipeline `PresReflPass` instance demonstrates how correctness composes:
```lean
witnessRel m ws wr := ∃ wi mw wf,
  Pass1.witnessRel m ws wi ∧
  Pass2.witnessRel (compile1 m) wi mw ∧
  Pass3.witnessRel (compile12 m) mw wf ∧
  Pass4.witnessRel (compile123 m) wf wr
```

Once individual passes are proven, pipeline correctness follows by chaining.

### Clear Proof Obligations
Every `sorry` is now explicitly typed and documented:
- 2 module well-formedness proofs (Pass 1)
- 4 reflection + WF proofs (Pass 2) — 1 open research question
- 3 correctness proofs (Pass 3) — should follow StructIRToFlatIR pattern
- 4 composition proofs (Pipeline) — mechanical once passes are done

### Documentation Complete
- `AGENTS.md`: Design decision + proof status table
- `docs/GUARANTEES.md`: Full guarantee statements per pass + pipeline
- `docs/SORRY_STATUS.md`: Complete breakdown with priorities
- `README.md`: User-facing pass table

## Next Steps

See `docs/SORRY_STATUS.md` for priorities. Key targets:

1. **Pass 3 preservation/reflection**: Should follow old StructIRToFlatIR proof structure
2. **Pass 2 well-formedness**: Prove StructInlineIR modules satisfy WellFormedForCompile
3. **Pipeline composition**: Mechanical chaining once passes 1-4 are complete
4. **Pass 1 module WF**: Structural induction on expandBody/inlineBody

## Build Status

✅ `lake build` — 0 errors, warnings only for sorries and linter
✅ All typeclass instances resolve correctly
✅ 13 documented sorries with clear proof obligations
