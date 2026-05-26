# StructIRToFlatIR Golfing Analysis

## Identified Repetitive Patterns

### Pattern 1: `materialize_step_feltXXX_satisfies` (Binary Ops)
**Lines**: ~60 lines × 5 ops (Add, Sub, Mul, Div) = ~240 lines

All follow identical structure:
```lean
theorem materialize_step_feltAdd_satisfies ... :=
  let stmt := .feltAdd dest src1 src2
  have hd : stmt.dest = some dest := by rfl
  let val := env (freshMap freshBase src1) + env (freshMap freshBase src2)
  have hDest := materializeConstrainBody_head_dest_after_write ... hd ...
  have hSrc1 := materializeConstrainBody_head_read_after_write ... (by simp [stmt, ConstrainStmt.reads]) ...
  have hSrc2 := materializeConstrainBody_head_read_after_write ... (by simp [stmt, ConstrainStmt.reads]) ...
  have hsrc1_ne := isSSA_read_ne_dest ... hd (by simp [stmt, ConstrainStmt.reads])
  have hsrc2_ne := isSSA_read_ne_dest ... hd (by simp [stmt, ConstrainStmt.reads])
  exact materialize_compile_feltAdd_satisfies ... ih hDest (by simpa [hsrc1_ne] using hSrc1) (by simpa [hsrc2_ne] using hSrc2)
```

**Tactic to create**:
```lean
syntax "materialize_binop" ident : tactic
```
Should generate all intermediate lemmas automatically.

### Pattern 2: `materializeConstrainBody_XXX_rename_eq` (5 statement types)
**Lines**: ~15 lines × 7 stmt types = ~105 lines

All follow:
```lean
theorem materializeConstrainBody_feltAdd_rename_eq ... :=
  materializeConstrainBody ... (renameBody freshMap (.feltAdd dest src1 src2 :: rest)) =
    let val := env (freshMap src1) + env (freshMap src2)
    let wt' := fun v => if v = freshMap dest then val else wt v
    materializeConstrainBody ... wt' (env.update (freshMap dest) val) ... rest
  := by simp [materializeConstrainBody, renameBody, renameStmt]
```

**Tactic to create**:
```lean
syntax "materialize_rename_simp" ident : tactic
```

### Pattern 3: SSA lemma applications
**Lines**: ~200 lines scattered

Repeated chains like:
```lean
have hSrc1 := materializeConstrainBody_head_read_after_write ... (by simp [stmt, ConstrainStmt.reads]) ...
have hSrc2 := materializeConstrainBody_head_read_after_write ... (by simp [stmt, ConstrainStmt.reads]) ...
have hsrc1_ne := isSSA_read_ne_dest ... (by simp [stmt, ConstrainStmt.reads])
have hsrc2_ne := isSSA_read_ne_dest ... (by simp [stmt, ConstrainStmt.reads])
```

**Tactic to create**:
```lean
syntax "ssa_lemmas_for" ident ident* : tactic
```
Should derive all SSA properties for listed variables.

### Pattern 4: Frame lemmas (witness update doesn't affect old slots)
**Lines**: ~150 lines

Repeated structure:
```lean
lemma witness_update_fresh_frame (wt : Witness F) (nextFresh dest v : Nat) (val : F) (hv : v < nextFresh) :
  (fun u => if u = freshMap nextFresh dest then val else wt u) v = wt v := by
  have hne := fresh_old_disjoint nextFresh v dest hv
  simp [hne]
```

**Tactic to create**:
```lean
syntax "frame_by_fresh" : tactic
```

### Pattern 5: `compileConstrainBody_XXX_eq` unfolding lemmas
**Lines**: ~10 lines × 8 cases = ~80 lines

All identical:
```lean
theorem compileConstrainBody_feltAdd_eq ... :=
  compileConstrainBody ... (.feltAdd dest src1 src2 :: rest) =
    let (tail, objEnv', nextFresh') := compileConstrainBody ... rest
    (Instr.assignAdd dest src1 src2 :: tail, objEnv', nextFresh')
  := by simp [compileConstrainBody]
```

**Should be eliminated**: These can be `@[simp]` lemmas or inlined at call sites.

## Compression Opportunities

### High-value targets (sorted by impact):

1. **Binary felt-op theorems** (~240 lines → ~40 lines)
   - Create single polymorphic tactic handling all binops
   - Saves: ~200 lines

2. **Rename equality theorems** (~105 lines → ~20 lines)
   - Single `materialize_rename_simp` tactic
   - Saves: ~85 lines

3. **Frame lemmas** (~150 lines → ~50 lines)
   - Unified `frame_by_fresh` tactic
   - Saves: ~100 lines

4. **SSA property derivations** (~200 lines → ~60 lines)
   - Smart `ssa_lemmas_for` tactic
   - Saves: ~140 lines

5. **Unfolding lemmas** (~80 lines → 0 lines)
   - Mark definitions as `@[simp]` or inline
   - Saves: ~80 lines

**Total estimated compression**: 6,901 lines → ~5,300 lines (23% reduction, ~1,600 lines saved)

## Implementation Priority

1. **Phase 1** (low-risk): Eliminate unfolding lemmas via `@[simp]` annotations
2. **Phase 2** (medium-risk): Build `materialize_binop` tactic for felt ops
3. **Phase 3** (low-risk): Build `materialize_rename_simp` tactic
4. **Phase 4** (medium-risk): Build `frame_by_fresh` and `ssa_lemmas_for` tactics

Each phase maintains proof robustness by preserving proof structure, just automating boilerplate.
