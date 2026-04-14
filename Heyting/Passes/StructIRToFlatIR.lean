import Heyting.Core.Pass
import Heyting.Languages.StructIR
import Heyting.Languages.FlatIR

/-!
# StructIR → FlatIR Pass

Flattens a hierarchical StructIR module into a flat list of FlatIR instructions.
Proved correct as a `PresReflPass`: reflection gives CC~ (trace-relating
compiler correctness, Abate et al. ESOP 2020), and preservation additionally
guarantees completeness (no spurious constraints added).

## Compilation strategy

The pass walks the main struct's `@constrain` body, recursively inlining
cross-struct calls, and emits FlatIR instructions for felt ops and constraints.

### Variable mapping

We use a **counter-based allocation**: each assignment gets a fresh FlatIR
variable ID from a monotonically increasing counter. This ensures correctness
even when StructIR locals are reassigned (non-SSA programs).

The `compileWitness` function mirrors this allocation and maps each FlatIR
variable to the value computed by the corresponding StructIR operation.

### What gets compiled

- **Felt ops** → FlatIR `assign*` instructions (fresh dest variable)
- **`constrainEq`** → FlatIR `assertEq`
- **`readMember`** → no instruction (witness handles value injection)
- **`call`** → recursively inline callee body (params via witness)
- **Zero-init prefix** → `assignConst v 0` for `v ∈ 0..initNext-1`,
  constraining param positions to 0 (needed for reflection, see below)

## Correctness proof architecture

**Preservation** (`preservation_body`): Given a StructIR witness `ws` satisfying
the source, construct a FlatIR witness `wt = compileWitness(ws)` satisfying the
compiled program. Uses `WitnessCoherent wt varMap env` as the main invariant.

**Reflection** (`reflection_direct`): Given a FlatIR witness `wt` satisfying
the compiled program, show that the source `evalConstrainBody` holds when
instantiated with `w = extractWitness(wt)`. Uses `wt` directly (not through
`compileWitness`) and maintains `WitnessCoherent wt varMap env` inductively.
The zero-initialization prefix forces `wt v = 0` for param positions, which
is needed to establish initial coherence for reflection.
-/

namespace StructIRToFlatIR

open StructIR FlatIR

variable {F : Type} [Field F] {n : Nat}

/-! ## Compilation state

Both `compileConstrainBody` and `compileWitness` thread a counter (`next`)
for allocating fresh FlatIR variable IDs. To keep them in sync, both
use the same allocation logic.

For each felt op with destination `dest`:
- A fresh FlatIR variable `next` is allocated for the result
- Source operands are looked up via a mapping `varMap : LocalVar → FlatIR.VarId`
- `varMap` is updated: `varMap[dest] := next`
- Counter advances: `next' := next + 1`

For `readMember dest self member`:
- A fresh FlatIR variable `next` is allocated
- The FlatIR witness maps `next` to `w(objEnv self, member.val)`
- `varMap[dest] := next`, `next' := next + 1`

For `constrainEq src1 src2`:
- Emits `assertEq (varMap src1) (varMap src2)`
- No allocation

For `call target args`:
- Initialize callee's varMap from args: `calleeVarMap[k] := varMap[args[k]]`
- Recursively compile callee body
- No allocation in this frame (callee uses its own)
-/

-- Mapping from StructIR local variables to FlatIR variable IDs
abbrev VarMap := LocalVar → FlatIR.VarId

def VarMap.update (vm : VarMap) (local_ : LocalVar) (flat : FlatIR.VarId) :
    VarMap :=
  fun v => if v == local_ then flat else vm v

/-! ## Program compilation -/

-- Compile a constrain body to FlatIR instructions.
-- `varMap`: maps current StructIR locals to FlatIR variable IDs
-- `next`: next fresh FlatIR variable ID
-- Returns (instructions, updated next)
def compileConstrainBody (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    List (FlatIR.Instr F) × Nat :=
  match stmts with
  | [] => ([], next)
  | stmt :: rest =>
    let (instrs, varMap', next') := match stmt with
      | .feltAdd dest src1 src2 =>
        ([Instr.assignAdd next (varMap src1) (varMap src2)],
         varMap.update dest next, next + 1)
      | .feltSub dest src1 src2 =>
        ([Instr.assignSub next (varMap src1) (varMap src2)],
         varMap.update dest next, next + 1)
      | .feltMul dest src1 src2 =>
        ([Instr.assignMul next (varMap src1) (varMap src2)],
         varMap.update dest next, next + 1)
      | .feltDiv dest src1 src2 =>
        ([Instr.assignDiv next (varMap src1) (varMap src2)],
         varMap.update dest next, next + 1)
      | .feltNeg dest src =>
        ([Instr.assignNeg next (varMap src)],
         varMap.update dest next, next + 1)
      | .feltConst dest c =>
        ([Instr.assignConst next c],
         varMap.update dest next, next + 1)
      | .readMember dest _self _member =>
        -- No instruction; witness injects the value at `next`
        ([], varMap.update dest next, next + 1)
      | .constrainEq src1 src2 =>
        ([Instr.assertEq (varMap src1) (varMap src2)], varMap, next)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let sd := m.structs j
        -- Build callee varMap: param k maps to varMap(args[k])
        let calleeVarMap : VarMap := fun param =>
          match args[param]? with
          | some arg => varMap arg
          | none => 0  -- unused params default to var 0
        let (callInstrs, next'') :=
          compileConstrainBody m j calleeVarMap next sd.constrain.body
        (callInstrs, varMap, next'')
    let (restInstrs, finalNext) :=
      compileConstrainBody m i varMap' next' rest
    (instrs ++ restInstrs, finalNext)
termination_by (i, stmts.length)

def compileProgram (m : StructIR.Module (n + 1) F) : FlatIR.Program F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef := m.structs mainIdx
  -- Initial varMap: params map to themselves; other locals map to 0
  -- This ensures VarMapBound holds when numParams > 0
  let initVarMap : VarMap := fun v =>
    if v < mainDef.constrain.numParams then v else 0
  let initNext := max mainDef.constrain.numParams 1
  -- Emit zero-initialization constraints for variables 0..initNext-1.
  -- The StructIR semantics initializes all local variables to 0, but without
  -- these constraints the FlatIR program would accept witnesses with non-zero
  -- values at param positions, breaking reflection.
  let zeroConstrs : FlatIR.Program F :=
    (List.range initNext).map (fun v => Instr.assignConst v 0)
  zeroConstrs ++ (compileConstrainBody m mainIdx initVarMap initNext mainDef.constrain.body).1

/-! ## Witness construction

`compileWitness` mirrors `compileConstrainBody` exactly in allocation, but
records the computed values at each fresh variable. Used in the correctness
proofs to construct the FlatIR witness from a StructIR witness.
-/

def compileWitness (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F) : (FlatIR.VarId → F) × Nat :=
  match stmts with
  | [] => (acc, next)
  | stmt :: rest =>
    let (env', objEnv', varMap', next', acc') := match stmt with
      | .feltAdd dest src1 src2 =>
        let val := env src1 + env src2
        (env.update dest val, objEnv, varMap.update dest next, next + 1,
         fun v => if v == next then val else acc v)
      | .feltSub dest src1 src2 =>
        let val := env src1 - env src2
        (env.update dest val, objEnv, varMap.update dest next, next + 1,
         fun v => if v == next then val else acc v)
      | .feltMul dest src1 src2 =>
        let val := env src1 * env src2
        (env.update dest val, objEnv, varMap.update dest next, next + 1,
         fun v => if v == next then val else acc v)
      | .feltDiv dest src1 src2 =>
        let val := env src1 * (env src2)⁻¹
        (env.update dest val, objEnv, varMap.update dest next, next + 1,
         fun v => if v == next then val else acc v)
      | .feltNeg dest src =>
        let val := -(env src)
        (env.update dest val, objEnv, varMap.update dest next, next + 1,
         fun v => if v == next then val else acc v)
      | .feltConst dest c =>
        (env.update dest c, objEnv, varMap.update dest next, next + 1,
         fun v => if v == next then c else acc v)
      | .readMember dest self member =>
        let path := objEnv self
        let val := w (path, member.val)
        (env.update dest val, objEnv.update dest (path ++ [member.val]),
         varMap.update dest next, next + 1,
         fun v => if v == next then val else acc v)
      | .constrainEq _src1 _src2 =>
        (env, objEnv, varMap, next, acc)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let sd := m.structs j
        let calleeEnv : LocalEnv F := fun param =>
          match args[param]? with
          | some arg => env arg
          | none => 0
        let calleeObjEnv : ObjEnv := fun param =>
          match args[param]? with
          | some arg => objEnv arg
          | none => []
        let calleeVarMap : VarMap := fun param =>
          match args[param]? with
          | some arg => varMap arg
          | none => 0
        let (acc', next') := compileWitness m w j calleeVarMap next
          calleeEnv calleeObjEnv sd.constrain.body acc
        (env, objEnv, varMap, next', acc')
    compileWitness m w i varMap' next' env' objEnv' rest acc'
termination_by (i, stmts.length)

/-! ## Backward witness extraction

`extractWitness` reconstructs a StructIR witness from a FlatIR witness by
tracing through the compilation to find which FlatIR variable corresponds
to each (path, member) pair, then reading the FlatIR witness at that position.
-/

-- Track which FlatIR variable holds each (path, member) value.
-- Mirrors `compileConstrainBody` / `compileWitness` allocation, but records
-- the mapping from (path, memberIdx) → FlatIR.VarId.
def buildVarAlloc (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : StructIR.VarId → FlatIR.VarId) :
    (StructIR.VarId → FlatIR.VarId) × Nat :=
  match stmts with
  | [] => (acc, next)
  | stmt :: rest =>
    let (objEnv', varMap', next', acc') := match stmt with
      | .feltAdd dest _src1 _src2 =>
        (objEnv, varMap.update dest next, next + 1, acc)
      | .feltSub dest _src1 _src2 =>
        (objEnv, varMap.update dest next, next + 1, acc)
      | .feltMul dest _src1 _src2 =>
        (objEnv, varMap.update dest next, next + 1, acc)
      | .feltDiv dest _src1 _src2 =>
        (objEnv, varMap.update dest next, next + 1, acc)
      | .feltNeg dest _src =>
        (objEnv, varMap.update dest next, next + 1, acc)
      | .feltConst dest _c =>
        (objEnv, varMap.update dest next, next + 1, acc)
      | .readMember dest self member =>
        let path := objEnv self
        (objEnv.update dest (path ++ [member.val]),
         varMap.update dest next, next + 1,
         fun vid => if vid == (path, member.val) then next else acc vid)
      | .constrainEq _src1 _src2 =>
        (objEnv, varMap, next, acc)
      | .call target args =>
        let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
        let sd := m.structs j
        let calleeObjEnv : ObjEnv := fun param =>
          match args[param]? with
          | some arg => objEnv arg
          | none => []
        let calleeVarMap : VarMap := fun param =>
          match args[param]? with
          | some arg => varMap arg
          | none => 0
        let (acc', next') := buildVarAlloc m j calleeVarMap next
          calleeObjEnv sd.constrain.body acc
        (objEnv, varMap, next', acc')
    buildVarAlloc m i varMap' next' objEnv' rest acc'
termination_by (i, stmts.length)

-- Extract a StructIR witness from a FlatIR witness by using the variable
-- allocation map to find which FlatIR variable holds each member value.
def extractWitness (m : StructIR.Module (n + 1) F)
    (wt : FlatIR.Witness F) : StructIR.Witness F :=
  let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
  let mainDef := m.structs mainIdx
  let initVarMap : VarMap := fun v =>
    if v < mainDef.constrain.numParams then v else 0
  let initNext := max mainDef.constrain.numParams 1
  let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
  let varAlloc := (buildVarAlloc m mainIdx initVarMap initNext
    initObjEnv mainDef.constrain.body (fun _ => 0)).1
  fun vid => wt (varAlloc vid)

/-! ## Witness relation

The witness relation ties source and target witnesses through the variable
allocation map (`buildVarAlloc`). At each `readMember` during compilation,
`buildVarAlloc` records which FlatIR variable holds the value of each
`(path, member)` pair. The relation requires that the source and target
witnesses agree at these positions:

  `witnessRel p ws wt := ∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)`

The condition `varAlloc vid ≠ 0` restricts agreement to positions actually
read by the program (unread positions default to 0 in the allocation map,
and `initNext ≥ 1` ensures all real allocations are ≥ 1).

**WARNING**: Reflection requires the `NoDuplicateReads` condition on the
source module (carried as `Module.noDupReads`). This ensures each
`(path, member)` is read at most once, so `buildVarAlloc` assigns a unique
FlatIR variable to each read position. Without this, `extractWitness` could
assign inconsistent values. This condition holds for SSA-form programs.
-/

/-! ## Correctness -/

-- Witness coherence: acc maps varMap(v) to env(v) for all locals v
def WitnessCoherent (acc : FlatIR.VarId → F) (varMap : VarMap)
    (env : LocalEnv F) : Prop :=
  ∀ v : LocalVar, acc (varMap v) = env v

-- VarMap range bounded by next (all mapped values are fresh variable IDs < next)
def VarMapBound (varMap : VarMap) (next : Nat) : Prop :=
  ∀ v : LocalVar, varMap v < next

/-! ### Auxiliary lemmas for compileWitness -/

-- The variable counter only increases through compileWitness
theorem compileWitness_next_le (m : StructIR.Module n F)
    (w : StructIR.Witness F) (i : Fin n) (varMap : VarMap)
    (next : Nat) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F) :
    next ≤ (compileWitness m w i varMap next env objEnv stmts acc).2 := by
  match stmts with
  | [] => simp [compileWitness]
  | stmt :: rest =>
    unfold compileWitness
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. | .readMember .. =>
      simp only
      exact Nat.le_trans (Nat.le_succ _)
        (compileWitness_next_le m w i _ _ _ _ rest _)
    | .constrainEq .. =>
      simp only; exact compileWitness_next_le m w i _ _ _ _ rest _
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      exact Nat.le_trans
        (compileWitness_next_le m w j _ _ _ _ _ _)
        (compileWitness_next_le m w i _ _ _ _ rest _)
termination_by (i, stmts.length)

-- compileWitness only writes to variables >= next; values below are preserved
theorem compileWitness_preserves_below (m : StructIR.Module n F)
    (w : StructIR.Witness F) (i : Fin n) (varMap : VarMap)
    (next : Nat) (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F) (v : FlatIR.VarId) (hv : v < next) :
    (compileWitness m w i varMap next env objEnv stmts acc).1 v =
      acc v := by
  match stmts with
  | [] => unfold compileWitness; rfl
  | stmt :: rest =>
    unfold compileWitness
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. | .readMember .. =>
      simp only
      have hv' : v < next + 1 := Nat.lt_of_lt_of_le hv (Nat.le_succ _)
      rw [compileWitness_preserves_below m w i _ _ _ _ rest _ v hv']
      simp [Nat.ne_of_lt hv]
    | .constrainEq .. =>
      simp only; exact compileWitness_preserves_below m w i _ _ _ _ rest _ v hv
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      have h_callee_next : next ≤ (compileWitness m w j calleeVarMap next
          calleeEnv calleeObjEnv sd.constrain.body acc).2 :=
        compileWitness_next_le m w j calleeVarMap next
          calleeEnv calleeObjEnv sd.constrain.body acc
      rw [compileWitness_preserves_below m w i varMap _ env objEnv rest _ v
        (Nat.lt_of_lt_of_le hv h_callee_next)]
      exact compileWitness_preserves_below m w j calleeVarMap next
        calleeEnv calleeObjEnv sd.constrain.body acc v hv
termination_by (i, stmts.length)

/-! ### Coherence and bound maintenance -/

-- VarMapBound is preserved when we update varMap with the current next
-- VarMapBound is preserved when we update varMap with the current next
private theorem varMapBound_update (varMap : VarMap) (next : Nat)
    (dest : LocalVar) (hb : VarMapBound varMap next) :
    VarMapBound (varMap.update dest next) (next + 1) := by
  intro v
  simp only [VarMap.update]
  split
  · exact Nat.lt_succ_iff.mpr (Nat.le_refl next)
  · exact Nat.lt_of_lt_of_le (hb v) (Nat.le_succ next)

-- WitnessCoherent is preserved for felt ops (dest := next, val written)
omit [Field F] in
private theorem witnessCoherent_update_felt (acc : FlatIR.VarId → F)
    (varMap : VarMap) (env : LocalEnv F) (next : Nat)
    (dest : LocalVar) (val : F)
    (hcoh : WitnessCoherent acc varMap env)
    (hbound : VarMapBound varMap next) :
    WitnessCoherent
      (fun v => if (v == next) = true then val else acc v)
      (varMap.update dest next) (env.update dest val) := by
  intro v
  simp only [VarMap.update, LocalEnv.update]
  split
  case isTrue h =>
    simp only [beq_iff_eq] at h
    subst h
    simp
  case isFalse h =>
    simp only [beq_iff_eq] at h
    have hne : varMap v ≠ next := Nat.ne_of_lt (hbound v)
    simp [beq_iff_eq, hne, hcoh v]

/-! ### Counter synchronization -/

-- compileWitness and compileConstrainBody produce the same counter
theorem compileWitness_compileConstrainBody_next (m : StructIR.Module n F)
    (w : StructIR.Witness F) (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F) :
    (compileWitness m w i varMap next env objEnv stmts acc).2 =
    (compileConstrainBody m i varMap next stmts).2 := by
  match stmts with
  | [] => simp [compileWitness, compileConstrainBody]
  | stmt :: rest =>
    unfold compileWitness compileConstrainBody
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. | .readMember .. | .constrainEq .. =>
      simp only
      exact compileWitness_compileConstrainBody_next m w i _ _ _ _ rest _
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      have h_callee := compileWitness_compileConstrainBody_next m w j
        calleeVarMap next calleeEnv calleeObjEnv sd.constrain.body acc
      rw [h_callee]
      exact compileWitness_compileConstrainBody_next m w i _ _ _ _ rest _
termination_by (i, stmts.length)

/-! ### Instruction variable bounds -/

-- The counter only increases through compileConstrainBody
omit [Field F] in
theorem compileConstrainBody_next_le (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length)) :
    next ≤ (compileConstrainBody m i varMap next stmts).2 := by
  match stmts with
  | [] => simp [compileConstrainBody]
  | stmt :: rest =>
    unfold compileConstrainBody
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. | .readMember .. =>
      simp only
      exact Nat.le_trans (Nat.le_succ _)
        (compileConstrainBody_next_le m i _ _ rest)
    | .constrainEq .. =>
      simp only; exact compileConstrainBody_next_le m i _ _ rest
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      exact Nat.le_trans
        (compileConstrainBody_next_le m j _ _ _)
        (compileConstrainBody_next_le m i _ _ rest)
termination_by (i, stmts.length)

-- All variables referenced by compiled instructions are bounded by the final next
omit [Field F] in
theorem compileConstrainBody_instrVars_bounded (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hbound : VarMapBound varMap next) :
    ∀ instr ∈ (compileConstrainBody m i varMap next stmts).1,
    ∀ v ∈ instrVars instr,
    v < (compileConstrainBody m i varMap next stmts).2 := by
  match stmts with
  | [] => simp [compileConstrainBody]
  | stmt :: rest =>
    unfold compileConstrainBody
    intro instr hinstr vid hvid
    match stmt with
    | .feltAdd dest src1 src2 | .feltSub dest src1 src2
    | .feltMul dest src1 src2 | .feltDiv dest src1 src2 =>
      simp only at hinstr
      rw [List.mem_append] at hinstr
      have hle : next + 1 ≤ (compileConstrainBody m i
          (varMap.update dest next) (next + 1) rest).2 :=
        compileConstrainBody_next_le m i _ _ rest
      cases hinstr with
      | inl h =>
        simp only [List.mem_singleton] at h; subst h
        simp only [instrVars, List.mem_cons, List.mem_nil_iff, or_false] at hvid
        rcases hvid with rfl | rfl | rfl
        · exact Nat.lt_of_lt_of_le (Nat.lt_succ_iff.mpr (Nat.le_refl vid)) hle
        · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hbound src1) (Nat.le_succ _)) hle
        · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hbound src2) (Nat.le_succ _)) hle
      | inr h =>
        exact compileConstrainBody_instrVars_bounded m i
          (varMap.update dest next) (next + 1) rest
          (varMapBound_update varMap next dest hbound) instr h vid hvid
    | .feltNeg dest src =>
      simp only at hinstr
      rw [List.mem_append] at hinstr
      have hle : next + 1 ≤ (compileConstrainBody m i
          (varMap.update dest next) (next + 1) rest).2 :=
        compileConstrainBody_next_le m i _ _ rest
      cases hinstr with
      | inl h =>
        simp only [List.mem_singleton] at h; subst h
        simp only [instrVars, List.mem_cons, List.mem_nil_iff, or_false] at hvid
        rcases hvid with rfl | rfl
        · exact Nat.lt_of_lt_of_le (Nat.lt_succ_iff.mpr (Nat.le_refl vid)) hle
        · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hbound src) (Nat.le_succ _)) hle
      | inr h =>
        exact compileConstrainBody_instrVars_bounded m i
          (varMap.update dest next) (next + 1) rest
          (varMapBound_update varMap next dest hbound) instr h vid hvid
    | .feltConst dest _c =>
      simp only at hinstr
      rw [List.mem_append] at hinstr
      have hle : next + 1 ≤ (compileConstrainBody m i
          (varMap.update dest next) (next + 1) rest).2 :=
        compileConstrainBody_next_le m i _ _ rest
      cases hinstr with
      | inl h =>
        simp only [List.mem_singleton] at h; subst h
        simp only [instrVars, List.mem_cons, List.mem_nil_iff, or_false] at hvid
        subst hvid
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_iff.mpr (Nat.le_refl vid)) hle
      | inr h =>
        exact compileConstrainBody_instrVars_bounded m i
          (varMap.update dest next) (next + 1) rest
          (varMapBound_update varMap next dest hbound) instr h vid hvid
    | .readMember dest _self _member =>
      simp only at hinstr
      rw [List.mem_append] at hinstr
      cases hinstr with
      | inl h => simp at h
      | inr h =>
        exact compileConstrainBody_instrVars_bounded m i
          (varMap.update dest next) (next + 1) rest
          (varMapBound_update varMap next dest hbound) instr h vid hvid
    | .constrainEq src1 src2 =>
      simp only at hinstr
      rw [List.mem_append] at hinstr
      cases hinstr with
      | inl h =>
        simp only [List.mem_singleton] at h; subst h
        simp only [instrVars, List.mem_cons, List.mem_nil_iff, or_false] at hvid
        have hle : next ≤ (compileConstrainBody m i varMap next rest).2 :=
          compileConstrainBody_next_le m i _ _ rest
        rcases hvid with rfl | rfl
        · exact Nat.lt_of_lt_of_le (hbound src1) hle
        · exact Nat.lt_of_lt_of_le (hbound src2) hle
      | inr h =>
        exact compileConstrainBody_instrVars_bounded m i varMap next rest
          hbound instr h vid hvid
    | .call target args =>
      simp only at hinstr
      rw [List.mem_append] at hinstr
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with
        | some arg => varMap arg
        | none => 0
      have h_callee_bound : VarMapBound calleeVarMap next := by
        intro param
        simp only [calleeVarMap]
        split
        case h_1 arg _ => exact hbound arg
        case h_2 => exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hbound 0)
      cases hinstr with
      | inl h =>
        have h_callee := compileConstrainBody_instrVars_bounded m j
          calleeVarMap next sd.constrain.body h_callee_bound instr h vid hvid
        have hle_rest : (compileConstrainBody m j calleeVarMap next
            sd.constrain.body).2 ≤
            (compileConstrainBody m i varMap
              (compileConstrainBody m j calleeVarMap next sd.constrain.body).2
              rest).2 :=
          compileConstrainBody_next_le m i _ _ rest
        exact Nat.lt_of_lt_of_le h_callee hle_rest
      | inr h =>
        have hle_callee : next ≤ (compileConstrainBody m j calleeVarMap next
            sd.constrain.body).2 :=
          compileConstrainBody_next_le m j _ _ _
        have hbound' : VarMapBound varMap
            (compileConstrainBody m j calleeVarMap next sd.constrain.body).2 :=
          fun param => Nat.lt_of_lt_of_le (hbound param) hle_callee
        exact compileConstrainBody_instrVars_bounded m i varMap
          (compileConstrainBody m j calleeVarMap next sd.constrain.body).2
          rest hbound' instr h vid hvid
termination_by (i, stmts.length)

/-! ### compileWitness and buildVarAlloc agreement -/

-- buildVarAlloc counter stays in sync with compileConstrainBody/compileWitness.
-- (Same recursion structure: felt ops +1, readMember +1, constrainEq +0, call recurses.)
omit [Field F] in
theorem buildVarAlloc_next_eq (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (allocAcc : StructIR.VarId → FlatIR.VarId) :
    (buildVarAlloc m i varMap next objEnv stmts allocAcc).2 =
    (compileConstrainBody m i varMap next stmts).2 := by
  match stmts with
  | [] => simp [buildVarAlloc, compileConstrainBody]
  | stmt :: rest =>
    unfold buildVarAlloc compileConstrainBody
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. | .readMember .. | .constrainEq .. =>
      simp only
      exact buildVarAlloc_next_eq m i _ _ _ rest _
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      have h_callee := buildVarAlloc_next_eq m j calleeVarMap next
        calleeObjEnv sd.constrain.body allocAcc
      rw [h_callee]
      exact buildVarAlloc_next_eq m i _ _ _ rest _
termination_by (i, stmts.length)

-- buildVarAlloc preserves the bound: if all non-zero entries of allocAcc are < next,
-- then all non-zero entries of the result are < the result counter.
omit [Field F] in
theorem buildVarAlloc_alloc_bound (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (allocAcc : StructIR.VarId → FlatIR.VarId)
    (hbound : ∀ vid, allocAcc vid ≠ 0 → allocAcc vid < next) :
    ∀ vid, (buildVarAlloc m i varMap next objEnv stmts allocAcc).1 vid ≠ 0 →
      (buildVarAlloc m i varMap next objEnv stmts allocAcc).1 vid <
      (buildVarAlloc m i varMap next objEnv stmts allocAcc).2 := by
  match stmts with
  | [] => unfold buildVarAlloc; exact hbound
  | stmt :: rest =>
    unfold buildVarAlloc
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. =>
      simp only
      exact buildVarAlloc_alloc_bound m i _ _ _ rest _
        (fun vid h => Nat.lt_of_lt_of_le (hbound vid h) (Nat.le_succ _))
    | .readMember dest self member =>
      simp only
      exact buildVarAlloc_alloc_bound m i _ _ _ rest _
        (fun vid h => by
          split
          case isTrue => exact Nat.lt_succ_iff.mpr le_rfl
          case isFalse hne =>
            simp only [hne] at h
            exact Nat.lt_of_lt_of_le (hbound vid h) (Nat.le_succ _))
    | .constrainEq .. =>
      simp only
      exact buildVarAlloc_alloc_bound m i _ _ _ rest _ hbound
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      exact buildVarAlloc_alloc_bound m i _ _ _ rest _
        (buildVarAlloc_alloc_bound m j calleeVarMap next
          calleeObjEnv sd.constrain.body allocAcc hbound)
termination_by (i, stmts.length)

-- buildVarAlloc preserves allocAcc entries for VarIds not in readPositions.
-- If a VarId is not read by any readMember in the traversal, its allocation is unchanged.
omit [Field F] in
theorem buildVarAlloc_preserves_absent (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (allocAcc : StructIR.VarId → FlatIR.VarId) (vid : StructIR.VarId)
    (habsent : vid ∉ StructIR.readPositions m.structs i objEnv stmts) :
    (buildVarAlloc m i varMap next objEnv stmts allocAcc).1 vid = allocAcc vid := by
  match stmts with
  | [] => unfold buildVarAlloc; rfl
  | stmt :: rest =>
    unfold buildVarAlloc readPositions at *
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. =>
      simp only at habsent ⊢
      exact buildVarAlloc_preserves_absent m i _ _ _ rest _ vid habsent
    | .readMember dest self member =>
      simp only at habsent ⊢
      simp only [List.cons_append, List.mem_cons, List.nil_append] at habsent
      push_neg at habsent
      obtain ⟨hne, habsent_rest⟩ := habsent
      have : (fun v => if v == (objEnv self, ↑member) then next else allocAcc v) vid
          = allocAcc vid := by
        simp only [beq_iff_eq]
        split
        case isTrue h => exact absurd h hne
        case isFalse => rfl
      rw [buildVarAlloc_preserves_absent m i _ _ _ rest _ vid habsent_rest]
      exact this
    | .constrainEq .. =>
      simp only at habsent ⊢
      exact buildVarAlloc_preserves_absent m i _ _ _ rest _ vid habsent
    | .call target args =>
      simp only at habsent ⊢
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      simp only [List.mem_append] at habsent
      push_neg at habsent
      obtain ⟨habsent_callee, habsent_rest⟩ := habsent
      rw [buildVarAlloc_preserves_absent m i _ _ _ rest _ vid habsent_rest]
      exact buildVarAlloc_preserves_absent m j _ _ _ sd.constrain.body _ vid habsent_callee
  termination_by (i, stmts.length)

-- buildVarAlloc result at positions in readPositions does not depend on the accumulator.
-- This is because buildVarAlloc overwrites those positions, so the initial value is irrelevant.
omit [Field F] in
theorem buildVarAlloc_acc_irrelevant (m : StructIR.Module n F)
    (i : Fin n) (varMap : VarMap) (next : Nat) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc1 acc2 : StructIR.VarId → FlatIR.VarId) (vid : StructIR.VarId)
    (hnodup : (StructIR.readPositions m.structs i objEnv stmts).Nodup)
    (hin : vid ∈ StructIR.readPositions m.structs i objEnv stmts) :
    (buildVarAlloc m i varMap next objEnv stmts acc1).1 vid =
    (buildVarAlloc m i varMap next objEnv stmts acc2).1 vid := by
  match stmts with
  | [] => simp [StructIR.readPositions] at hin
  | stmt :: rest =>
    unfold buildVarAlloc StructIR.readPositions at *
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. =>
      simp only at *
      exact buildVarAlloc_acc_irrelevant m i _ _ _ rest acc1 acc2 vid hnodup hin
    | .readMember dest self member =>
      simp only at *
      simp only [List.cons_append, List.nil_append] at hnodup hin
      have habsent := (List.nodup_cons.mp hnodup).1
      have hnodup_rest := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hin with heq | hin_rest
      · -- vid = (objEnv self, member.val): both accumulators set it to `next`
        subst heq
        rw [buildVarAlloc_preserves_absent m i _ _ _ rest _ _ habsent]
        rw [buildVarAlloc_preserves_absent m i _ _ _ rest _ _ habsent]
        simp only [beq_self_eq_true, ↓reduceIte]
      · -- vid ∈ readPositions rest: by IH
        have hne : vid ≠ (objEnv self, (member : Nat)) := fun h => habsent (h ▸ hin_rest)
        have hacc1' : (fun v => if v == (objEnv self, ↑member) then next else acc1 v) vid
            = acc1 vid := by simp [beq_iff_eq, hne]
        have hacc2' : (fun v => if v == (objEnv self, ↑member) then next else acc2 v) vid
            = acc2 vid := by simp [beq_iff_eq, hne]
        -- The updated accumulators still differ only outside readPositions rest
        -- But IH handles that
        exact buildVarAlloc_acc_irrelevant m i _ _ _ rest _ _ vid hnodup_rest hin_rest
    | .constrainEq .. =>
      simp only at *
      exact buildVarAlloc_acc_irrelevant m i _ _ _ rest acc1 acc2 vid hnodup hin
    | .call target args =>
      simp only at *
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      rw [List.nodup_append] at hnodup
      obtain ⟨hnodup_callee, hnodup_rest, hdisjoint⟩ := hnodup
      rcases List.mem_append.mp hin with hin_callee | hin_rest
      · -- vid ∈ readPositions callee: callee sets the value, rest preserves it
        have habsent_rest : vid ∉ StructIR.readPositions m.structs i objEnv rest :=
          fun h => hdisjoint vid hin_callee vid h rfl
        rw [buildVarAlloc_preserves_absent m i _ _ _ rest _ _ habsent_rest]
        rw [buildVarAlloc_preserves_absent m i _ _ _ rest _ _ habsent_rest]
        exact buildVarAlloc_acc_irrelevant m j calleeVarMap next calleeObjEnv
          sd.constrain.body acc1 acc2 vid hnodup_callee hin_callee
      · -- vid ∈ readPositions rest: rest sets the value
        have habsent_callee : vid ∉ StructIR.readPositions m.structs j calleeObjEnv
            sd.constrain.body :=
          fun h => hdisjoint vid h vid hin_rest rfl
        -- Rest uses callee's output as accumulator; the callee outputs may differ
        -- but vid is set by rest independently of accumulator (by IH).
        -- The next counters agree (buildVarAlloc_next_eq).
        have h_next_eq : (buildVarAlloc m j calleeVarMap next calleeObjEnv
            sd.constrain.body acc1).2 = (buildVarAlloc m j calleeVarMap next calleeObjEnv
            sd.constrain.body acc2).2 := by
          rw [buildVarAlloc_next_eq, buildVarAlloc_next_eq]
        conv_lhs => rw [show (buildVarAlloc m j calleeVarMap next calleeObjEnv
            sd.constrain.body acc1).2 = (buildVarAlloc m j calleeVarMap next calleeObjEnv
            sd.constrain.body acc2).2 from h_next_eq]
        exact buildVarAlloc_acc_irrelevant m i varMap _ _ rest _ _ vid hnodup_rest hin_rest
  termination_by (i, stmts.length)

-- Coherence update lemma for felt ops in reflection_direct:
-- If wt next equals some value that, under coherence, equals val_env,
-- then coherence is maintained after env/varMap update.
omit [Field F] in
private theorem witnessCoherent_update_from_sat
    (wt : FlatIR.VarId → F) (varMap : VarMap) (env : LocalEnv F)
    (next : Nat) (dest : LocalVar) (val_env : F)
    (hcoh : WitnessCoherent wt varMap env)
    (hval : wt next = val_env) :
    WitnessCoherent wt (varMap.update dest next)
      (env.update dest val_env) := by
  intro v; simp only [VarMap.update, LocalEnv.update]
  split
  case isTrue h =>
    simp only [beq_iff_eq] at h; subst h; exact hval
  case isFalse => exact hcoh v

-- Main reflection theorem: directly uses wt (the FlatIR witness) to prove
-- StructIR evaluation, without going through compileWitness.
theorem reflection_direct (m : StructIR.Module n F) (w : StructIR.Witness F)
    (wt : FlatIR.VarId → F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (hcoh : WitnessCoherent wt varMap env)
    (hbound : VarMapBound varMap next)
    (hpoz : 0 < next)
    (hwt_zero : wt 0 = 0)
    (hnodup : (StructIR.readPositions m.structs i objEnv stmts).Nodup)
    (hw : ∀ vid,
      (buildVarAlloc m i varMap next objEnv stmts (fun _ => 0)).1 vid ≠ 0 →
      w vid = wt ((buildVarAlloc m i varMap next objEnv stmts (fun _ => 0)).1 vid))
    (hsat : ∀ instr ∈ (compileConstrainBody m i varMap next stmts).1,
      FlatIR.satisfiesInstr wt instr) :
    evalConstrainBody m w i env objEnv stmts := by
  match stmts with
  | [] => simp [evalConstrainBody]
  | stmt :: rest =>
    unfold evalConstrainBody compileConstrainBody buildVarAlloc readPositions at *
    match stmt with
    | .feltAdd dest src1 src2 =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assignAdd next (varMap src1) (varMap src2))
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      exact ⟨trivial, reflection_direct m w wt i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 + env src2)) objEnv rest
        (witnessCoherent_update_from_sat wt varMap env next dest _ hcoh
          (by rw [hsat_instr, hcoh src1, hcoh src2]))
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        hwt_zero hnodup hw hsat_rest⟩
    | .feltSub dest src1 src2 =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assignSub next (varMap src1) (varMap src2))
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      exact ⟨trivial, reflection_direct m w wt i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 - env src2)) objEnv rest
        (witnessCoherent_update_from_sat wt varMap env next dest _ hcoh
          (by rw [hsat_instr, hcoh src1, hcoh src2]))
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        hwt_zero hnodup hw hsat_rest⟩
    | .feltMul dest src1 src2 =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assignMul next (varMap src1) (varMap src2))
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      exact ⟨trivial, reflection_direct m w wt i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 * env src2)) objEnv rest
        (witnessCoherent_update_from_sat wt varMap env next dest _ hcoh
          (by rw [hsat_instr, hcoh src1, hcoh src2]))
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        hwt_zero hnodup hw hsat_rest⟩
    | .feltDiv dest src1 src2 =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assignDiv next (varMap src1) (varMap src2))
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      obtain ⟨hne_wt, hsat_eq⟩ := hsat_instr
      have hne_env : env src2 ≠ 0 := by
        rw [← hcoh src2]; exact hne_wt
      exact ⟨hne_env, reflection_direct m w wt i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 * (env src2)⁻¹)) objEnv rest
        (witnessCoherent_update_from_sat wt varMap env next dest _ hcoh
          (by rw [hsat_eq, hcoh src1, hcoh src2]))
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        hwt_zero hnodup hw hsat_rest⟩
    | .feltNeg dest src =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assignNeg next (varMap src))
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      exact ⟨trivial, reflection_direct m w wt i (varMap.update dest next) (next + 1)
        (env.update dest (-(env src))) objEnv rest
        (witnessCoherent_update_from_sat wt varMap env next dest _ hcoh
          (by rw [hsat_instr, hcoh src]))
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        hwt_zero hnodup hw hsat_rest⟩
    | .feltConst dest c =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assignConst next c)
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      exact ⟨trivial, reflection_direct m w wt i (varMap.update dest next) (next + 1)
        (env.update dest c) objEnv rest
        (witnessCoherent_update_from_sat wt varMap env next dest _ hcoh hsat_instr)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        hwt_zero hnodup hw hsat_rest⟩
    | .readMember dest self member =>
      simp only at *
      simp only [List.cons_append, List.nil_append] at hnodup
      let objEnv' := objEnv.update dest (objEnv self ++ [member.val])
      have habsent : (objEnv self, (member : Nat)) ∉
          StructIR.readPositions m.structs i objEnv' rest :=
        (List.nodup_cons.mp hnodup).1
      have hnodup_rest : (StructIR.readPositions m.structs i objEnv' rest).Nodup :=
        (List.nodup_cons.mp hnodup).2
      -- readMember: env' = env.update dest (w (path, member))
      -- varMap' = varMap.update dest next, next' = next + 1
      -- Need: w (objEnv self, member.val) = wt next (for coherence update)
      -- From hw: buildVarAlloc sets (objEnv self, member.val) → next
      -- Since (objEnv self, member.val) ∉ readPositions rest (from hnodup),
      -- buildVarAlloc_preserves_absent gives us the final value is still next
      have halloc_val : (buildVarAlloc m i (varMap.update dest next) (next + 1) objEnv' rest
          (fun v => if v == (objEnv self, ↑member) then next else 0)).1
          (objEnv self, ↑member) = next := by
        rw [buildVarAlloc_preserves_absent m i (varMap.update dest next) (next + 1) objEnv'
          rest _ (objEnv self, ↑member) habsent]
        simp only [beq_self_eq_true, ↓reduceIte]
      have hne_next : (next : FlatIR.VarId) ≠ 0 := by omega
      have hw_val : w (objEnv self, ↑member) = wt next := by
        have := hw (objEnv self, ↑member) (by rw [halloc_val]; exact hne_next)
        rw [halloc_val] at this; exact this
      -- Coherence update: wt next = w (path, member) = env' dest
      have hcoh' : WitnessCoherent wt (varMap.update dest next)
          (env.update dest (w (objEnv self, ↑member))) := by
        intro v; simp only [VarMap.update, LocalEnv.update]
        split
        case isTrue h =>
          simp only [beq_iff_eq] at h; subst h
          exact hw_val.symm
        case isFalse h => exact hcoh v
      -- Convert hw from updated accumulator to zero accumulator for recursive call.
      -- Key: if (buildVarAlloc ... (fun _ => 0)).1 vid ≠ 0, then vid ∈ readPositions rest
      -- (otherwise preserves_absent gives 0), so acc_irrelevant applies.
      have hw' : ∀ vid,
          (buildVarAlloc m i (varMap.update dest next) (next + 1) objEnv' rest (fun _ => 0)).1
            vid ≠ 0 →
          w vid = wt ((buildVarAlloc m i (varMap.update dest next) (next + 1) objEnv' rest
            (fun _ => 0)).1 vid) := by
        intro vid hne_vid
        -- Show vid ∈ readPositions rest by contradiction
        have hin_rest : vid ∈ StructIR.readPositions m.structs i objEnv' rest := by
          by_contra h
          exact hne_vid (buildVarAlloc_preserves_absent m i (varMap.update dest next)
            (next + 1) objEnv' rest (fun _ => 0) vid h)
        -- Use acc_irrelevant to equate the two accumulator versions
        have h_eq := buildVarAlloc_acc_irrelevant m i (varMap.update dest next) (next + 1)
          objEnv' rest (fun _ => 0)
          (fun v => if v == (objEnv self, ↑member) then next else 0) vid
          hnodup_rest hin_rest
        rw [h_eq]
        exact hw vid (by rw [← h_eq]; exact hne_vid)
      constructor
      · trivial
      · exact reflection_direct m w wt i (varMap.update dest next) (next + 1)
          (env.update dest (w (objEnv self, ↑member))) objEnv' rest
          hcoh' (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          hwt_zero hnodup_rest hw' hsat
    | .constrainEq src1 src2 =>
      simp only at *
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      have hsat_instr := hsat_head (Instr.assertEq (varMap src1) (varMap src2))
        (List.mem_cons_self ..)
      simp only [satisfiesInstr] at hsat_instr
      constructor
      · -- env src1 = env src2 from coherence + wt satisfaction
        rw [← hcoh src1, ← hcoh src2]; exact hsat_instr
      · exact reflection_direct m w wt i varMap next env objEnv rest
          hcoh hbound hpoz hwt_zero hnodup hw hsat_rest
    | .call target args =>
      simp only at *
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      -- Decompose hsat: callee instructions ++ rest instructions
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_callee, hsat_rest⟩ := hsat
      -- Decompose hnodup: callee reads ++ rest reads are nodup
      rw [List.nodup_append] at hnodup
      obtain ⟨hnodup_callee, hnodup_rest, hdisjoint⟩ := hnodup
      -- Callee coherence (hwt_zero handles unmapped params)
      have hcoh_callee : WitnessCoherent wt calleeVarMap calleeEnv := by
        intro v; simp only [calleeVarMap, calleeEnv]
        cases h : args[v]? with
        | none => exact hwt_zero
        | some arg => exact hcoh arg
      -- Callee bound
      have hbound_callee : VarMapBound calleeVarMap next := by
        intro v; simp only [calleeVarMap]
        cases h : args[v]? with
        | none => exact hpoz
        | some arg => exact hbound arg
      -- hw_callee: for callee allocations, the full alloc preserves them
      -- because callee reads are disjoint from rest reads
      have hw_callee : ∀ vid,
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).1 vid ≠ 0 →
          w vid = wt ((buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).1 vid) := by
        intro vid hne
        -- vid has a nonzero callee alloc, so vid ∈ readPositions callee
        have hin_callee : vid ∈ StructIR.readPositions m.structs j calleeObjEnv
            sd.constrain.body := by
          by_contra h
          exact hne (buildVarAlloc_preserves_absent m j calleeVarMap next calleeObjEnv
            sd.constrain.body (fun _ => 0) vid h)
        -- Since vid ∈ callee reads and callee/rest reads are disjoint, vid ∉ rest reads
        have habsent_rest : vid ∉ StructIR.readPositions m.structs i objEnv rest :=
          fun h => hdisjoint vid hin_callee vid h rfl
        -- So rest's buildVarAlloc preserves callee's allocation
        have h_preserved := buildVarAlloc_preserves_absent m i varMap
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).2
          objEnv rest
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).1
          vid habsent_rest
        -- Use hw with the preserved value
        have h_full := hw vid (by rw [h_preserved]; exact hne)
        rw [h_preserved] at h_full
        exact h_full
      -- hw_rest: for rest allocations, similar reasoning
      have hw_rest : ∀ vid,
          (buildVarAlloc m i varMap
            (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
              (fun _ => 0)).2
            objEnv rest (fun _ => 0)).1 vid ≠ 0 →
          w vid = wt ((buildVarAlloc m i varMap
            (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
              (fun _ => 0)).2
            objEnv rest (fun _ => 0)).1 vid) := by
        intro vid hne
        -- vid ∈ readPositions rest
        have hin_rest : vid ∈ StructIR.readPositions m.structs i objEnv rest := by
          by_contra h
          exact hne (buildVarAlloc_preserves_absent m i varMap _ objEnv rest
            (fun _ => 0) vid h)
        -- Use acc_irrelevant: rest's result at vid is the same regardless of accumulator
        have h_eq := buildVarAlloc_acc_irrelevant m i varMap
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).2
          objEnv rest (fun _ => 0)
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).1
          vid hnodup_rest hin_rest
        rw [h_eq]
        exact hw vid (by rw [← h_eq]; exact hne)
      -- hsat_rest needs the right next value
      have h_next_sync := buildVarAlloc_next_eq m j calleeVarMap next calleeObjEnv
        sd.constrain.body (fun _ => (0 : Nat))
      -- hbound_rest: varMap is still bounded by callee's output next
      have hbound_rest : VarMapBound varMap
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).2 := by
        intro v; rw [h_next_sync]
        exact Nat.lt_of_lt_of_le (hbound v) (compileConstrainBody_next_le m j _ _ _)
      have hpoz_rest : 0 <
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).2 := by
        rw [h_next_sync]
        exact Nat.lt_of_lt_of_le hpoz (compileConstrainBody_next_le m j _ _ _)
      -- hsat_rest alignment: compileConstrainBody next = buildVarAlloc next
      have hsat_rest' : ∀ instr ∈ (compileConstrainBody m i varMap
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).2
          rest).1, FlatIR.satisfiesInstr wt instr := by
        rw [h_next_sync]; exact hsat_rest
      constructor
      · exact reflection_direct m w wt j calleeVarMap next calleeEnv calleeObjEnv
          sd.constrain.body hcoh_callee hbound_callee hpoz hwt_zero hnodup_callee
          hw_callee hsat_callee
      · exact reflection_direct m w wt i varMap
          (buildVarAlloc m j calleeVarMap next calleeObjEnv sd.constrain.body
            (fun _ => 0)).2
          env objEnv rest
          hcoh hbound_rest hpoz_rest hwt_zero hnodup_rest hw_rest hsat_rest'

-- compileWitness agrees with the source witness at positions tracked by buildVarAlloc.
-- Key property: for each readMember, compileWitness records w(path, member) at position
-- `next`, and buildVarAlloc records (path, member) → next. Since compileWitness preserves
-- values below `next`, the final compileWitness result at varAlloc(vid) equals w(vid).
theorem compileWitness_varAlloc_agree (m : StructIR.Module n F)
    (w : StructIR.Witness F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F)
    (allocAcc : StructIR.VarId → FlatIR.VarId)
    (hpoz : 0 < next)
    (halloc_bound : ∀ vid, allocAcc vid ≠ 0 → allocAcc vid < next)
    -- Previous allocations are consistent:
    --  compileWitness result agrees with w at allocAcc positions
    (hprev : ∀ vid, allocAcc vid ≠ 0 → allocAcc vid < next →
      acc (allocAcc vid) = w vid) :
    let bw := (compileWitness m w i varMap next env objEnv stmts acc).1
    let va := (buildVarAlloc m i varMap next objEnv stmts allocAcc).1
    ∀ vid, va vid ≠ 0 → bw (va vid) = w vid := by
  match stmts with
  | [] =>
    unfold compileWitness buildVarAlloc
    intro _ _ vid hne
    exact hprev vid hne (halloc_bound vid hne)
  | stmt :: rest =>
    unfold compileWitness buildVarAlloc
    match stmt with
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltConst .. =>
      simp only
      apply compileWitness_varAlloc_agree m w i _ _ _ _ rest _ _
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
      · intro vid hne
        exact Nat.lt_of_lt_of_le (halloc_bound vid hne) (Nat.le_succ _)
      · intro vid hne hlt
        have hne_next : allocAcc vid ≠ next :=
          Nat.ne_of_lt (halloc_bound vid hne)
        simp only [beq_iff_eq, hne_next, ↓reduceIte]
        exact hprev vid hne (halloc_bound vid hne)
    | .readMember dest self member =>
      simp only
      apply compileWitness_varAlloc_agree m w i _ _ _ _ rest _ _
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
      · -- halloc_bound for readMember: allocAcc' vid ≠ 0 → allocAcc' vid < next + 1
        intro vid hne
        split
        case isTrue => exact Nat.lt_succ_iff.mpr le_rfl
        case isFalse hne_eq =>
          simp only [hne_eq] at hne
          exact Nat.lt_of_lt_of_le (halloc_bound vid hne) (Nat.le_succ _)
      · -- hprev for readMember: acc' (allocAcc' vid) = w vid
        intro vid hne hlt
        split
        case isTrue heq =>
          -- vid == (path, member), allocAcc' vid = next, acc' next = w (path, member)
          simp only [BEq.rfl, ↓reduceIte]
          have := beq_iff_eq.mp heq
          rw [this]
        case isFalse hne_eq =>
          -- vid ≠ (path, member), allocAcc' vid = allocAcc vid
          simp only [hne_eq] at hne hlt
          have hne_next : allocAcc vid ≠ next :=
            Nat.ne_of_lt (halloc_bound vid hne)
          simp only [beq_iff_eq, hne_next, ↓reduceIte]
          exact hprev vid hne (halloc_bound vid hne)
    | .constrainEq src1 src2 =>
      simp only
      exact compileWitness_varAlloc_agree m w i _ _ _ _ rest _ _
        hpoz halloc_bound hprev
    | .call target args =>
      simp only
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      -- Sync buildVarAlloc and compileWitness counters for callee
      have h_callee_sync := buildVarAlloc_next_eq m j calleeVarMap next
        calleeObjEnv sd.constrain.body allocAcc
      have h_callee_sync_bw := compileWitness_compileConstrainBody_next m w j
        calleeVarMap next calleeEnv calleeObjEnv sd.constrain.body acc
      -- Rewrite buildVarAlloc counter to compileWitness counter in goal
      have h_va_eq_bw : (buildVarAlloc m j calleeVarMap next
          calleeObjEnv sd.constrain.body allocAcc).2 =
          (compileWitness m w j calleeVarMap next
          calleeEnv calleeObjEnv sd.constrain.body acc).2 := by
        rw [h_callee_sync, h_callee_sync_bw]
      rw [h_va_eq_bw]
      -- Apply IH to callee
      have h_callee_agree := compileWitness_varAlloc_agree m w j
        calleeVarMap next calleeEnv calleeObjEnv sd.constrain.body
        acc allocAcc hpoz halloc_bound hprev
      -- Get callee bound
      have h_callee_bound := buildVarAlloc_alloc_bound m j calleeVarMap next
        calleeObjEnv sd.constrain.body allocAcc halloc_bound
      -- Get callee next >= next
      have h_callee_next_le : next ≤ (compileWitness m w j calleeVarMap next
          calleeEnv calleeObjEnv sd.constrain.body acc).2 :=
        compileWitness_next_le m w j calleeVarMap next calleeEnv calleeObjEnv
          sd.constrain.body acc
      -- callee alloc bound in terms of compileWitness counter
      have h_callee_bound' : ∀ vid,
          (buildVarAlloc m j calleeVarMap next
            calleeObjEnv sd.constrain.body allocAcc).1 vid ≠ 0 →
          (buildVarAlloc m j calleeVarMap next
            calleeObjEnv sd.constrain.body allocAcc).1 vid <
          (compileWitness m w j calleeVarMap next
            calleeEnv calleeObjEnv sd.constrain.body acc).2 := by
        intro vid hne
        rw [h_callee_sync_bw, ← h_callee_sync]
        exact h_callee_bound vid hne
      -- Apply IH to rest
      apply compileWitness_varAlloc_agree m w i varMap _ env objEnv rest _ _
        (Nat.lt_of_lt_of_le hpoz h_callee_next_le)
        h_callee_bound'
      -- hprev for rest: callee results agree
      intro vid hne hlt
      exact h_callee_agree vid hne
  termination_by (i, stmts.length)

/-! ### Core preservation lemma -/

-- Helper: acc 0 = 0 is preserved by compileWitness (0 < next ensures slot 0 is never overwritten)
private theorem compileWitness_preserves_zero (m : StructIR.Module n F)
    (w : StructIR.Witness F) (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F) (hpoz : 0 < next) (hacc_zero : acc 0 = 0) :
    (compileWitness m w i varMap next env objEnv stmts acc).1 0 = 0 := by
  rw [compileWitness_preserves_below m w i varMap next env objEnv stmts acc 0 hpoz]
  exact hacc_zero

-- Helper: WitnessCoherent is preserved through compileWitness when varMap values are below next
private theorem witnessCoherent_after_compileWitness (m : StructIR.Module n F)
    (w : StructIR.Witness F) (j : Fin n) (calleeVarMap : VarMap) (next : Nat)
    (calleeEnv : LocalEnv F) (calleeObjEnv : ObjEnv)
    (calleeStmts : List (ConstrainStmt n j F (m.structs j).members.length))
    (acc : FlatIR.VarId → F) (varMap : VarMap) (env : LocalEnv F)
    (hcoh : WitnessCoherent acc varMap env)
    (hbound : VarMapBound varMap next) :
    WitnessCoherent
      (compileWitness m w j calleeVarMap next calleeEnv calleeObjEnv calleeStmts acc).1
      varMap env := by
  intro v
  rw [compileWitness_preserves_below m w j calleeVarMap next calleeEnv calleeObjEnv
    calleeStmts acc (varMap v) (hbound v)]
  exact hcoh v

-- Helper: for a binop head instruction in preservation_body, after peeling back
-- compileWitness to the accumulator, the result at `next` is `val`, and at
-- `varMap src1/src2` is `env src1/src2` via coherence.
private theorem preservation_body_peel_binop (m : StructIR.Module n F)
    (w : StructIR.Witness F) (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (rest : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F) (dest src1 src2 : LocalVar) (val : F)
    (hcoh : WitnessCoherent acc varMap env)
    (hbound : VarMapBound varMap next) :
    let flatW := (compileWitness m w i (varMap.update dest next) (next + 1)
      (env.update dest val) objEnv rest
      (fun v => if (v == next) = true then val else acc v)).1
    flatW next = val ∧ flatW (varMap src1) = env src1 ∧ flatW (varMap src2) = env src2 := by
  constructor
  · rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
      (env.update dest val) objEnv rest
      (fun v => if (v == next) = true then val else acc v) next
      (Nat.lt_succ_iff.mpr le_rfl)]
    simp
  constructor
  · rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
      (env.update dest val) objEnv rest
      (fun v => if (v == next) = true then val else acc v) (varMap src1)
      (Nat.lt_of_lt_of_le (hbound src1) (Nat.le_succ _))]
    simp [Nat.ne_of_lt (hbound src1), hcoh src1]
  · rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
      (env.update dest val) objEnv rest
      (fun v => if (v == next) = true then val else acc v) (varMap src2)
      (Nat.lt_of_lt_of_le (hbound src2) (Nat.le_succ _))]
    simp [Nat.ne_of_lt (hbound src2), hcoh src2]

-- Core preservation lemma for a constrain body
theorem preservation_body (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F)
    (hcoh : WitnessCoherent acc varMap env)
    (hbound : VarMapBound varMap next)
    (hpoz : 0 < next) (hacc_zero : acc 0 = 0)
    (heval : evalConstrainBody m w i env objEnv stmts) :
    let flatW := (compileWitness m w i varMap next env objEnv stmts acc).1
    let instrs := (compileConstrainBody m i varMap next stmts).1
    ∀ instr ∈ instrs, FlatIR.satisfiesInstr flatW instr := by
  match stmts with
  | [] => unfold compileConstrainBody compileWitness; simp
  | stmt :: rest =>
    match stmt with
    | .feltAdd dest src1 src2 =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨_, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        obtain ⟨h1, h2, h3⟩ := preservation_body_peel_binop m w i varMap next env objEnv
          rest acc dest src1 src2 _ hcoh hbound
        rw [h1, h2, h3]
      · exact preservation_body m w i (varMap.update dest next) (next + 1)
          (env.update dest (env src1 + env src2)) objEnv rest
          (fun v => if (v == next) = true then env src1 + env src2 else acc v)
          (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
          (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .feltSub dest src1 src2 =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨_, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        obtain ⟨h1, h2, h3⟩ := preservation_body_peel_binop m w i varMap next env objEnv
          rest acc dest src1 src2 _ hcoh hbound
        rw [h1, h2, h3]
      · exact preservation_body m w i (varMap.update dest next) (next + 1)
          (env.update dest (env src1 - env src2)) objEnv rest
          (fun v => if (v == next) = true then env src1 - env src2 else acc v)
          (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
          (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .feltMul dest src1 src2 =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨_, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        obtain ⟨h1, h2, h3⟩ := preservation_body_peel_binop m w i varMap next env objEnv
          rest acc dest src1 src2 _ hcoh hbound
        rw [h1, h2, h3]
      · exact preservation_body m w i (varMap.update dest next) (next + 1)
          (env.update dest (env src1 * env src2)) objEnv rest
          (fun v => if (v == next) = true then env src1 * env src2 else acc v)
          (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
          (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .feltDiv dest src1 src2 =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨hne, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        obtain ⟨h1, h2, h3⟩ := preservation_body_peel_binop m w i varMap next env objEnv
          rest acc dest src1 src2 _ hcoh hbound
        exact ⟨by rw [h3]; exact hne, by rw [h1, h2, h3]⟩
      · exact preservation_body m w i (varMap.update dest next) (next + 1)
          (env.update dest (env src1 * (env src2)⁻¹)) objEnv rest
          (fun v => if (v == next) = true then env src1 * (env src2)⁻¹ else acc v)
          (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
          (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .feltNeg dest src =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨_, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
          (env.update dest (-(env src))) objEnv rest
          (fun v => if (v == next) = true then -(env src) else acc v) next
          (Nat.lt_succ_iff.mpr le_rfl)]
        rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
          (env.update dest (-(env src))) objEnv rest
          (fun v => if (v == next) = true then -(env src) else acc v) (varMap src)
          (by exact Nat.lt_of_lt_of_le (hbound src) (Nat.le_succ _))]
        simp [Nat.ne_of_lt (hbound src), hcoh src]
      · exact preservation_body m w i (varMap.update dest next) (next + 1)
          (env.update dest (-(env src))) objEnv rest
          (fun v => if (v == next) = true then -(env src) else acc v)
          (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
          (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .feltConst dest c =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨_, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
          (env.update dest c) objEnv rest
          (fun v => if (v == next) = true then c else acc v) next
          (Nat.lt_succ_iff.mpr le_rfl)]
        simp
      · exact preservation_body m w i (varMap.update dest next) (next + 1)
          (env.update dest c) objEnv rest
          (fun v => if (v == next) = true then c else acc v)
          (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
          (varMapBound_update varMap next dest hbound)
          (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
          (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .readMember dest self member =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨_, hrest⟩ := heval
      intro instr hmem
      rw [List.nil_append] at hmem
      let objEnv' := objEnv.update dest (objEnv self ++ [member.val])
      exact preservation_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (w (objEnv self, member.val))) objEnv' rest
        (fun v => if (v == next) = true then w (objEnv self, member.val) else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hrest instr hmem
    | .constrainEq src1 src2 =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨heq, hrest⟩ := heval
      intro instr hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        simp only [satisfiesInstr]
        rw [compileWitness_preserves_below m w i varMap next env objEnv rest acc (varMap src1)
          (hbound src1)]
        rw [compileWitness_preserves_below m w i varMap next env objEnv rest acc (varMap src2)
          (hbound src2)]
        rw [hcoh src1, hcoh src2, heq]
      · exact preservation_body m w i varMap next env objEnv rest acc
          hcoh hbound hpoz hacc_zero hrest instr hmem
    | .call target args =>
      simp only [compileConstrainBody, compileWitness, evalConstrainBody] at *
      obtain ⟨hcall, hrest⟩ := heval
      intro instr hmem
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      have hcoh_callee : WitnessCoherent acc calleeVarMap calleeEnv := by
        intro v; simp only [calleeVarMap, calleeEnv]
        match h_eq : args[v]? with
        | some arg => exact hcoh arg
        | none => exact hacc_zero
      have hbound_callee : VarMapBound calleeVarMap next := by
        intro v; simp only [calleeVarMap]
        match h_eq : args[v]? with
        | some arg => exact hbound arg
        | none => exact hpoz
      have h_sync := compileWitness_compileConstrainBody_next m w j
        calleeVarMap next calleeEnv calleeObjEnv sd.constrain.body acc
      let calleeNext := (compileWitness m w j calleeVarMap next calleeEnv calleeObjEnv
        sd.constrain.body acc).2
      let calleeAcc := (compileWitness m w j calleeVarMap next calleeEnv calleeObjEnv
        sd.constrain.body acc).1
      have hle_callee : next ≤ calleeNext :=
        compileWitness_next_le m w j calleeVarMap next calleeEnv calleeObjEnv
          sd.constrain.body acc
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · -- Callee instruction: IH for callee (smaller index j < i), then transfer
        have ih_callee := preservation_body m w j calleeVarMap next
          calleeEnv calleeObjEnv sd.constrain.body acc
          hcoh_callee hbound_callee hpoz hacc_zero hcall
        have h_sat_callee := ih_callee instr hmem
        have h_vars_bounded := compileConstrainBody_instrVars_bounded m j
          calleeVarMap next sd.constrain.body hbound_callee instr hmem
        have h_congr : ∀ v ∈ instrVars instr,
            (compileWitness m w i varMap calleeNext env objEnv rest calleeAcc).1 v =
            calleeAcc v := fun v hv =>
          compileWitness_preserves_below m w i varMap calleeNext env objEnv
            rest calleeAcc v (by
              change v < (compileWitness m w j calleeVarMap next calleeEnv calleeObjEnv
                sd.constrain.body acc).2
              rw [h_sync]; exact h_vars_bounded v hv)
        exact (satisfiesInstr_congr h_congr).mpr h_sat_callee
      · -- Rest instructions: IH for rest (same i, shorter list)
        have hcoh_rest : WitnessCoherent calleeAcc varMap env :=
          witnessCoherent_after_compileWitness m w j calleeVarMap next
            calleeEnv calleeObjEnv sd.constrain.body acc varMap env hcoh hbound
        have hbound_rest : VarMapBound varMap calleeNext :=
          fun v => Nat.lt_of_lt_of_le (hbound v) hle_callee
        have hpoz_rest : 0 < calleeNext :=
          Nat.lt_of_lt_of_le hpoz hle_callee
        have hacc_zero_rest : calleeAcc 0 = 0 :=
          compileWitness_preserves_zero m w j calleeVarMap next
            calleeEnv calleeObjEnv sd.constrain.body acc hpoz hacc_zero
        have hmem' : instr ∈ (compileConstrainBody m i varMap calleeNext rest).1 := by
          change instr ∈ (compileConstrainBody m i varMap
            (compileWitness m w j calleeVarMap next calleeEnv calleeObjEnv
              sd.constrain.body acc).2 rest).1
          rw [h_sync]; exact hmem
        exact preservation_body m w i varMap calleeNext env objEnv rest calleeAcc
          hcoh_rest hbound_rest hpoz_rest hacc_zero_rest hrest instr hmem'
  termination_by (i, stmts.length)

/-! ### Core reflection lemma -/

theorem reflection_body (m : StructIR.Module n F) (w : StructIR.Witness F)
    (i : Fin n) (varMap : VarMap) (next : Nat)
    (env : LocalEnv F) (objEnv : ObjEnv)
    (stmts : List (ConstrainStmt n i F (m.structs i).members.length))
    (acc : FlatIR.VarId → F)
    (hcoh : WitnessCoherent acc varMap env)
    (hbound : VarMapBound varMap next)
    (hpoz : 0 < next) (hacc_zero : acc 0 = 0)
    (hsat : ∀ instr ∈ (compileConstrainBody m i varMap next stmts).1,
      FlatIR.satisfiesInstr
        (compileWitness m w i varMap next env objEnv stmts acc).1 instr) :
    evalConstrainBody m w i env objEnv stmts := by
  match stmts with
  | [] => simp [evalConstrainBody]
  | stmt :: rest =>
    unfold evalConstrainBody compileConstrainBody compileWitness at *
    match stmt with
    | .feltAdd dest src1 src2 =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨_, hsat_rest⟩ := hsat
      exact ⟨trivial, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 + env src2)) objEnv rest
        (fun v => if (v == next) = true then env src1 + env src2 else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat_rest⟩
    | .feltSub dest src1 src2 =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨_, hsat_rest⟩ := hsat
      exact ⟨trivial, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 - env src2)) objEnv rest
        (fun v => if (v == next) = true then env src1 - env src2 else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat_rest⟩
    | .feltMul dest src1 src2 =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨_, hsat_rest⟩ := hsat
      exact ⟨trivial, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 * env src2)) objEnv rest
        (fun v => if (v == next) = true then env src1 * env src2 else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat_rest⟩
    | .feltDiv dest src1 src2 =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      -- Extract the assignDiv instruction satisfaction
      have h_div := hsat_head (Instr.assignDiv next (varMap src1) (varMap src2))
        (by exact List.mem_cons_self)
      simp only [FlatIR.satisfiesInstr] at h_div
      obtain ⟨h_ne_zero, _⟩ := h_div
      -- Transfer h_ne_zero from compileWitness witness to env
      have hv2 : varMap src2 < next + 1 :=
        Nat.lt_of_lt_of_le (hbound src2) (Nat.le_succ _)
      rw [compileWitness_preserves_below m w i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 * (env src2)⁻¹)) objEnv rest _ (varMap src2) hv2] at h_ne_zero
      have h_ne_var : varMap src2 ≠ next := Nat.ne_of_lt (hbound src2)
      simp only [ne_eq, beq_iff_eq, h_ne_var, if_false] at h_ne_zero
      rw [hcoh src2] at h_ne_zero
      exact ⟨h_ne_zero, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (env src1 * (env src2)⁻¹)) objEnv rest
        (fun v => if (v == next) = true then env src1 * (env src2)⁻¹ else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat_rest⟩
    | .feltNeg dest src =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨_, hsat_rest⟩ := hsat
      exact ⟨trivial, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (-(env src))) objEnv rest
        (fun v => if (v == next) = true then -(env src) else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat_rest⟩
    | .feltConst dest c =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨_, hsat_rest⟩ := hsat
      exact ⟨trivial, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest c) objEnv rest
        (fun v => if (v == next) = true then c else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat_rest⟩
    | .readMember dest self member =>
      simp only at hsat ⊢
      -- No instructions emitted for readMember, instrs = []
      rw [List.nil_append] at hsat
      let objEnv' := objEnv.update dest (objEnv self ++ [member.val])
      exact ⟨trivial, reflection_body m w i (varMap.update dest next) (next + 1)
        (env.update dest (w (objEnv self, member.val))) objEnv' rest
        (fun v => if (v == next) = true then w (objEnv self, member.val) else acc v)
        (witnessCoherent_update_felt acc varMap env next dest _ hcoh hbound)
        (varMapBound_update varMap next dest hbound)
        (Nat.lt_of_lt_of_le hpoz (Nat.le_succ _))
        (by simp [show 0 ≠ next from Nat.ne_of_lt hpoz, hacc_zero]) hsat⟩
    | .constrainEq src1 src2 =>
      simp only at hsat ⊢
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_head, hsat_rest⟩ := hsat
      constructor
      · -- Need: env src1 = env src2
        have h := hsat_head (Instr.assertEq (varMap src1) (varMap src2))
          (by exact List.mem_cons_self)
        simp only [FlatIR.satisfiesInstr] at h
        rw [compileWitness_preserves_below m w i varMap next env objEnv rest acc
          (varMap src1) (hbound src1)] at h
        rw [compileWitness_preserves_below m w i varMap next env objEnv rest acc
          (varMap src2) (hbound src2)] at h
        rw [hcoh src1, hcoh src2] at h
        exact h
      · exact reflection_body m w i varMap next env objEnv rest acc
          hcoh hbound hpoz hacc_zero hsat_rest
    | .call target args =>
      simp only at hsat ⊢
      let j : Fin n := ⟨target.val, Nat.lt_trans target.isLt i.isLt⟩
      let sd := m.structs j
      let calleeEnv : LocalEnv F := fun param =>
        match args[param]? with | some arg => env arg | none => 0
      let calleeObjEnv : ObjEnv := fun param =>
        match args[param]? with | some arg => objEnv arg | none => []
      let calleeVarMap : VarMap := fun param =>
        match args[param]? with | some arg => varMap arg | none => 0
      let calleeAcc := (compileWitness m w j calleeVarMap next
        calleeEnv calleeObjEnv sd.constrain.body acc).1
      let calleeNext := (compileWitness m w j calleeVarMap next
        calleeEnv calleeObjEnv sd.constrain.body acc).2
      rw [List.forall_mem_append] at hsat
      obtain ⟨hsat_callee, hsat_rest⟩ := hsat
      have hcoh_callee : WitnessCoherent acc calleeVarMap calleeEnv := by
        intro v; simp only [calleeVarMap, calleeEnv]
        match args[v]? with
        | some arg => exact hcoh arg
        | none => exact hacc_zero
      have hbound_callee : VarMapBound calleeVarMap next := by
        intro v; simp only [calleeVarMap]
        match args[v]? with
        | some arg => exact hbound arg
        | none => exact hpoz
      have hle_callee : next ≤ calleeNext :=
        compileWitness_next_le m w j calleeVarMap next calleeEnv calleeObjEnv
          sd.constrain.body acc
      have h_sync := compileWitness_compileConstrainBody_next m w j
        calleeVarMap next calleeEnv calleeObjEnv sd.constrain.body acc
      -- Transfer hsat_callee from rest-witness to callee-witness
      have hsat_callee' : ∀ instr ∈ (compileConstrainBody m j calleeVarMap next
          sd.constrain.body).1,
          FlatIR.satisfiesInstr calleeAcc instr := by
        intro instr hmem
        have h_orig := hsat_callee instr hmem
        have h_vars := compileConstrainBody_instrVars_bounded m j calleeVarMap next
          sd.constrain.body hbound_callee instr hmem
        exact (FlatIR.satisfiesInstr_congr (fun v hv => by
          exact compileWitness_preserves_below m w i varMap calleeNext env objEnv
            rest calleeAcc v (by
              change v < (compileWitness m w j calleeVarMap next calleeEnv calleeObjEnv
                sd.constrain.body acc).2
              rw [h_sync]; exact h_vars v hv))).mp h_orig
      constructor
      · -- Callee body satisfaction: use IH for callee (smaller index j < i)
        exact reflection_body m w j calleeVarMap next calleeEnv calleeObjEnv
          sd.constrain.body acc hcoh_callee hbound_callee hpoz hacc_zero hsat_callee'
      · -- Rest satisfaction: use IH for rest (same i, shorter list)
        have hcoh_rest : WitnessCoherent calleeAcc varMap env :=
          witnessCoherent_after_compileWitness m w j calleeVarMap next
            calleeEnv calleeObjEnv sd.constrain.body acc varMap env hcoh hbound
        have hbound_rest : VarMapBound varMap calleeNext :=
          fun v => Nat.lt_of_lt_of_le (hbound v) hle_callee
        have hpoz_rest : 0 < calleeNext :=
          Nat.lt_of_lt_of_le hpoz hle_callee
        have hacc_zero_rest : calleeAcc 0 = 0 :=
          compileWitness_preserves_zero m w j calleeVarMap next
            calleeEnv calleeObjEnv sd.constrain.body acc hpoz hacc_zero
        rw [h_sync.symm] at hsat_rest
        exact reflection_body m w i varMap calleeNext env objEnv rest calleeAcc
          hcoh_rest hbound_rest hpoz_rest hacc_zero_rest hsat_rest
  termination_by (i, stmts.length)

/-! ## Pass instance -/

instance CorrectPass (n : Nat) (F : Type) [Field F] :
    PresReflPass (StructIR.Language n F) (FlatIR.Language F) where
  compile := compileProgram
  witnessRel p ws wt :=
    let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
    let mainDef := p.structs mainIdx
    let initVarMap : VarMap := fun v =>
      if v < mainDef.constrain.numParams then v else 0
    let initNext := max mainDef.constrain.numParams 1
    let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
    let varAlloc := (buildVarAlloc p mainIdx initVarMap initNext
      initObjEnv mainDef.constrain.body (fun _ => 0)).1
    ∀ vid, varAlloc vid ≠ 0 → ws vid = wt (varAlloc vid)

  preservation := by
    intro ws p hsat
    simp only [StructIR.Language, StructIR.satisfies] at hsat
    let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
    let mainDef := p.structs mainIdx
    let initVarMap : VarMap := fun v =>
      if v < mainDef.constrain.numParams then v else 0
    let initNext := max mainDef.constrain.numParams 1
    let initEnv : LocalEnv F := fun _ => 0
    let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
    let initAcc : FlatIR.VarId → F := fun _ => 0
    let wt := (compileWitness p ws mainIdx initVarMap initNext
      initEnv initObjEnv mainDef.constrain.body initAcc).1
    have hpoz : 0 < initNext := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right _ _)
    refine ⟨wt, ?witnessRel, ?sat⟩
    case witnessRel =>
      -- Peel through the let-bindings in the witnessRel definition
      intro _ _ _ _ _ _ v hv
      exact (compileWitness_varAlloc_agree p ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc (fun _ => 0)
        hpoz (fun _ h => absurd rfl h) (fun _ h => absurd rfl h)
        v hv).symm
    case sat =>
    simp only [FlatIR.Language, FlatIR.satisfies, compileProgram]
    have hcoh : WitnessCoherent initAcc initVarMap initEnv := by
      intro v; simp [initAcc, initEnv]
    have hbound : VarMapBound initVarMap initNext := by
      intro v; simp only [initVarMap, initNext]
      split
      case isTrue h => exact Nat.lt_of_lt_of_le h (le_max_left _ _)
      case isFalse => exact Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right _ _)
    have hacc_zero : initAcc 0 = 0 := rfl
    intro instr hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem_zero | hmem_body
    · -- Zero-initialization constraints: wt v = 0 for v < initNext
      simp only [List.mem_map, List.mem_range] at hmem_zero
      obtain ⟨v, hv, rfl⟩ := hmem_zero
      simp only [FlatIR.satisfiesInstr]
      exact compileWitness_preserves_below p ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc v hv
    · -- Body constraints: use preservation_body
      exact preservation_body p ws mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body initAcc
        hcoh hbound hpoz hacc_zero hsat instr hmem_body

  reflection := by
    intro wt p hsat
    let ws := extractWitness p wt
    refine ⟨ws, ?witnessRel, ?sat⟩
    case witnessRel =>
      -- ws vid = wt (varAlloc vid) is definitional since ws = extractWitness p wt
      intro _ _ _ _ _ _ v _hv
      rfl
    case sat =>
      simp only [StructIR.Language, StructIR.satisfies]
      simp only [FlatIR.Language, FlatIR.satisfies, compileProgram] at hsat
      let mainIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩
      let mainDef := p.structs mainIdx
      let initVarMap : VarMap := fun v =>
        if v < mainDef.constrain.numParams then v else 0
      let initNext := max mainDef.constrain.numParams 1
      let initEnv : LocalEnv F := fun _ => 0
      let initObjEnv : ObjEnv := ObjEnv.update (fun _ => []) 0 []
      have hpoz : 0 < initNext :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right _ _)
      -- Extract wt v = 0 for v < initNext from zero-initialization constraints
      have hwt_zero : ∀ v, v < initNext → wt v = 0 := by
        intro v hv
        have := hsat (Instr.assignConst v 0) (by
          rw [List.mem_append]; left
          simp only [List.mem_map, List.mem_range]
          exact ⟨v, hv, rfl⟩)
        simpa [FlatIR.satisfiesInstr] using this
      -- Extract body satisfaction from the compiled program
      have hsat_body : ∀ instr ∈ (compileConstrainBody p mainIdx initVarMap initNext
          mainDef.constrain.body).1, FlatIR.satisfiesInstr wt instr := by
        intro instr hmem
        exact hsat instr (by rw [List.mem_append]; right; exact hmem)
      -- Build initial coherence: env v = wt (varMap v) for all v
      have hcoh : WitnessCoherent wt initVarMap initEnv := by
        intro v; simp only [initEnv, initVarMap]
        split
        case isTrue h => exact hwt_zero v (Nat.lt_of_lt_of_le h (le_max_left _ _))
        case isFalse => exact hwt_zero 0 hpoz
      have hbound : VarMapBound initVarMap initNext := by
        intro v; simp only [initVarMap, initNext]
        split
        case isTrue h => exact Nat.lt_of_lt_of_le h (le_max_left _ _)
        case isFalse => exact hpoz
      have hnodup := p.noDupReads (Nat.zero_lt_succ n)
      -- Apply reflection_direct
      exact reflection_direct p ws wt mainIdx initVarMap initNext
        initEnv initObjEnv mainDef.constrain.body
        hcoh hbound hpoz (hwt_zero 0 hpoz) hnodup
        (fun vid hv => rfl) hsat_body

end StructIRToFlatIR
