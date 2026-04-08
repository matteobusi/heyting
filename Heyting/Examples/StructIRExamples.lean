import Mathlib.Algebra.Field.ZMod
import Heyting.Languages.StructIR
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.FlatIRToR1CS

/-!
# StructIR Examples

Encoding of LLZK test cases to validate the StructIR representation
with intrinsic well-formedness, and demonstrate the full compilation
pipeline StructIR → FlatIR → R1CS.

## Field

All examples use `ZMod 1993` (a prime field).
-/

-- Suppress linter noise in example proofs (repeated unfold/simp patterns)
section
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.style.nativeDecide false

namespace StructIR.Examples

open StructIR

def p : ℕ := 1993
instance hp : Fact (Nat.Prime p) := ⟨by native_decide⟩
abbrev F := ZMod p

/-!
## Example 1: Single Component (equality constraints)

Corresponds to LLZK `Component1A`:
```
struct.def @Component1A {
  struct.member @f1 : !felt.type
  struct.member @f2 : !felt.type

  function.def @constrain(%self, %z) {
    %a = struct.readm %self[@f1]
    constrain.eq %a, %z
    %b = struct.readm %self[@f2]
    constrain.eq %b, %z
  }
}
```

Module has 1 struct. Component1A is at index 0 (the only and main struct).
Members f1 and f2 are indexed as `Fin 2`: ⟨0, _⟩ and ⟨1, _⟩.
-/

def component1A :
    StructDef 1 ⟨0, Nat.zero_lt_one⟩ F where
  name := "Component1A"
  members := [
    { name := "f1", type := .felt },
    { name := "f2", type := .felt }
  ]
  compute := {
    numParams := 1
    body := [
      .newStruct 1,
      .writeMember 1 ⟨0, by simp⟩ 0,
      .writeMember 1 ⟨1, by simp⟩ 0
    ]
    returnVar := 1
  }
  constrain := {
    -- @constrain(%self, %z)
    -- %0 = %self, %1 = %z, %2 = readm f1, %3 = readm f2
    numParams := 2
    body := [
      .readMember 2 0 ⟨0, by simp⟩,  -- %2 = readm %self[@f1]
      .constrainEq 2 1,                 -- constrain.eq %2, %1
      .readMember 3 0 ⟨1, by simp⟩,  -- %3 = readm %self[@f2]
      .constrainEq 3 1                  -- constrain.eq %3, %1
    ]
  }

-- Read positions: [([], 0), ([], 1)] — distinct
def module1A : Module 1 F where
  structs := fun ⟨0, _⟩ => component1A
  noDupReads := by
    intro _
    show (readPositions _ ⟨0, _⟩ _ _).Nodup
    unfold readPositions; simp [component1A, ObjEnv.update]
    unfold readPositions; simp [component1A, ObjEnv.update]
    unfold readPositions; simp [component1A, ObjEnv.update]
    unfold readPositions; simp [component1A, ObjEnv.update]
    unfold readPositions; simp

/-!
### Compilation: StructIR → FlatIR

The output includes:
- A **zero-initialization prefix** (`assignConst v 0` for param positions)
- **`assertEq`** constraints from `constrainEq` statements

`readMember` emits no FlatIR instruction — the witness handles value
injection. Vars 2 and 3 (allocated by `readMember`) appear as operands
in `assertEq`.
-/

-- StructIR → FlatIR:
--   assignConst 0 0    ← zero-init for %self (param 0)
--   assignConst 1 0    ← zero-init for %z (param 1)
--   assertEq 2 1       ← constrain.eq %f1, %z
--   assertEq 3 1       ← constrain.eq %f2, %z
#eval StructIRToFlatIR.compileProgram module1A

/-!
### Compilation: FlatIR → R1CS

Each FlatIR instruction compiles to R1CS constraints `A * B = C`:
- `assignConst v 0` → `0 * 1 = v` (forces `v = 0`)
- `assertEq a b` → `a * 1 = b` (forces `a = b`)
-/

-- Full pipeline: StructIR → FlatIR → R1CS
#eval FlatIRToR1CS.compileProgram F
  (StructIRToFlatIR.compileProgram module1A)

/-!
### Satisfaction

The parameter `%z` is initialized to 0 (all locals start at 0), so the
constraints reduce to `w([], 0) = 0 ∧ w([], 1) = 0`.
-/

-- The zero witness satisfies module1A
example : satisfies (fun _ => (0 : F)) module1A := by
  simp only [satisfies, module1A, component1A]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])

-- 42 ≠ 0 in F_1993, so this fails
example : ¬ satisfies (fun _ => (42 : F)) module1A := by
  simp only [satisfies, module1A, component1A, not_and, not_forall]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])
  native_decide

/-!
## Example 2: Felt arithmetic (addition constraint)

A struct that computes `sum = a + b` and constrains `sum = c`.

```
struct.def @Adder {
  struct.member @a : !felt.type
  struct.member @b : !felt.type
  struct.member @c : !felt.type

  function.def @constrain(%self) {
    %a = struct.readm %self[@a]
    %b = struct.readm %self[@b]
    %sum = felt.add %a, %b
    %c = struct.readm %self[@c]
    constrain.eq %sum, %c
  }
}
```
-/

def adder : StructDef 1 ⟨0, Nat.zero_lt_one⟩ F where
  name := "Adder"
  members := [
    { name := "a", type := .felt },
    { name := "b", type := .felt },
    { name := "c", type := .felt }
  ]
  compute := { numParams := 0, body := [], returnVar := 0 }
  constrain := {
    numParams := 1
    body := [
      .readMember 1 0 ⟨0, by simp⟩,  -- %1 = readm %self[@a]
      .readMember 2 0 ⟨1, by simp⟩,  -- %2 = readm %self[@b]
      .feltAdd 3 1 2,                   -- %3 = %1 + %2
      .readMember 4 0 ⟨2, by simp⟩,  -- %4 = readm %self[@c]
      .constrainEq 3 4                  -- constrain.eq %3, %4
    ]
  }

-- Read positions: [([], 0), ([], 1), ([], 2)] — distinct
def moduleAdder : Module 1 F where
  structs := fun ⟨0, _⟩ => adder
  noDupReads := by
    intro _
    show (readPositions _ ⟨0, _⟩ _ _).Nodup
    unfold readPositions; simp [adder, ObjEnv.update]
    unfold readPositions; simp [adder, ObjEnv.update]
    unfold readPositions; simp [adder, ObjEnv.update]
    unfold readPositions; simp [adder, ObjEnv.update]
    unfold readPositions; simp [adder, ObjEnv.update]
    unfold readPositions; simp

/-!
### Compilation

The `feltAdd` generates an `assignAdd` instruction. The `constrainEq`
generates an `assertEq`.
-/

-- StructIR → FlatIR:
--   assignConst 0 0    ← zero-init for %self
--   assignAdd 3 1 2    ← %3 = %a + %b (var 1 = readm @a, var 2 = readm @b)
--   assertEq 3 4       ← constrain.eq %sum, %c (var 4 = readm @c)
#eval StructIRToFlatIR.compileProgram moduleAdder

-- Full pipeline: StructIR → FlatIR → R1CS
-- The `assignAdd` becomes `(var 1 + var 2) * 1 = var 3`
-- The `assertEq` becomes `var 3 * 1 = var 4`
#eval FlatIRToR1CS.compileProgram F
  (StructIRToFlatIR.compileProgram moduleAdder)

/-!
### Satisfaction
-/

-- Witness: a=3, b=5, c=8 satisfies (3 + 5 = 8)
example : satisfies (fun (_, idx) =>
    match idx with | 0 => (3 : F) | 1 => 5 | 2 => 8 | _ => 0)
    moduleAdder := by
  simp only [satisfies, moduleAdder, adder]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])
  native_decide

-- Witness: a=3, b=5, c=9 does NOT satisfy (3 + 5 ≠ 9)
example : ¬ satisfies (fun (_, idx) =>
    match idx with | 0 => (3 : F) | 1 => 5 | 2 => 9 | _ => 0)
    moduleAdder := by
  simp only [satisfies, moduleAdder, adder, not_and, not_forall]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])
  native_decide

/-!
## Example 3: Division and non-zero constraint

A struct constraining `a / b = c` (with `b ≠ 0`).

```
struct.def @Divider {
  struct.member @a : !felt.type
  struct.member @b : !felt.type
  struct.member @c : !felt.type

  function.def @constrain(%self) {
    %a = struct.readm %self[@a]
    %b = struct.readm %self[@b]
    %q = felt.div %a, %b
    %c = struct.readm %self[@c]
    constrain.eq %q, %c
  }
}
```
-/

def divider : StructDef 1 ⟨0, Nat.zero_lt_one⟩ F where
  name := "Divider"
  members := [
    { name := "a", type := .felt },
    { name := "b", type := .felt },
    { name := "c", type := .felt }
  ]
  compute := { numParams := 0, body := [], returnVar := 0 }
  constrain := {
    numParams := 1
    body := [
      .readMember 1 0 ⟨0, by simp⟩,  -- %1 = readm @a
      .readMember 2 0 ⟨1, by simp⟩,  -- %2 = readm @b
      .feltDiv 3 1 2,                   -- %3 = %1 / %2
      .readMember 4 0 ⟨2, by simp⟩,  -- %4 = readm @c
      .constrainEq 3 4                  -- constrain.eq %3, %4
    ]
  }

def moduleDivider : Module 1 F where
  structs := fun ⟨0, _⟩ => divider
  noDupReads := by
    intro _
    show (readPositions _ ⟨0, _⟩ _ _).Nodup
    unfold readPositions; simp [divider, ObjEnv.update]
    unfold readPositions; simp [divider, ObjEnv.update]
    unfold readPositions; simp [divider, ObjEnv.update]
    unfold readPositions; simp [divider, ObjEnv.update]
    unfold readPositions; simp [divider, ObjEnv.update]
    unfold readPositions; simp

/-!
### Compilation

`feltDiv` generates two R1CS constraints:
1. `src2 * dest = src1` (the division)
2. `src2 * aux = 1` (forces `src2 ≠ 0`)
-/

-- StructIR → FlatIR
#eval StructIRToFlatIR.compileProgram moduleDivider

-- Full pipeline — note: assignDiv produces 2 R1CS constraints
#eval FlatIRToR1CS.compileProgram F
  (StructIRToFlatIR.compileProgram moduleDivider)

/-!
### Satisfaction
-/

-- Witness: a=10, b=2, c=5 satisfies (10 / 2 = 5)
example : satisfies (fun (_, idx) =>
    match idx with | 0 => (10 : F) | 1 => 2 | 2 => 5 | _ => 0)
    moduleDivider := by
  simp only [satisfies, moduleDivider, divider]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])
  constructor
  · native_decide
  · native_decide

/-!
## Example 4: Nested struct (cross-component call)

A wrapper struct that holds a `Component1A` instance and delegates
constraint checking to it.

```
struct.def @Component1A {    -- index 0
  struct.member @f1 : !felt.type
  struct.member @f2 : !felt.type

  function.def @constrain(%self) {
    %a = struct.readm %self[@f1]
    %b = struct.readm %self[@f2]
    constrain.eq %a, %b
  }
}

struct.def @Wrapper {        -- index 1
  struct.member @inner : !struct.type<@Component1A>

  function.def @constrain(%self) {
    %inner = struct.readm %self[@inner]
    call @Component1A::@constrain(%inner)
  }
}
```

Module has 2 structs. Component1A at index 0, Wrapper at index 1 (main).
After `readMember`, `objEnv[1] = [0]`, so the callee reads from path `[0]`.
-/

-- Component1A: constrains f1 = f2
def component1A_nested :
    StructDef 2 ⟨0, by omega⟩ F where
  name := "Component1A"
  members := [
    { name := "f1", type := .felt },
    { name := "f2", type := .felt }
  ]
  compute := { numParams := 0, body := [], returnVar := 0 }
  constrain := {
    -- @constrain(%self)
    -- %0 = %self, %1 = readm f1, %2 = readm f2
    numParams := 1
    body := [
      .readMember 1 0 ⟨0, by simp⟩,  -- %1 = readm %self[@f1]
      .readMember 2 0 ⟨1, by simp⟩,  -- %2 = readm %self[@f2]
      .constrainEq 1 2                  -- constrain.eq %1, %2
    ]
  }

-- Wrapper: holds a Component1A and calls its constrain
def wrapper : StructDef 2 ⟨1, by omega⟩ F where
  name := "Wrapper"
  members := [
    { name := "inner", type := .substruct ⟨0, by omega⟩ }
  ]
  compute := { numParams := 0, body := [], returnVar := 0 }
  constrain := {
    -- @constrain(%self)
    -- %0 = %self, %1 = readm @inner
    numParams := 1
    body := [
      .readMember 1 0 ⟨0, by simp⟩,         -- %1 = readm %self[@inner]
      .call ⟨0, Nat.zero_lt_one⟩ [1]             -- call @Component1A::@constrain(%1)
    ]
  }

-- Read positions: after readMember, objEnv[1] = [0].
-- Call passes args=[1], so callee objEnv[0] = [0].
-- Callee reads ([0], 0) and ([0], 1) — distinct.
def moduleNested : Module 2 F where
  structs := fun
    | ⟨0, _⟩ => component1A_nested
    | ⟨1, _⟩ => wrapper
  noDupReads := by
    intro _
    show (readPositions _ ⟨1, _⟩ _ _).Nodup
    simp only [wrapper]
    unfold readPositions; dsimp only; simp only [ObjEnv.update, beq_iff_eq, List.nil_append]
    unfold readPositions; dsimp only; simp [ObjEnv.update, component1A_nested]
    unfold readPositions; dsimp only; simp [ObjEnv.update, component1A_nested]
    unfold readPositions; dsimp only; simp [ObjEnv.update, component1A_nested]
    unfold readPositions; simp
    unfold readPositions; simp

/-!
### Compilation
-/

-- StructIR → FlatIR
#eval StructIRToFlatIR.compileProgram moduleNested

-- Full pipeline: StructIR → FlatIR → R1CS
#eval FlatIRToR1CS.compileProgram F
  (StructIRToFlatIR.compileProgram moduleNested)

/-!
### Satisfaction

The witness maps `([0], 0) ↦ 7` and `([0], 1) ↦ 7` (f1 = f2 = 7 in the
nested Component1A instance).
-/

-- Witness: inner.f1 = inner.f2 = 7 satisfies Wrapper
example : satisfies (fun (path, idx) =>
    match path, idx with
    | [0], 0 => (7 : F)
    | [0], 1 => 7
    | _, _ => 0)
    moduleNested := by
  simp only [satisfies, moduleNested, wrapper, component1A_nested]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])

-- Witness: inner.f1 = 3, inner.f2 = 5 does NOT satisfy (3 ≠ 5)
example : ¬ satisfies (fun (path, idx) =>
    match path, idx with
    | [0], 0 => (3 : F)
    | [0], 1 => 5
    | _, _ => 0)
    moduleNested := by
  simp only [satisfies, moduleNested, wrapper, component1A_nested]
  repeat (unfold evalConstrainBody; simp [LocalEnv.update, ObjEnv.update])
  intro h
  have : (3 : F) = 5 := h
  revert this; native_decide

end StructIR.Examples
end -- section
