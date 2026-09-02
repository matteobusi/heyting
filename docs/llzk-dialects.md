# LLZK Dialect Reference

Reference for the [LLZK](https://github.com/project-llzk/llzk-lib) MLIR dialect system,
as it relates to Heyting's formalization targets.

## Dialect Tiers

### Tier 1 — Foundational (appear in every non-trivial program)

| Dialect | Namespace | Purpose |
|---------|-----------|---------|
| `felt` | `::llzk::felt` | Field element type and arithmetic |
| `constrain` | `::llzk::constrain` | Constraint emission |
| `struct` | `::llzk::component` | Circuit component definitions |
| `function` | `::llzk::function` | Function definitions, calls, returns |
| `llzk` | `::llzk` | Common attributes (`pub`, `nondet`, `main`) |

### Tier 2 — Higher-level (removable by lowering passes)

| Dialect | Purpose |
|---------|---------|
| `array` | N-dimensional arrays |
| `include` | File inclusion (inlineable) |
| `poly` | Polymorphism / type variables |
| `pod` | Plain-old-data structs |

### Tier 3 — Specialized

| Dialect | Purpose |
|---------|---------|
| `bool` | Boolean logic + comparisons |
| `cast` | `felt` <-> `index`/`i1` conversions |
| `global` | Global constants and variables |
| `string` | String literals |

### Backend Dialects

| Dialect | Purpose |
|---------|---------|
| `r1cs` | R1CS constraint system representation |
| `zkbuilder` | ZKLean constraint builder state |
| `zkexpr` | ZKLean ZK expressions |
| `zkleanlean` | ZKLean/Lean specific ops |

MLIR builtins also used: `arith` (integer arithmetic) and `scf` (structured control flow).

---

## Detailed Dialect Definitions

### `felt` — Field Arithmetic

**Types:**
- `!felt.type` — unspecified field element
- `!felt.type<"bn254">` — field element in a named field (babybear, bn128/bn254, goldilocks, koalabear, mersenne31)

**Attributes:**
- `felt.const N` — field element constant
- `felt.field<name, prime>` — field specification for user-defined fields

**Field-native operations (valid everywhere):**
| Op | Signature | Notes |
|----|-----------|-------|
| `felt.const` | `() -> !felt.type` | Constant |
| `felt.add` | `(!felt.type, !felt.type) -> !felt.type` | Commutative |
| `felt.sub` | `(!felt.type, !felt.type) -> !felt.type` | |
| `felt.mul` | `(!felt.type, !felt.type) -> !felt.type` | Commutative |
| `felt.div` | `(!felt.type, !felt.type) -> !felt.type` | Field division (multiply by inverse) |
| `felt.neg` | `(!felt.type) -> !felt.type` | Additive inverse |

**Non-field-native operations (require `allow_non_native_field_ops`):**
| Op | Notes |
|----|-------|
| `felt.pow` | Exponentiation |
| `felt.inv` | Multiplicative inverse |
| `felt.uintdiv`, `felt.sintdiv` | Integer division |
| `felt.umod`, `felt.smod` | Modular arithmetic |
| `felt.bit_and`, `felt.bit_or`, `felt.bit_xor` | Bitwise |
| `felt.shl`, `felt.shr` | Shifts |
| `felt.bit_not` | Bitwise NOT |

### `constrain` — Constraint Emission

| Op | Signature | Notes |
|----|-----------|-------|
| `constrain.eq` | `(!felt.type, !felt.type) -> ()` | Equality constraint (commutative) |
| `constrain.in` | `(!array.type, !T) -> ()` | Containment constraint |

Both carry the `ConstraintGen` trait — only valid in `@constrain` functions.

### `struct` — Circuit Components

**Types:**
- `!struct.type<@Name>` — reference to a struct definition
- `!struct.type<@Name<[params...]>>` — parametric struct

**Operations:**
| Op | Notes |
|----|-------|
| `struct.def @Name { ... }` | Defines a component (contains `@compute` and `@constrain` functions) |
| `struct.member @name : type` | Member declaration. Attrs: `{llzk.pub}`, `{column}`, `{signal}` |
| `struct.new` | Create instance (`WitnessGen`) |
| `struct.readm %s[@member]` | Read member value |
| `struct.writem %s[@member] = %v` | Write member value (`WitnessGen`) |

### `function` — Functions

| Op | Notes |
|----|-------|
| `function.def @name(%args) -> results { body }` | Function definition |
| `function.return %values` | Return |
| `function.call @Struct::@func(%args)` | Fully-qualified call |

**Special functions:** `@compute` (has `allow_witness`), `@constrain` (has `allow_constraint`).

**Op traits:**
- `WitnessGen` — only valid in `@compute` or `allow_witness` functions
- `ConstraintGen` — only valid in `@constrain` or `allow_constraint` functions
- `NotFieldNative` — needs `allow_non_native_field_ops`

### `array` — Arrays

**Types:**
- `!array.type<D1,D2,...,Dn x ElemType>` — N-dimensional array

| Op | Notes |
|----|-------|
| `array.new` | Create array |
| `array.read %arr[%i]` | Read element |
| `array.write %arr[%i] = %v` | Write element |
| `array.extract %arr[%i,%j]` | Extract sub-array |
| `array.insert %arr[%i] = %sub` | Insert sub-array |
| `array.len %arr, %dim` | Get dimension size |

### `poly` — Polymorphism

**Types:**
- `!poly.tvar<@Name>` — type variable

| Op | Notes |
|----|-------|
| `poly.read_const @Param` | Read template parameter |
| `poly.unifiable_cast %v` | Cast between unifiable types |
| `poly.applymap` | Apply AffineMap to indices |

### `bool` — Boolean Logic

All ops carry `NotFieldNative` trait.

| Op | Notes |
|----|-------|
| `bool.and`, `bool.or`, `bool.xor` | Binary on `i1` |
| `bool.not` | Unary NOT |
| `bool.cmp pred(%a, %b)` | Compare felt values (eq/ne/lt/le/gt/ge) |
| `bool.assert %cond` | Static assertion |

### `cast`, `global`, `pod`, `include`, `string`

- `cast.tofelt` / `cast.toindex` — type conversions
- `global.def` / `global.read` / `global.write` — global variables
- `pod.new` / `pod.read` / `pod.write` — structural records
- `include.from "path" as @alias` — file inclusion
- `string.new "literal"` — string constants

---

## R1CS Backend

| Op | Notes |
|----|-------|
| `r1cs.circuit @Name inputs (...)` | Circuit definition |
| `r1cs.def <label> : !r1cs.signal` | Define a signal/wire |
| `r1cs.to_linear` | Signal to linear expression |
| `r1cs.const` | Constant linear value |
| `r1cs.add`, `r1cs.mul_const`, `r1cs.neg` | Linear algebra |
| `r1cs.constrain %a, %b, %c` | Enforce `a * b - c = 0` |

---

## Key Semantic Invariants

1. Every struct has a `@compute` (witness gen) and `@constrain` (constraint gen) function
2. `WitnessGen` ops only in `@compute`, `ConstraintGen` ops only in `@constrain`
3. `NotFieldNative` ops need explicit opt-in
4. Modules have `llzk.lang` and `llzk.main` root attributes
5. All symbol references are fully qualified from the root

---

## Mapping to Heyting

| LLZK Concept | Current Heyting | Status |
|--------------|-----------------|--------|
| `felt.add/sub/mul/div/neg/inv/const` | `Dialect.Felt` → `R1CSLike` | Done |
| `constrain.eq` | `Dialect.ConstrainEq` | Done |
| `struct.def` / `struct.member` | `Dialect.Module` / `MemberDecl` | Done |
| `struct.readm` | `Dialect.StructObject.readMember` | Done |
| `struct.writem` | `Dialect.StructObject.writeMember` | Done (compute only) |
| `struct.new` | `Dialect.StructObject.newStruct` | Done (compute only) |
| `function.def` | typed `compute` / `constrain` fields | Done, one pair per struct |
| `function.call` | `Dialect.Call.call` | Done, selector 0 and decreasing targets |
| `llzk.nondet` | `Dialect.Oracle.next` | Done (compute only) |
| `llzk.pub` member attribute | typed `MemberDecl.isPublic` | Done |
| `array.*` | — | Planned |
| R1CS backend | `R1CS.lean` | Done (core) |
| Typed dialect → R1CS artifact | `DialectPipeline.lean` | Done (certified boundary) |
| FlatIR → R1CS pass | `FlatIRToR1CS.lean` | Done (fully verified) |
