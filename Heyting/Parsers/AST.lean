/-!
# LLZK AST — Untyped Parse Tree

Lightweight AST for the subset of LLZK MLIR textual IR that maps to
`StructIR.Module`. This is the output of parsing and the input to lowering.

The AST is deliberately untyped: names are strings, variables are strings,
indices are not yet `Fin`. The lowering pass (`Lowering.lean`) resolves
names, assigns indices, and constructs the dependently-typed `StructIR.Module`.

## Supported constructs

- `module` (with optional attributes)
- `struct.def` with members and compute/constrain functions
- `function.def` / `function.return` / `function.call`
- `struct.new` / `struct.readm` / `struct.writem`
- Felt operations: `felt.add`, `felt.sub`, `felt.mul`, `felt.div`,
  `felt.neg`, `felt.const`, `felt.inv`
- `constrain.eq`
- `llzk.nondet`

## Unsupported (rejected with error)

Templates/generics, arrays, scf.for/if/while, pod types, poly.read_const,
include.from, affine_maps, booleans, strings, arith ops.
-/

namespace LLZK

/-! ## Source position tracking -/

/-- Source position for error reporting. -/
structure Pos where
  line : Nat
  col  : Nat
  deriving Repr, Inhabited

instance : ToString Pos where
  toString p := s!"{p.line}:{p.col}"

/-! ## Types -/

/-- LLZK type as parsed. We only need to distinguish `!felt.type` and
`!struct.type<@Name>` for lowering; everything else is rejected. -/
inductive Ty where
  | felt : Ty
  | structTy : String → Ty   -- `!struct.type<@Name>`
  | other : String → Ty      -- catch-all for unsupported types (used in error messages)
  deriving Repr, Inhabited

/-! ## Statements -/

/-- An SSA value reference: `%name`. -/
abbrev SSAName := String

/-- A symbol reference: `@name`. -/
abbrev SymName := String

/-- A statement in a function body. -/
inductive Stmt where
  -- Felt arithmetic: `%dest = felt.add %a, %b`
  | feltAdd (pos : Pos) (dest : SSAName) (src1 src2 : SSAName)
  | feltSub (pos : Pos) (dest : SSAName) (src1 src2 : SSAName)
  | feltMul (pos : Pos) (dest : SSAName) (src1 src2 : SSAName)
  | feltDiv (pos : Pos) (dest : SSAName) (src1 src2 : SSAName)
  -- Felt unary: `%dest = felt.neg %src`
  | feltNeg (pos : Pos) (dest : SSAName) (src : SSAName)
  -- Felt inverse: `%dest = felt.inv %src` (lowered to feltDiv: 1 / src)
  | feltInv (pos : Pos) (dest : SSAName) (src : SSAName)
  -- Felt constant: `%dest = felt.const <value>`
  | feltConst (pos : Pos) (dest : SSAName) (value : Int)
  -- Struct operations
  | structNew (pos : Pos) (dest : SSAName) (structName : SymName)
  | readMember (pos : Pos) (dest : SSAName) (self : SSAName) (member : SymName)
  | writeMember (pos : Pos) (self : SSAName) (member : SymName) (src : SSAName)
  -- Constraint: `constrain.eq %a, %b : !felt.type`
  | constrainEq (pos : Pos) (src1 src2 : SSAName)
  -- Function call: `%dest = function.call @Struct::@func(%args) : ...`
  | call (pos : Pos) (dest : Option SSAName) (target : SymName)
         (args : List SSAName)
  -- Function return: `function.return %v` or `function.return`
  | funcReturn (pos : Pos) (retVal : Option SSAName)
  -- Nondet: `%dest = llzk.nondet : !felt.type`
  | nondet (pos : Pos) (dest : SSAName)
  -- Skipped/unsupported (parsed but ignored during lowering)
  | skipped (pos : Pos) (opName : String)
  deriving Repr

/-! ## Function and struct declarations -/

/-- Parsed parameter declaration: `%name : !type`. -/
structure ParamDecl where
  name : SSAName
  ty   : Ty
  deriving Repr

/-- Parsed function definition before lowering resolves names and indices. -/
structure FuncDef where
  name       : SymName            -- e.g., "compute" or "constrain"
  params     : List ParamDecl
  returnType : Option Ty          -- None for void functions
  body       : List Stmt
  pos        : Pos
  deriving Repr

/-- Parsed struct member declaration: `struct.member @name : !type {llzk.pub}?`. -/
structure MemberDecl where
  name     : SymName
  ty       : Ty
  isPublic : Bool     -- true iff `{llzk.pub}` attribute was present
  pos      : Pos
  deriving Repr

/-- Parsed struct definition consisting of members and function bodies. -/
structure StructDef where
  name     : SymName
  members  : List MemberDecl
  funcs    : List FuncDef
  pos      : Pos
  deriving Repr

/-- Parsed top-level module containing struct definitions. -/
structure Module where
  structs : List StructDef
  pos     : Pos
  deriving Repr

end LLZK
