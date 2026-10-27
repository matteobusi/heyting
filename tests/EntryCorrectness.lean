import Heyting.Passes.DialectPipeline
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Executable whole-entry correctness checks

Concrete LLZK ASTs are pushed through the real frontend (`lowerFull`) and the certified
entry compiler over the small field `ZMod 7`. Every finite source observation is then
enumerated, so the checks below compare three independent judges on all of them:

* a hand-written arithmetic oracle (`expected`),
* the typed-source checker (`checkTypedSource`), and
* the compiled R1CS evaluated on the witness produced by the executable `forward`.

Each family also asserts a non-vacuity count, so a bug that makes every judge reject (or
`forward` fail) cannot pass silently. The theorems `typed_entry_correct` and
`typed_source_forward_total` say these agreements hold in general; these checks exercise
the concrete code paths the theorems are about, including the failure modes.
-/

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace Dialect.Pipeline.EntryTests

abbrev F := ZMod 7

/-! ## AST helpers -/

def pos : LLZK.Pos := { line := 1, col := 1 }
def feltParam (name : String) : LLZK.ParamDecl := { name, ty := .felt }
def selfParam (structName : String) : LLZK.ParamDecl :=
  { name := "self", ty := .structTy structName }

/-- Constrain function: `self` first, then the felt inputs, as LLZK lays them out. -/
def constrainFn (structName : String) (inputs : List String) (body : List LLZK.Stmt) :
    LLZK.FuncDef where
  name := "constrain"
  params := selfParam structName :: inputs.map feltParam
  returnType := none
  body := body ++ [.funcReturn pos none]
  pos

/-- Compute function that only allocates and returns the object. -/
def computeFn (structName : String) (inputs : List String) (body : List LLZK.Stmt := []) :
    LLZK.FuncDef where
  name := "compute"
  params := inputs.map feltParam
  returnType := some (.structTy structName)
  body := [.structNew pos "self" structName] ++ body ++ [.funcReturn pos (some "self")]
  pos

def member (name : String) : LLZK.MemberDecl := { name, ty := .felt, isPublic := true, pos }

def mkModule (structs : List LLZK.StructDef) : LLZK.Module :=
  { structs, freeFuncs := [], pos }

def mkStruct (name : String) (members : List LLZK.MemberDecl) (funcs : List LLZK.FuncDef) :
    LLZK.StructDef :=
  { name, members, funcs, pos }

/-! ## Fixtures -/

/-- `a * b = 6`. Two inputs, no members; `self` occupies one reserved slot. -/
def product : LLZK.Module := mkModule [mkStruct "Main" []
  [computeFn "Main" ["a", "b"], constrainFn "Main" ["a", "b"] [
    .feltMul pos "p" "a" "b", .feltConst pos "six" 6, .constrainEq pos "p" "six"]]]

def productExpected (a b : F) : Bool := a * b == 6

/-- `a / b = 3`. Division by zero must be a fault, never a satisfying witness. -/
def quotient : LLZK.Module := mkModule [mkStruct "Main" []
  [computeFn "Main" ["a", "b"], constrainFn "Main" ["a", "b"] [
    .feltDiv pos "q" "a" "b", .feltConst pos "three" 3, .constrainEq pos "q" "three"]]]

def quotientExpected (a b : F) : Bool := b != 0 && a / b == 3

/-- The member records the input; the constraint reads the member back. One object slot. -/
def stored : LLZK.Module := mkModule [mkStruct "Main" [member "value"]
  [computeFn "Main" ["x"] [.writeMember pos "self" "value" "x"],
   constrainFn "Main" ["x"] [.readMember pos "actual" "self" "value",
     .feltConst pos "one" 1, .feltAdd pos "expected" "x" "one",
     .constrainEq pos "actual" "expected"]]]

/-- Observation `(x, value)` satisfies `value = x + 1`. -/
def storedExpected (x v : F) : Bool := v == x + 1

/-- Root delegates to its Leaf member, which asserts `x = 1`; the call is inlined. -/
def called : LLZK.Module := mkModule [
  mkStruct "Root" [{ name := "leaf", ty := .structTy "Leaf", isPublic := false, pos }]
    [computeFn "Root" ["x"], constrainFn "Root" ["x"] [
      .readMember pos "leaf" "self" "leaf",
      .call pos none "Leaf::constrain" ["leaf", "x"]]],
  mkStruct "Leaf" [] [computeFn "Leaf" ["x"], constrainFn "Leaf" ["x"] [
    .feltConst pos "one" 1, .constrainEq pos "x" "one"]]]

def calledExpected (x : F) : Bool := x == 1

/-! ## Harness -/

/-- Lower, certify and compile, then run `f` on the resulting evidence. -/
def withCompiled {α : Type} (ast : LLZK.Module)
    (f : ∀ {k : Nat} (m : Dialect.Module LLZK.DialectLowering.WitnessSourceSet (k + 1) F),
      TypedEntryCompilationArtifact m ⟨k, Nat.lt_succ_self k⟩ → α) : Except String α := do
  let ⟨k, m⟩ ← LLZK.DialectLowering.lowerFull (F := F) ast
  let compiled ← compileTypedEntryArtifact m ⟨k, Nat.lt_succ_self k⟩
  pure (f m compiled)

/-- Bool form of `R1CS.satisfies` (including the `varOne = 1` invariant). -/
def holds (system : R1CS.System F) (w : R1CS.Witness F) : Bool :=
  w .varOne == 1 && system.constraints.all fun c ↦
    decide (R1CS.evalLinComb w c.A * R1CS.evalLinComb w c.B = R1CS.evalLinComb w c.C)

def elems : List F := (List.range 7).map fun n ↦ (n : F)

def wireIs (v : Nat) : R1CS.VarId → Bool
  | .var u => u == v
  | _ => false

def bump (w : R1CS.Witness F) (v : Nat) (delta : F) : R1CS.Witness F :=
  fun x ↦ if wireIs v x then w x + delta else w x

/-- Outcome of the executable path on one observation: whether `forward` succeeded, whether
the typed checker accepts, whether the compiled R1CS accepts the forwarded witness, and
whether readback is exact. -/
structure Outcome where
  forwarded : Bool
  typed : Bool
  targetOk : Bool
  roundTrip : Bool
  deriving Repr, DecidableEq

def outcome (ast : LLZK.Module) (source : SourceWitness F) : Option Outcome :=
  (withCompiled ast fun m compiled ↦
    let typed := checkTypedSource m ⟨_, Nat.lt_succ_self _⟩ source
    match compiled.artifact.forward source with
    | .error _ => Outcome.mk false typed false false
    | .ok target =>
      Outcome.mk true typed (holds compiled.artifact.target target)
        (compiled.artifact.readback target == source)).toOption

/-- All observations `inputs ++ objects` from the given finite grids. -/
def grid2 (objects : List (List F)) : List (SourceWitness F) :=
  (elems.flatMap fun a ↦ elems.flatMap fun b ↦ objects.map fun o ↦
    { inputs := [a, b], objects := o })

def grid1 (objects : List (List F)) : List (SourceWitness F) :=
  elems.flatMap fun a ↦ objects.map fun o ↦ { inputs := [a], objects := o }

/-- Every observation: `forward` succeeds, the R1CS agrees with the typed checker and the
arithmetic oracle, and readback is exact. Also returns how many were satisfying. -/
def sweep (ast : LLZK.Module) (sources : List (SourceWitness F))
    (expected : SourceWitness F → Bool) : Option (Bool × Nat) :=
  sources.foldlM (init := (true, 0)) fun (ok, count) s ↦ do
    let o ← outcome ast s
    let good := o.forwarded && o.roundTrip && o.typed == expected s && o.targetOk == expected s
    pure (ok && good, count + if expected s then 1 else 0)

/-! ## Agreement on every observation -/

-- 6 = a * b has exactly one solution b for each nonzero a in ZMod 7.
#guard sweep product (grid2 [[]]) (fun s ↦ productExpected s.inputs[0]! s.inputs[1]!)
  == some (true, 6)

-- One satisfying object value `x + 1` per input.
#guard sweep stored (grid1 [[0], [1], [2], [3], [4], [5], [6]])
  (fun s ↦ storedExpected s.inputs[0]! s.objects[0]!) == some (true, 7)

-- The `leaf` member occupies one unconstrained object slot: x = 1 with any slot value.
#guard sweep called (grid1 (elems.map ([·]))) (fun s ↦ calledExpected s.inputs[0]!)
  == some (true, 7)

/-! ## Division faults

A zero divisor is a transport fault, not a satisfying witness; nonzero divisors behave as
usual. In no case may the typed checker accept while `forward` fails. -/

def quotientOutcomes : Option (List Outcome) :=
  (grid2 [[]]).mapM (outcome quotient)

#guard (quotientOutcomes.map fun os ↦
    os.all fun o ↦ !o.forwarded → !o.typed) == some true
#guard (quotientOutcomes.map fun os ↦
    (os.filter fun o ↦ o.forwarded).all fun o ↦ o.targetOk == o.typed && o.roundTrip)
  == some true
-- Only the seven pairs with b = 0 fault.
#guard (quotientOutcomes.map fun os ↦ (os.filter fun o ↦ !o.forwarded).length) == some 7
-- a / b = 3 has one solution per nonzero b.
#guard (quotientOutcomes.map fun os ↦ (os.filter fun o ↦ o.typed).length) == some 6
#guard ((grid2 [[]]).all fun s ↦
  (outcome quotient s).map (·.typed) == some (quotientExpected s.inputs[0]! s.inputs[1]!))

/-! ## Reserved-slot and wire tampering -/

/-- The honest R1CS witness for one observation, with its system, if everything succeeds. -/
def honest (ast : LLZK.Module) (source : SourceWitness F) :
    Option (R1CS.System F × R1CS.Witness F × Nat) :=
  (withCompiled ast fun _ compiled ↦
    (compiled.artifact.forward source).toOption.map fun w ↦
      (compiled.artifact.target, w, compiled.artifact.paramOffset)).toOption.bind id

def productSource (a b : F) : SourceWitness F := { inputs := [a, b], objects := [] }

-- `self` is reserved: exactly one slot, and the honest witness satisfies the target.
#guard (honest product (productSource 2 3)).map (fun (sys, w, off) ↦
  (off, holds sys w)) == some (1, true)

-- Setting the reserved slot away from zero must be rejected even though no other
-- constraint mentions it. This fails if `enforceZeroPrefix` is dropped.
#guard (honest product (productSource 2 3)).map (fun (sys, w, _) ↦
  elems.all fun d ↦ d == 0 || !holds sys (bump w 0 d)) == some true

-- Reflection sample: perturbing any single ordinary or auxiliary wire of an honest
-- witness either breaks the target or yields a witness whose readback is still a valid
-- source observation. `accepted` counts the surviving perturbations (some must exist).
def perturbationAudit : Option (Bool × Nat) :=
  let sources := grid2 [[]]
  sources.foldlM (init := (true, 0)) fun (ok, accepted) s ↦ do
    let (sys, w, _) ← honest product s
    let compiled ← (withCompiled product fun m c ↦ (checkTypedSource m ⟨_, Nat.lt_succ_self _⟩,
      c.artifact.readback)).toOption
    let mut ok := ok
    let mut accepted := accepted
    for v in List.range 12 do
      for d in elems do
        if d != 0 then
          let w' := bump w v d
          if holds sys w' then
            accepted := accepted + 1
            ok := ok && compiled.1 (compiled.2 w')
    pure (ok, accepted)

#guard (perturbationAudit.map (·.1)) == some true
-- Non-vacuity: perturbing a wire that no constraint reads (e.g. far beyond the layout)
-- is accepted, so the audit actually reaches its implication.
#guard (perturbationAudit.map (·.2 != 0)) == some true

/-! ## Malformed observations -/

def lengthFaults (ast : LLZK.Module) (sources : List (SourceWitness F)) : Option (List Bool) :=
  sources.mapM fun s ↦
    (withCompiled ast fun _ compiled ↦ (compiled.artifact.forward s).toOption.isNone).toOption

-- Wrong input arity, wrong object arity, and empty input all fail in `forward`.
#guard lengthFaults product [
    { inputs := [1], objects := [] }, { inputs := [1, 2, 3], objects := [] },
    { inputs := [], objects := [] }, { inputs := [1, 2], objects := [0] }] ==
  some [true, true, true, true]
#guard lengthFaults stored [
    { inputs := [1], objects := [] }, { inputs := [1], objects := [2, 3] },
    { inputs := [1, 2], objects := [2] }] == some [true, true, true]
-- ... while a well-shaped observation goes through, satisfying or not.
#guard lengthFaults stored [{ inputs := [1], objects := [2] },
    { inputs := [1], objects := [5] }] == some [false, false]

/-! ## Parameter layout certification

`lowerEntryCertified` requires the compute function to have no more parameters than the
constrain function. -/

def layout (ast : LLZK.Module) : Except String (Nat × Nat) :=
  withCompiled ast fun _ compiled ↦
    (compiled.artifact.computeParams, compiled.artifact.paramOffset)

-- `self` plus the inputs: offset 1 (product, quotient), 1 (stored), 1 (called).
#guard layout product matches .ok (2, 1)
#guard layout stored matches .ok (1, 1)
#guard layout called matches .ok (1, 1)

def rejectedMessage (ast : LLZK.Module) : Option String :=
  match layout ast with
  | .error e => some e
  | .ok _ => none

def hasSubstring (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Compute takes two inputs but constrain only one parameter. -/
def computeWider : LLZK.Module := mkModule [mkStruct "Main" []
  [computeFn "Main" ["a", "b"],
   { name := "constrain", params := [feltParam "a"],
     returnType := none, body := [.funcReturn pos none], pos }]]

#guard (rejectedMessage computeWider).map (hasSubstring · "more parameters") == some true

/-- The frontend infers one compute parameter when there is no compute function; a
constrain function with no parameters at all therefore violates the layout. -/
def noComputeNoParams : LLZK.Module := mkModule [mkStruct "Main" []
  [{ name := "constrain", params := [], returnType := none,
     body := [.funcReturn pos none], pos }]]

#guard (rejectedMessage noComputeNoParams).isSome

/-- Equal counts are accepted: no reserved prefix. -/
def equalCounts : LLZK.Module := mkModule [mkStruct "Main" []
  [computeFn "Main" ["a"],
   { name := "constrain", params := [feltParam "a"],
     returnType := none, body := [.funcReturn pos none], pos }]]

#guard layout equalCounts matches .ok (1, 0)

/-- Constraint-only struct with parameters: default single compute input, reserved rest. -/
def constraintOnly : LLZK.Module := mkModule [mkStruct "Main" []
  [constrainFn "Main" ["a"] []]]

#guard layout constraintOnly matches .ok (1, 1)

/-! ## End to end from the source text path (generator + checker + transport) -/

/-- `witnessAST` runs compute, checks the constraints, and forwards. It must accept exactly
the observations the oracle accepts, and the resulting witness must satisfy the target. -/
def endToEnd (ast : LLZK.Module) (inputs : List F) : Option (Bool × Bool) :=
  match witnessAST (F := F) ast inputs with
  | .error _ => some (false, false)
  | .ok (sys, w) => some (true, holds sys w)

#guard (grid2 [[]]).all fun s ↦
  endToEnd product s.inputs ==
    some (productExpected s.inputs[0]! s.inputs[1]!,
      productExpected s.inputs[0]! s.inputs[1]!)
-- `stored`: compute writes `x` but constrain demands `x + 1`, so the program is
-- unsatisfiable for every input; witness generation must refuse rather than emit a witness.
#guard (grid1 [[]]).all fun s ↦ endToEnd stored s.inputs == some (false, false)
#guard (grid1 [[]]).all fun s ↦ endToEnd called s.inputs ==
  some (calledExpected s.inputs[0]!, calledExpected s.inputs[0]!)

end Dialect.Pipeline.EntryTests
