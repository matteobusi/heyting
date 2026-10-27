import Heyting.Parsers.Main
import Heyting.Passes.DialectPipeline
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Frontend strictness regressions

The parser and typed frontend never skip input or guess a meaning. Each rejection below
was previously accepted silently (skipped, defaulted, or resolved against the wrong
declaration); each acceptance checks the upstream-LLZK behavior that replaced it.
-/

namespace LLZK.FrontendTests

abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Parse, then compile; return the first error message. -/
def compileError (src : String) : String :=
  match LLZK.parse src with
  | .error e => e
  | .ok m => match Dialect.Pipeline.compileAST (F := F) m with
    | .error e => e
    | .ok _ => "<accepted>"

def rejects (needle src : String) : Bool := contains (compileError src) needle

def accepts (src : String) : Bool := compileError src == "<accepted>"

/-- Wrap struct definitions in a root module. -/
def mod (body : String) (attrs : String := "llzk.lang") : String :=
  s!"module attributes \{{attrs}} \{\n{body}\n}"

/-- A minimal well-formed struct whose constrain body is `body`. -/
def simple (name : String) (body : String := "") (params : String := "") : String :=
  let sep := if params.isEmpty then "" else ", "
  s!"struct.def @{name} \{
  function.def @compute({params}) -> !struct.type<@{name}> \{
    %self = struct.new : !struct.type<@{name}>
    function.return %self : !struct.type<@{name}>
  }
  function.def @constrain(%self: !struct.type<@{name}>{sep}{params}) \{
{body}
    function.return
  }
}"

/-! ## Baseline -/

#guard accepts (mod (simple "Main" "    %a = felt.const 1 : !felt.type
    constrain.eq %a, %a : !felt.type, !felt.type"))

/-! ## Parser: nothing is skipped -/

-- Unsupported operations are errors, not `.skipped` statements.
#guard rejects "unsupported operation 'arith.constant'"
  (mod (simple "Main" "    %c = arith.constant 1 : index"))

-- A statement after a type annotation is parsed, not consumed with the annotation.
#guard rejects "unsupported operation 'bool.assert'"
  (mod (simple "Main" "    %a = felt.const 1 : !felt.type
    constrain.eq %a, %a : !felt.type, !felt.type
    bool.assert %a : i1"))

#guard rejects "split-input-file separator"
  (mod (simple "Main") ++ "\n// -----\n" ++ mod (simple "Other"))

#guard rejects "templates are not supported"
  (mod "struct.def @Main<[@N]> {\n}")

#guard rejects "unsupported attribute 'foo' in member attributes"
  (mod "struct.def @Main {\n  struct.member @x : !felt.type {foo}\n}")

#guard rejects "unsupported attribute 'llzk.weird' in module attributes"
  (mod (simple "Main") "llzk.lang, llzk.weird")

#guard rejects "has no body"
  (mod "struct.def @Main {
  function.def @compute() -> !struct.type<@Main> attributes {function.allow_witness}
}")

#guard rejects "unsupported prime field \"moo\""
  (mod (simple "Main" "    %a = felt.const 1 <\"moo\"> : !felt.type"))

#guard rejects "anonymous nested modules are not supported"
  (mod ("module {\n" ++ simple "Main" ++ "\n}"))

#guard rejects "affine map operands"
  (mod (simple "Leaf" ++ "\n" ++ simple "Main"
    ("    %l = struct.readm %self[@l] : !struct.type<@Main>, !struct.type<@Leaf>\n" ++
    "    function.call @Leaf::@constrain(%l) {} : (!struct.type<@Leaf>) -> ()")))

#guard rejects "expected struct.member or function.def in struct body"
  (mod "struct.def @Main {\n  struct.field @x : !felt.type\n}")

#guard rejects "multiple result types are not supported"
  (mod "struct.def @Main {
  function.def @compute() -> (!felt.type, !felt.type) {
    function.return
  }
}")

/-! ## Typed frontend: no guessed meaning -/

def childAndMain (childMembers mainRead mainMembers : String) : String := mod s!"
struct.def @Child \{
{childMembers}
  function.def @compute(%a: !felt.type) -> !struct.type<@Child> \{
    %self = struct.new : !struct.type<@Child>
    %sq = felt.mul %a, %a : !felt.type, !felt.type
    struct.writem %self[@out] = %a : !struct.type<@Child>, !felt.type
    struct.writem %self[@other] = %sq : !struct.type<@Child>, !felt.type
    function.return %self : !struct.type<@Child>
  }
  function.def @constrain(%self: !struct.type<@Child>, %a: !felt.type) \{
    %o = struct.readm %self[@out] : !struct.type<@Child>, !felt.type
    constrain.eq %o, %a : !felt.type, !felt.type
    function.return
  }
}
struct.def @Main \{
{mainMembers}
  function.def @compute(%a: !felt.type) -> !struct.type<@Main> \{
    %self = struct.new : !struct.type<@Main>
    %c = function.call @Child::@compute(%a) : (!felt.type) -> !struct.type<@Child>
    struct.writem %self[@c] = %c : !struct.type<@Main>, !struct.type<@Child>
    %co = struct.readm %c[@{mainRead}] : !struct.type<@Child>, !felt.type
    struct.writem %self[@out] = %co : !struct.type<@Main>, !felt.type
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %a: !felt.type) \{
    %c = struct.readm %self[@c] : !struct.type<@Main>, !struct.type<@Child>
    function.call @Child::@constrain(%c, %a) : (!struct.type<@Child>, !felt.type) -> ()
    %co = struct.readm %c[@{mainRead}] : !struct.type<@Child>, !felt.type
    constrain.eq %co, %a : !felt.type, !felt.type
    function.return
  }
}"

/-- `Main.@out` has index 0 and `Child.@out` has index 1. Resolving `%c[@out]` in Main's own
member list would read `Child.@other = a * a` and fail `co = a` for `a = 5`. -/
def crossRead : String := childAndMain
  "  struct.member @other : !felt.type\n  struct.member @out : !felt.type {llzk.pub}"
  "out"
  "  struct.member @out : !felt.type {llzk.pub}\n  struct.member @c : !struct.type<@Child>"

#guard accepts crossRead
#guard match LLZK.parse crossRead with
  | .error _ => false
  | .ok m => (Dialect.Pipeline.witnessAST (F := F) m [5]).toBool

-- Upstream LLZK: only public members of another struct are readable.
#guard rejects "reads private member @other of struct @Child" (childAndMain
  "  struct.member @other : !felt.type\n  struct.member @out : !felt.type {llzk.pub}"
  "other"
  "  struct.member @out : !felt.type {llzk.pub}\n  struct.member @c : !struct.type<@Child>")

#guard rejects "has type !struct.type<@Main>, expected !felt.type"
  (mod (simple "Main" "    %a = felt.add %self, %self : !felt.type, !felt.type"))

#guard rejects "duplicate struct definition: @Main"
  (mod (simple "Main" ++ "\n" ++ simple "Main"))

#guard rejects "SSA value %a is defined more than once"
  (mod (simple "Main" "    %a = felt.const 1 : !felt.type
    %a = felt.const 2 : !felt.type"))

#guard rejects "unsupported type !array.type"
  (mod (simple "Main" "" "%x: !array.type<3 x !felt.type>"))

#guard rejects "unsupported function @helper"
  (mod "struct.def @Main {
  function.def @constrain(%self: !struct.type<@Main>) {
    function.return
  }
  function.def @helper() {
    function.return
  }
}")

#guard rejects "differs from the matching @constrain parameters"
  (mod "struct.def @Main {
  function.def @compute(%x: !felt.type {llzk.pub}) -> !struct.type<@Main> {
    %self = struct.new : !struct.type<@Main>
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %x: !felt.type) {
    function.return
  }
}")

#guard rejects "ambiguous entry struct"
  (mod (simple "A" ++ "\n" ++ simple "B"))

#guard rejects "free functions"
  (mod (simple "Main" ++ "\nfunction.def @f() {\n  function.return\n}"))

/-! ## Upstream behavior that replaced silent defaults -/

/-- Nested module paths are absolute, `llzk.main` picks the entry even when another root
exists, field names are recorded, and `{llzk.pub}` inputs reach the typed module. -/
def nested : String :=
  mod (attrs := "llzk.lang, llzk.main = !struct.type<@Lib::@Main<[]>>") s!"
module @Lib \{
{simple "Unused"}
struct.def @Main \{
  function.def @compute(%x: !felt.type<\"bn128\"> \{llzk.pub}, %y: !felt.type)
      -> !struct.type<@Lib::@Main> attributes \{function.allow_witness} \{
    %self = struct.new : !struct.type<@Lib::@Main>
    function.return %self : !struct.type<@Lib::@Main>
  }
  function.def @constrain(%self: !struct.type<@Lib::@Main>, %x: !felt.type \{llzk.pub},
      %y: !felt.type) attributes \{function.allow_constraint} \{
    constrain.eq %x, %y : !felt.type, !felt.type
    function.return
  }
}
}"

#guard accepts nested
#guard match LLZK.parse nested with
  | .error _ => false
  | .ok m => m.main == some "Lib::Main" && m.fields == ["bn128"] &&
      LLZK.ASTAnalysis.selectEntry m matches .ok "Lib::Main"

#guard match LLZK.parse nested >>= LLZK.ASTAnalysis.restrictToEntry with
  | .error _ => false
  | .ok m => match LLZK.DialectLowering.lowerFull (F := F) m with
    | .error _ => false
    | .ok ⟨k, typed⟩ =>
      (typed.structs ⟨k, Nat.lt_succ_self k⟩).name == "Lib::Main" &&
        (typed.structs ⟨k, Nat.lt_succ_self k⟩).inputIsPublic == [true, false]

-- Inputs are never padded with zeros.
#guard match LLZK.parse nested with
  | .error _ => false
  | .ok m => match Dialect.Pipeline.witnessAST (F := F) m [3] with
    | .error e => contains e "entry struct takes 2 inputs, got 1"
    | .ok _ => false

/-! ## Public statement -/

def publicIO : String := mod s!"
struct.def @Main \{
  struct.member @out : !felt.type \{llzk.pub}
  function.def @compute(%x: !felt.type \{llzk.pub}, %y: !felt.type) -> !struct.type<@Main> \{
    %self = struct.new : !struct.type<@Main>
    %p = felt.mul %x, %y : !felt.type, !felt.type
    struct.writem %self[@out] = %p : !struct.type<@Main>, !felt.type
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %x: !felt.type \{llzk.pub},
      %y: !felt.type) \{
    %out = struct.readm %self[@out] : !struct.type<@Main>, !felt.type
    %p = felt.mul %x, %y : !felt.type, !felt.type
    constrain.eq %out, %p : !felt.type, !felt.type
    function.return
  }
}"

-- The statement wires expose exactly [out, x] = [3 * 2, 3]; the private input 2 is absent.
#guard match LLZK.parse publicIO with
  | .error _ => false
  | .ok m => match Dialect.Pipeline.witnessAST (F := F) m [3, 2] with
    | .error _ => false
    | .ok (system, w) => R1CS.statement system w == [6, 3] &&
        system.publicOutputs.length == 1 && system.publicInputs.length == 1

#guard rejects "public member @out of Main is never read by @constrain"
  (mod "struct.def @Main {
  struct.member @out : !felt.type {llzk.pub}
  function.def @constrain(%self: !struct.type<@Main>) {
    function.return
  }
}")

#guard rejects "has a struct type; only felt members can be public outputs"
  (mod (simple "Leaf" ++ "\n" ++ "struct.def @Main {
  struct.member @l : !struct.type<@Leaf> {llzk.pub}
  function.def @constrain(%self: !struct.type<@Main>) {
    %l = struct.readm %self[@l] : !struct.type<@Main>, !struct.type<@Leaf>
    function.call @Leaf::@constrain(%l) : (!struct.type<@Leaf>) -> ()
    function.return
  }
}"))

end LLZK.FrontendTests
