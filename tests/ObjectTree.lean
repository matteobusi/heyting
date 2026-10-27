import Heyting.Parsers.Main
import Heyting.Passes.DialectPipeline
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Sub-component placement (tree object model)

`@compute` stores a sub-component with `writeObject`, which copies its subtree below the
member path where `@constrain` reads it. Before the tree model, a sub-component's path was its
allocation number, so these programs either failed witness generation or, for unconstrained
members, received values that differ from upstream compute semantics. Each check below runs
the real frontend and pipeline and compares the public statement with the upstream value.
-/

namespace Dialect.ObjectTreeTests

abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Public statement of the generated witness, or `none` on any failure. -/
def statementOf (src : String) (inputs : List F) : Option (List F) :=
  match LLZK.parse src with
  | .error _ => none
  | .ok m => match Pipeline.witnessAST (F := F) m inputs with
    | .error _ => none
    | .ok (system, w) => some (R1CS.statement system w)

def mod (body : String) : String :=
  "module attributes {llzk.lang, llzk.main = !struct.type<@Main>} {\n" ++ body ++ "\n}"

/-- Leaf component: public `@v = x + k`, constrained. -/
def leaf (name : String) (k : Nat) : String := s!"
struct.def @{name} \{
  struct.member @v : !felt.type \{llzk.pub}
  function.def @compute(%x: !felt.type) -> !struct.type<@{name}> \{
    %self = struct.new : !struct.type<@{name}>
    %k = felt.const {k} : !felt.type
    %v = felt.add %x, %k : !felt.type, !felt.type
    struct.writem %self[@v] = %v : !struct.type<@{name}>, !felt.type
    function.return %self : !struct.type<@{name}>
  }
  function.def @constrain(%self: !struct.type<@{name}>, %x: !felt.type) \{
    %v = struct.readm %self[@v] : !struct.type<@{name}>, !felt.type
    %k = felt.const {k} : !felt.type
    %e = felt.add %x, %k : !felt.type, !felt.type
    constrain.eq %v, %e : !felt.type, !felt.type
    function.return
  }
}"

/-- The sub-component member `@c` has index 0 but is the second allocation. -/
def indexBeforeAllocation : String := mod (leaf "Child" 1 ++ "
struct.def @Main {
  struct.member @c : !struct.type<@Child>
  struct.member @out : !felt.type {llzk.pub}
  function.def @compute(%a: !felt.type) -> !struct.type<@Main> {
    %self = struct.new : !struct.type<@Main>
    %c = function.call @Child::@compute(%a) : (!felt.type) -> !struct.type<@Child>
    struct.writem %self[@c] = %c : !struct.type<@Main>, !struct.type<@Child>
    %v = struct.readm %c[@v] : !struct.type<@Child>, !felt.type
    struct.writem %self[@out] = %v : !struct.type<@Main>, !felt.type
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %a: !felt.type) {
    %c = struct.readm %self[@c] : !struct.type<@Main>, !struct.type<@Child>
    function.call @Child::@constrain(%c, %a) : (!struct.type<@Child>, !felt.type) -> ()
    %v = struct.readm %c[@v] : !struct.type<@Child>, !felt.type
    %out = struct.readm %self[@out] : !struct.type<@Main>, !felt.type
    constrain.eq %v, %out : !felt.type, !felt.type
    function.return
  }
}")

#guard statementOf indexBeforeAllocation [3] == some [4]

/-- Two sub-components created in the reverse order of their member indices. -/
def reverseOrder : String := mod (leaf "Child" 0 ++ "
struct.def @Main {
  struct.member @a : !struct.type<@Child>
  struct.member @b : !struct.type<@Child>
  struct.member @out : !felt.type {llzk.pub}
  function.def @compute(%x: !felt.type, %y: !felt.type) -> !struct.type<@Main> {
    %self = struct.new : !struct.type<@Main>
    %cb = function.call @Child::@compute(%y) : (!felt.type) -> !struct.type<@Child>
    %ca = function.call @Child::@compute(%x) : (!felt.type) -> !struct.type<@Child>
    struct.writem %self[@a] = %ca : !struct.type<@Main>, !struct.type<@Child>
    struct.writem %self[@b] = %cb : !struct.type<@Main>, !struct.type<@Child>
    %va = struct.readm %ca[@v] : !struct.type<@Child>, !felt.type
    %vb = struct.readm %cb[@v] : !struct.type<@Child>, !felt.type
    %d = felt.sub %va, %vb : !felt.type, !felt.type
    struct.writem %self[@out] = %d : !struct.type<@Main>, !felt.type
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %x: !felt.type, %y: !felt.type) {
    %ca = struct.readm %self[@a] : !struct.type<@Main>, !struct.type<@Child>
    %cb = struct.readm %self[@b] : !struct.type<@Main>, !struct.type<@Child>
    function.call @Child::@constrain(%ca, %x) : (!struct.type<@Child>, !felt.type) -> ()
    function.call @Child::@constrain(%cb, %y) : (!struct.type<@Child>, !felt.type) -> ()
    %va = struct.readm %ca[@v] : !struct.type<@Child>, !felt.type
    %vb = struct.readm %cb[@v] : !struct.type<@Child>, !felt.type
    %d = felt.sub %va, %vb : !felt.type, !felt.type
    %out = struct.readm %self[@out] : !struct.type<@Main>, !felt.type
    constrain.eq %d, %out : !felt.type, !felt.type
    function.return
  }
}")

-- out = x - y = 5 - 1.
#guard statementOf reverseOrder [5, 1] == some [4]

/-- Two levels: Main ⊃ Mid ⊃ Leaf. -/
def twoLevels : String := mod (leaf "Leaf" 1 ++ "
struct.def @Mid {
  struct.member @l : !struct.type<@Leaf>
  struct.member @w : !felt.type {llzk.pub}
  function.def @compute(%x: !felt.type) -> !struct.type<@Mid> {
    %self = struct.new : !struct.type<@Mid>
    %l = function.call @Leaf::@compute(%x) : (!felt.type) -> !struct.type<@Leaf>
    struct.writem %self[@l] = %l : !struct.type<@Mid>, !struct.type<@Leaf>
    %v = struct.readm %l[@v] : !struct.type<@Leaf>, !felt.type
    %w = felt.add %v, %v : !felt.type, !felt.type
    struct.writem %self[@w] = %w : !struct.type<@Mid>, !felt.type
    function.return %self : !struct.type<@Mid>
  }
  function.def @constrain(%self: !struct.type<@Mid>, %x: !felt.type) {
    %l = struct.readm %self[@l] : !struct.type<@Mid>, !struct.type<@Leaf>
    function.call @Leaf::@constrain(%l, %x) : (!struct.type<@Leaf>, !felt.type) -> ()
    %v = struct.readm %l[@v] : !struct.type<@Leaf>, !felt.type
    %w = struct.readm %self[@w] : !struct.type<@Mid>, !felt.type
    %e = felt.add %v, %v : !felt.type, !felt.type
    constrain.eq %w, %e : !felt.type, !felt.type
    function.return
  }
}
struct.def @Main {
  struct.member @m : !struct.type<@Mid>
  struct.member @out : !felt.type {llzk.pub}
  function.def @compute(%a: !felt.type) -> !struct.type<@Main> {
    %self = struct.new : !struct.type<@Main>
    %m = function.call @Mid::@compute(%a) : (!felt.type) -> !struct.type<@Mid>
    struct.writem %self[@m] = %m : !struct.type<@Main>, !struct.type<@Mid>
    %w = struct.readm %m[@w] : !struct.type<@Mid>, !felt.type
    struct.writem %self[@out] = %w : !struct.type<@Main>, !felt.type
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %a: !felt.type) {
    %m = struct.readm %self[@m] : !struct.type<@Main>, !struct.type<@Mid>
    function.call @Mid::@constrain(%m, %a) : (!struct.type<@Mid>, !felt.type) -> ()
    %w = struct.readm %m[@w] : !struct.type<@Mid>, !felt.type
    %out = struct.readm %self[@out] : !struct.type<@Main>, !felt.type
    constrain.eq %w, %out : !felt.type, !felt.type
    function.return
  }
}")

-- out = 2 * (a + 1) = 2 * 3.
#guard statementOf twoLevels [2] == some [6]

/-- The child has more members than the reader, and its read member `@sq = a * a` is not
constrained by the child. The value must still be the upstream compute value. -/
def wideUnconstrained : String := mod "
struct.def @Child {
  struct.member @p0 : !felt.type
  struct.member @p1 : !felt.type
  struct.member @sq : !felt.type {llzk.pub}
  function.def @compute(%a: !felt.type) -> !struct.type<@Child> {
    %self = struct.new : !struct.type<@Child>
    %sq = felt.mul %a, %a : !felt.type, !felt.type
    struct.writem %self[@p0] = %a : !struct.type<@Child>, !felt.type
    struct.writem %self[@p1] = %a : !struct.type<@Child>, !felt.type
    struct.writem %self[@sq] = %sq : !struct.type<@Child>, !felt.type
    function.return %self : !struct.type<@Child>
  }
  function.def @constrain(%self: !struct.type<@Child>, %a: !felt.type) {
    %p0 = struct.readm %self[@p0] : !struct.type<@Child>, !felt.type
    constrain.eq %p0, %a : !felt.type, !felt.type
    function.return
  }
}
struct.def @Main {
  struct.member @c : !struct.type<@Child>
  struct.member @out : !felt.type {llzk.pub}
  function.def @compute(%a: !felt.type) -> !struct.type<@Main> {
    %self = struct.new : !struct.type<@Main>
    %c = function.call @Child::@compute(%a) : (!felt.type) -> !struct.type<@Child>
    struct.writem %self[@c] = %c : !struct.type<@Main>, !struct.type<@Child>
    %sq = struct.readm %c[@sq] : !struct.type<@Child>, !felt.type
    struct.writem %self[@out] = %sq : !struct.type<@Main>, !felt.type
    function.return %self : !struct.type<@Main>
  }
  function.def @constrain(%self: !struct.type<@Main>, %a: !felt.type) {
    %c = struct.readm %self[@c] : !struct.type<@Main>, !struct.type<@Child>
    function.call @Child::@constrain(%c, %a) : (!struct.type<@Child>, !felt.type) -> ()
    %sq = struct.readm %c[@sq] : !struct.type<@Child>, !felt.type
    %out = struct.readm %self[@out] : !struct.type<@Main>, !felt.type
    constrain.eq %sq, %out : !felt.type, !felt.type
    function.return
  }
}"

-- out = 3 * 3 = 9 = 2 in ZMod 7. `@sq` has index 2, beyond Main's own two members.
#guard statementOf wideUnconstrained [3] == some [2]

/-- The lowered module satisfies `SelectorsSupported`, so `genWitness_fault` applies: its
witness generation can fail only on an exhausted oracle or a zero denominator. -/
def selectorsSupported (src : String) : Bool :=
  match LLZK.parse src >>= LLZK.ASTAnalysis.restrictToEntry with
  | .error _ => false
  | .ok ast => match LLZK.DialectLowering.lowerFull (F := F) ast with
    | .error _ => false
    | .ok ⟨_, m⟩ => WitnessExecution.checkSelectors m

#guard selectorsSupported indexBeforeAllocation
#guard selectorsSupported twoLevels

end Dialect.ObjectTreeTests
