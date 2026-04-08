import Heyting.Parser.Parser

/-!
# LLZK Parser — Entry Point

Top-level parsing functions for LLZK MLIR textual IR files.
Provides `LLZK.parseFile` which reads a string and produces the
untyped AST, and `LLZK.ppModule` for pretty-printing the result.

## Usage

```lean
#eval do
  let input := "module { struct.def @Foo { ... } }"
  match LLZK.parse input with
  | .ok (mod, warnings) => IO.println (LLZK.ppModule mod)
  | .error e => IO.eprintln e
```
-/

namespace LLZK

/-! ## Pretty-printing -/

private def indent (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

private def ppTy : Ty → String
  | .felt => "!felt.type"
  | .structTy name => s!"!struct.type<@{name}>"
  | .other name => s!"!{name}"

private def ppStmt (ind : Nat) : Stmt → String
  | .feltAdd _ dest src1 src2 => s!"{indent ind}%{dest} = felt.add %{src1}, %{src2}"
  | .feltSub _ dest src1 src2 => s!"{indent ind}%{dest} = felt.sub %{src1}, %{src2}"
  | .feltMul _ dest src1 src2 => s!"{indent ind}%{dest} = felt.mul %{src1}, %{src2}"
  | .feltDiv _ dest src1 src2 => s!"{indent ind}%{dest} = felt.div %{src1}, %{src2}"
  | .feltNeg _ dest src => s!"{indent ind}%{dest} = felt.neg %{src}"
  | .feltInv _ dest src => s!"{indent ind}%{dest} = felt.inv %{src}"
  | .feltConst _ dest value => s!"{indent ind}%{dest} = felt.const {value}"
  | .structNew _ dest name => s!"{indent ind}%{dest} = struct.new : !struct.type<@{name}>"
  | .readMember _ dest self member =>
    s!"{indent ind}%{dest} = struct.readm %{self}[@{member}]"
  | .writeMember _ self member src =>
    s!"{indent ind}struct.writem %{self}[@{member}] = %{src}"
  | .constrainEq _ src1 src2 => s!"{indent ind}constrain.eq %{src1}, %{src2}"
  | .call _ dest target args =>
    let argStr := ", ".intercalate (args.map fun a => s!"%{a}")
    let destStr := match dest with
      | some d => s!"%{d} = "
      | none => ""
    s!"{indent ind}{destStr}function.call @{target}({argStr})"
  | .funcReturn _ retVal =>
    match retVal with
    | some v => s!"{indent ind}function.return %{v}"
    | none => s!"{indent ind}function.return"
  | .nondet _ dest => s!"{indent ind}%{dest} = llzk.nondet"
  | .skipped _ opName => s!"{indent ind}// skipped: {opName}"

private def ppParam (p : ParamDecl) : String :=
  s!"%{p.name}: {ppTy p.ty}"

private def ppFunc (ind : Nat) (f : FuncDef) : String :=
  let params := ", ".intercalate (f.params.map ppParam)
  let retStr := match f.returnType with
    | some ty => s!" -> {ppTy ty}"
    | none => ""
  let bodyStr := "\n".intercalate (f.body.map (ppStmt (ind + 1)))
  s!"{indent ind}function.def @{f.name}({params}){retStr} \{\n{bodyStr}\n{indent ind}}"

private def ppMember (ind : Nat) (m : MemberDecl) : String :=
  s!"{indent ind}struct.member @{m.name} : {ppTy m.ty}"

private def ppStruct (ind : Nat) (sd : StructDef) : String :=
  let membersStr := "\n".intercalate (sd.members.map (ppMember (ind + 1)))
  let funcsStr := "\n".intercalate (sd.funcs.map (ppFunc (ind + 1)))
  let bodyParts := [membersStr, funcsStr].filter (· != "")
  s!"{indent ind}struct.def @{sd.name} \{\n{"\n".intercalate bodyParts}\n{indent ind}}"

/-- Pretty-print a parsed Module AST. -/
def ppModule (m : Module) : String :=
  let structsStr := "\n\n".intercalate (m.structs.map (ppStruct 1))
  s!"module \{\n{structsStr}\n}"

/-! ## Summary statistics -/

/-- Count statements by type in a module. -/
def countStmts (m : Module) : String :=
  let allStmts : List Stmt :=
    m.structs.flatMap fun sd => sd.funcs.flatMap fun f => f.body
  let total := allStmts.length
  let felt := allStmts.filter fun
    | .feltAdd .. | .feltSub .. | .feltMul .. | .feltDiv ..
    | .feltNeg .. | .feltInv .. | .feltConst .. => true
    | _ => false
  let constrain := allStmts.filter fun | .constrainEq .. => true | _ => false
  let calls := allStmts.filter fun | .call .. => true | _ => false
  let structOps := allStmts.filter fun
    | .structNew .. | .readMember .. | .writeMember .. => true
    | _ => false
  let skipped := allStmts.filter fun | .skipped .. => true | _ => false
  s!"Structs: {m.structs.length}, Total stmts: {total}, \
Felt ops: {felt.length}, Constraints: {constrain.length}, \
Calls: {calls.length}, Struct ops: {structOps.length}, \
Skipped: {skipped.length}"

end LLZK
