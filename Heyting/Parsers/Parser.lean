/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Parsers.Tokenizer

/-!
# LLZK Parser

Recursive descent parser converting a token stream into the LLZK AST.
Parses subset of LLZK MLIR textual IR accepted by typed dialect frontend:
modules, struct definitions, member declarations, compute/constrain
functions, Felt operations, constraints, calls, Oracle reads, and objects.

The parser never skips input. Every token is consumed by a rule of the supported
subset, or parsing stops with a positioned error. In particular:

- type annotations are parsed as types, not skipped up to a statement keyword;
- attribute dictionaries accept only attributes whose meaning the compiler implements
  or which do not affect R1CS semantics (`column`, `signal`, function capability flags);
- template parameters, affine map operands, multi-result functions, custom fields,
  anonymous nested modules, and split-input files are errors;
- `!felt.type<"name">` field names are recorded in `Module.fields` for the CLI to check.

Symbol references are absolute paths from the root module, as in upstream LLZK.
-/

namespace LLZK

/-! ## Parser state -/

/-- Parser state: a cursor into a token array and the field names seen so far. -/
structure ParseState where
  tokens : Array PosToken
  cursor : Nat
  fields : List String
  deriving Repr

namespace ParseState

/-- Create initial parser state from token list. -/
def init (tokens : List PosToken) : ParseState :=
  { tokens := tokens.toArray, cursor := 0, fields := [] }

/-- Test whether parser cursor has reached end of token array. -/
def atEnd (s : ParseState) : Bool :=
  s.cursor >= s.tokens.size

/-- Peek current token-position pair, defaulting to synthetic EOF when exhausted. -/
def peek (s : ParseState) : PosToken :=
  if h : s.cursor < s.tokens.size then
    s.tokens[s.cursor]
  else
    { tok := .eof, pos := { line := 0, col := 0 } }

/-- Peek current token kind. -/
def peekTok (s : ParseState) : Token := s.peek.tok
/-- Peek current source position. -/
def peekPos (s : ParseState) : Pos := s.peek.pos

/-- Advance parser cursor by one token. -/
def advance (s : ParseState) : ParseState :=
  { s with cursor := s.cursor + 1 }

end ParseState

/-- Parser monad using StateT over Except. -/
abbrev Parser := StateT ParseState (Except String)

/-! ## Parser primitives -/

/-- Current source position at parser cursor. -/
def getPos : Parser Pos := do
  let s ← get
  return s.peekPos

/-- Current token at parser cursor. -/
def getPeek : Parser Token := do
  let s ← get
  return s.peekTok

/-- Advance parser by one token. -/
def advance : Parser Unit :=
  modify ParseState.advance

/-- Throw a parse error at the current position. -/
def failHere {α : Type} (msg : String) : Parser α := do
  throw s!"{← getPos}: {msg}"

/-- Consume exact token or throw parse error with current position. -/
def expect (tok : Token) (msg : String := "") : Parser Unit := do
  let s ← get
  if s.peekTok == tok then
    modify ParseState.advance
  else
    let m := if msg.isEmpty then s!"expected {tok}, got {s.peekTok}" else msg
    throw s!"{s.peekPos}: {m}"

/-- Consume exact keyword token or throw positioned parse error. -/
def expectKeyword (kw : String) : Parser Unit := do
  let s ← get
  match s.peekTok with
  | .keyword k =>
    if k == kw then modify ParseState.advance
    else throw s!"{s.peekPos}: expected keyword '{kw}', got '{k}'"
  | other => throw s!"{s.peekPos}: expected keyword '{kw}', got {other}"

/-- Consume SSA name token `%name`. -/
def expectSSAName : Parser SSAName := do
  let s ← get
  match s.peekTok with
  | .ssaName n => do modify ParseState.advance; return n
  | other => throw s!"{s.peekPos}: expected SSA name (%name), got {other}"

/-- Consume one symbol name token `@name`. -/
def expectSymName : Parser SymName := do
  let s ← get
  match s.peekTok with
  | .symName n => do modify ParseState.advance; return n
  | other => throw s!"{s.peekPos}: expected symbol name (@name), got {other}"

/-- Consume a possibly nested symbol reference `@A::@B::@c`.
The tokenizer keeps the `::` separator on each leading part, so the parts concatenate
to the path `A::B::c`. A trailing `::` without a following part is an error. -/
partial def expectSymRef : Parser SymName := do
  let first ← expectSymName
  let rec loop (acc : SymName) : Parser SymName := do
    if acc.endsWith "::" then
      match ← getPeek with
      | .symName part => advance; loop (acc ++ part)
      | other => failHere s!"expected symbol after '{acc}', got {other}"
    else
      return acc
  loop first

/-- Consume integer literal token. -/
def expectIntLit : Parser Int := do
  let s ← get
  match s.peekTok with
  | .intLit v => do modify ParseState.advance; return v
  | other => throw s!"{s.peekPos}: expected integer literal, got {other}"

/-! ## Fields -/

/-- Prime-field names known to upstream LLZK (`llzk::Field`) and to the CLI. -/
def knownFields : List String :=
  ["bn128", "bn254", "babybear", "goldilocks", "mersenne31", "koalabear"]

/-- Parse a field specifier `<"name">` and record the field name. -/
def parseFieldSpec : Parser Unit := do
  expect .langle
  let pos ← getPos
  match ← getPeek with
  | .keyword k =>
    if k.startsWith "\"" && k.endsWith "\"" && k.length ≥ 2 then
      let name := (k.drop 1).dropEnd 1 |>.toString
      unless knownFields.contains name do
        throw s!"{pos}: unsupported prime field \"{name}\"; supported: {knownFields}"
      advance
      modify fun s => { s with fields := s.fields ++ [name] }
    else throw s!"{pos}: expected quoted field name, got '{k}'"
  | other => throw s!"{pos}: expected quoted field name, got {other}"
  expect .rangle

/-! ## Type parsing -/

/-- Skip one balanced `<...>` group whose opening `<` was already consumed.
Used only for types outside the subset (`!array.type<...>`), which lowering rejects. -/
private partial def skipAngleAux (s : ParseState) (depth : Nat) : ParseState :=
  if depth == 0 then s
  else if s.atEnd then s
  else match s.peekTok with
  | .langle => skipAngleAux s.advance (depth + 1)
  | .rangle => skipAngleAux s.advance (depth - 1)
  | .eof => s
  | _ => skipAngleAux s.advance depth

/-- Parse the body of a struct type after its `<`: `@Path` with optional empty `<[]>`,
then `>`. Non-empty template arguments are rejected. -/
def parseStructTypeArgs : Parser Ty := do
  let name ← expectSymRef
  if (← getPeek) == .langle then
    advance
    expect .lbracket "template arguments are not supported"
    expect .rbracket "template arguments are not supported (only empty '<[]>' is accepted)"
    expect .rangle
  expect .rangle
  return .structTy name

/-- Test whether a bare keyword names an MLIR builtin integer/index type. -/
private def isBuiltinTypeKeyword (k : String) : Bool :=
  k == "index" || k == "none" ||
    (k.startsWith "i" && k.length > 1 && (k.drop 1).all Char.isDigit)

/-- Parse a type:
- `!felt.type` with optional field `<"name">`;
- `!struct.type<@Path>` or the elided form `<@Path>`, with optional empty `<[]>`;
- other `!name<...>` and builtin `index`/`iN`/`none` types → `Ty.other` (rejected by lowering
  wherever a value of that type would matter). -/
def parseType : Parser Ty := do
  match ← getPeek with
  | .typeName "felt.type" =>
    advance
    if (← getPeek) == .langle then parseFieldSpec
    return .felt
  | .typeName "struct.type" =>
    advance
    expect .langle "expected '<' after !struct.type"
    parseStructTypeArgs
  | .typeName name =>
    advance
    if (← getPeek) == .langle then
      let s ← get
      set (skipAngleAux s.advance 1)
    return .other name
  | .langle =>
    advance
    parseStructTypeArgs
  | .keyword k =>
    if isBuiltinTypeKeyword k then
      advance
      return .other k
    else failHere s!"expected type, got keyword '{k}'"
  | other => failHere s!"expected type, got {other}"

/-- Parse a parenthesized type list `( t, ... )`; the `(` is the current token. -/
private partial def parseTypeTuple : Parser Unit := do
  expect .lparen
  if (← getPeek) == .rparen then
    advance
    return
  let _ ← parseType
  while (← getPeek) == .comma do
    advance
    let _ ← parseType
  expect .rparen

/-- Parse an optional operation type annotation:
`: t (, t)*` or `: (t, ...) -> t` or `: (t, ...) -> (t, ...)`.
Annotations restate operand types and are not used by lowering, but they are fully
parsed so that no following statement can be consumed with them. -/
partial def parseTypeAnnotation : Parser Unit := do
  unless (← getPeek) == .colon do return
  advance
  if (← getPeek) == .lparen then
    parseTypeTuple
    expect .arrow "expected '->' in function type annotation"
    if (← getPeek) == .lparen then parseTypeTuple
    else let _ ← parseType
  else
    let _ ← parseType
    while (← getPeek) == .comma do
      advance
      let _ ← parseType

/-! ## Attributes -/

/-- One attribute dictionary entry: its name, position, and type value if it has one. -/
structure AttrEntry where
  name  : String
  pos   : Pos
  value : Option Ty := none

/-- Skip an attribute value up to the next `,` or `}` at nesting depth zero. -/
private partial def skipAttrValue (depth : Nat) : Parser Unit := do
  match ← getPeek with
  | .eof => failHere "unterminated attribute value"
  | .comma => if depth == 0 then return else advance; skipAttrValue depth
  | .rbrace => if depth == 0 then return else advance; skipAttrValue (depth - 1)
  | .lbrace | .langle | .lparen | .lbracket => advance; skipAttrValue (depth + 1)
  | .rangle | .rparen | .rbracket => advance; skipAttrValue (depth - 1)
  | _ => advance; skipAttrValue depth

/-- Parse an attribute dictionary `{ name (= value)?, ... }` (current token `{`).
Every attribute name must be in `allowed`. Values of `typed` attributes are parsed as types
and returned; values of `opaqueValues` attributes are metadata without semantic effect and
are skipped; any other attribute must not have a value. -/
partial def parseAttrDict (context : String) (allowed : List String)
    (opaqueValues : List String := []) (typed : List String := []) :
    Parser (List AttrEntry) := do
  expect .lbrace
  let mut entries : List AttrEntry := []
  if (← getPeek) == .rbrace then
    advance
    return entries
  repeat
    let pos ← getPos
    let name ← match ← getPeek with
      | .keyword k => advance; pure k
      | other => failHere s!"expected attribute name in {context}, got {other}"
    unless allowed.contains name do
      throw s!"{pos}: unsupported attribute '{name}' in {context}; supported: {allowed}"
    if entries.any (·.name == name) then
      throw s!"{pos}: duplicate attribute '{name}' in {context}"
    let mut value : Option Ty := none
    if (← getPeek) == .equals then
      advance
      if typed.contains name then value := some (← parseType)
      else if opaqueValues.contains name then skipAttrValue 0
      else throw s!"{pos}: attribute '{name}' in {context} takes no value"
    else if typed.contains name then
      throw s!"{pos}: attribute '{name}' in {context} requires a value"
    entries := entries ++ [{ name, pos, value }]
    match ← getPeek with
    | .comma => advance
    | .rbrace => advance; break
    | other => failHere s!"expected ',' or '}' in {context}, got {other}"
  return entries

/-- Member attributes. `column` and `signal` mark PLONKish columns and circom signals;
they do not change R1CS semantics (offset reads that use columns are unsupported). -/
def memberAttrs : List String := ["llzk.pub", "column", "signal"]

/-- Function attributes. The capability flags only widen which operations a body may
contain, and every supported operation is checked by lowering; `llzk.derived` is metadata.
`extern` (a body-less declaration) is rejected. -/
def funcAttrs : List String :=
  ["function.allow_constraint", "function.allow_witness",
    "function.allow_non_native_field_ops", "llzk.derived"]

/-- Parse an optional `{...}` attribute dictionary on a member or parameter and return
whether it contains `llzk.pub`. -/
def parseOptPubAttrs (context : String) (allowed : List String) : Parser Bool := do
  if (← getPeek) == .lbrace then
    let entries ← parseAttrDict context allowed
    return entries.any (·.name == "llzk.pub")
  else
    return false

/-- Parse an optional `attributes {...}` clause on a function definition. -/
def parseFuncAttrsKw : Parser Unit := do
  match ← getPeek with
  | .keyword "attributes" =>
    advance
    let _ ← parseAttrDict "function attributes" funcAttrs
  | _ => pure ()

/-! ## Statement parsing -/

/-- Parse a binary felt operation. -/
def parseFeltBinop (pos : Pos) (dest : SSAName)
    (mkStmt : Pos → SSAName → SSAName → SSAName → Stmt) : Parser Stmt := do
  let src1 ← expectSSAName
  expect .comma
  let src2 ← expectSSAName
  parseTypeAnnotation
  return mkStmt pos dest src1 src2

/-- Parse a felt.neg operation. -/
def parseFeltNeg (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let src ← expectSSAName
  parseTypeAnnotation
  return .feltNeg pos dest src

/-- Parse a felt.inv operation. -/
def parseFeltInv (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let src ← expectSSAName
  parseTypeAnnotation
  return .feltInv pos dest src

/-- Parse a felt.const operation.
Handles `felt.const 42`, `felt.const 42 <"babybear">`, and `felt.const 42 : !felt.type`. -/
def parseFeltConst (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let value ← expectIntLit
  if (← getPeek) == .langle then parseFieldSpec
  parseTypeAnnotation
  return .feltConst pos dest value

/-- Parse struct.new: `%dest = struct.new : !struct.type<@Name>` or shorthand `: <@Name>`. -/
def parseStructNew (pos : Pos) (dest : SSAName) : Parser Stmt := do
  expect .colon
  match ← parseType with
  | .structTy name => return .structNew pos dest name
  | _ => throw s!"{pos}: struct.new requires !struct.type<@Name>"

/-- Parse struct.readm: `%dest = struct.readm %self[@member] : ...` -/
def parseReadMember (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let self ← expectSSAName
  expect .lbracket
  let member ← expectSymName
  expect .rbracket
  if (← getPeek) == .lbrace then
    failHere "struct.readm with offset/map operands is not supported"
  parseTypeAnnotation
  return .readMember pos dest self member

/-- Parse struct.writem: `struct.writem %self[@member] = %src : ...` -/
def parseWriteMember (pos : Pos) : Parser Stmt := do
  let self ← expectSSAName
  expect .lbracket
  let member ← expectSymName
  expect .rbracket
  expect .equals
  let src ← expectSSAName
  parseTypeAnnotation
  return .writeMember pos self member src

/-- Parse constrain.eq: `constrain.eq %a, %b : !felt.type` -/
def parseConstrainEq (pos : Pos) : Parser Stmt := do
  let src1 ← expectSSAName
  expect .comma
  let src2 ← expectSSAName
  parseTypeAnnotation
  return .constrainEq pos src1 src2

/-- Parse comma-separated SSA args until `)`. -/
private partial def parseArgsLoop (args : List SSAName) : Parser (List SSAName) := do
  let tok ← getPeek
  if tok == .comma then
    advance
    let a ← expectSSAName
    parseArgsLoop (args ++ [a])
  else
    return args

/-- Parse function.call: `%dest = function.call @target(%args) : ...`
or void: `function.call @target(%args) : ...`. The target is an absolute path such as
`@Mod::@Struct::@compute`. Affine map operands `{...}` are rejected. -/
def parseFuncCall (pos : Pos) (dest : Option SSAName) : Parser Stmt := do
  let target ← expectSymRef
  expect .lparen
  let firstTok ← getPeek
  let args ← if firstTok != .rparen then do
    let a ← expectSSAName
    parseArgsLoop [a]
  else
    pure []
  expect .rparen
  if (← getPeek) == .lbrace then
    failHere "function.call with affine map operands is not supported"
  parseTypeAnnotation
  return .call pos dest target args

/-- Parse function.return: `function.return %v : ...` or `function.return` -/
def parseFuncReturn (pos : Pos) : Parser Stmt := do
  let tok ← getPeek
  match tok with
  | .ssaName _ =>
    let v ← expectSSAName
    if (← getPeek) == .comma then
      failHere "function.return with multiple values is not supported"
    parseTypeAnnotation
    return .funcReturn pos (some v)
  | _ => return .funcReturn pos none

/-- Parse llzk.nondet: `%dest = llzk.nondet : !felt.type` -/
def parseNondet (pos : Pos) (dest : SSAName) : Parser Stmt := do
  expect .colon
  let ty ← parseType
  match ty with
  | .felt => return .nondet pos dest
  | other => throw s!"{pos}: llzk.nondet with non-felt type ({repr other}) not supported"

/-- Parse a single statement. Every operation outside the supported subset is an error. -/
partial def parseStmt : Parser Stmt := do
  let pos ← getPos
  match ← getPeek with
  | .ssaName dest => do
    advance  -- consume %dest
    if (← getPeek) == .comma then
      failHere s!"operations with multiple results are not supported (at %{dest})"
    expect .equals s!"expected '=' after %{dest}"
    match ← getPeek with
    | .keyword op =>
      advance  -- consume the op keyword
      match op with
      | "felt.add" => parseFeltBinop pos dest .feltAdd
      | "felt.sub" => parseFeltBinop pos dest .feltSub
      | "felt.mul" => parseFeltBinop pos dest .feltMul
      | "felt.div" => parseFeltBinop pos dest .feltDiv
      | "felt.neg" => parseFeltNeg pos dest
      | "felt.inv" => parseFeltInv pos dest
      | "felt.const" => parseFeltConst pos dest
      | "struct.new" => parseStructNew pos dest
      | "struct.readm" => parseReadMember pos dest
      | "function.call" => parseFuncCall pos (some dest)
      | "llzk.nondet" => parseNondet pos dest
      | _ => throw s!"{pos}: unsupported operation '{op}'"
    | other => throw s!"{pos}: expected operation name after '=', got {other}"
  | .keyword kw =>
    advance  -- consume the keyword
    match kw with
    | "struct.writem" => parseWriteMember pos
    | "constrain.eq" => parseConstrainEq pos
    | "function.call" => parseFuncCall pos none
    | "function.return" => parseFuncReturn pos
    | _ => throw s!"{pos}: unsupported operation '{kw}'"
  | other => throw s!"{pos}: expected statement, got {other}"

/-- Parse a function body: statements up to the closing `}` (not consumed). -/
partial def parseBody : Parser (List Stmt) := do
  match ← getPeek with
  | .rbrace => return []
  | .eof => failHere "unexpected end of input in function body"
  | _ =>
    let stmt ← parseStmt
    let rest ← parseBody
    return stmt :: rest

/-! ## Top-level declarations -/

/-- Parse one parameter `%name : type {attrs}?`. -/
private def parseParam : Parser ParamDecl := do
  let name ← expectSSAName
  expect .colon
  let ty ← parseType
  let isPublic ← parseOptPubAttrs "parameter attributes" ["llzk.pub"]
  return { name, ty, isPublic }

/-- Parse comma-separated parameters until `)`. -/
private partial def parseParamsLoop (params : List ParamDecl) : Parser (List ParamDecl) := do
  let tok ← getPeek
  if tok == .comma then
    advance
    let p ← parseParam
    parseParamsLoop (params ++ [p])
  else
    return params

/-- Parse a parameter list: `(%name: !type {llzk.pub}?, ...)`. -/
def parseParams : Parser (List ParamDecl) := do
  expect .lparen
  let tok ← getPeek
  let params ← if tok != .rparen then do
    let p ← parseParam
    parseParamsLoop [p]
  else
    pure []
  expect .rparen
  return params

/-- Parse a function definition:
`function.def @name(%params) -> !type attributes {...} { body }`.
`prefix` is the absolute module path (`"M::"` or `""`) of the enclosing scope. -/
def parseFuncDef (pfx : String := "") : Parser FuncDef := do
  let pos ← getPos
  expectKeyword "function.def"
  -- `private` only restricts symbol visibility.
  if (← getPeek) == .keyword "private" then advance
  let name ← expectSymName
  let params ← parseParams
  let mut retType : Option Ty := none
  if (← getPeek) == .arrow then
    advance
    if (← getPeek) == .lparen then
      failHere s!"function @{name}: parenthesized or multiple result types are not supported"
    retType := some (← parseType)
  parseFuncAttrsKw
  expect .lbrace s!"function @{name} has no body (external declarations are not \
supported)"
  let body ← parseBody
  expect .rbrace
  return { name := pfx ++ name, params, returnType := retType, body, pos }

/-- Parse a member declaration: `struct.member @name : !type {llzk.pub}?` -/
def parseMemberDecl : Parser MemberDecl := do
  let pos ← getPos
  expectKeyword "struct.member"
  let name ← expectSymName
  expect .colon
  let ty ← parseType
  let isPublic ← parseOptPubAttrs "member attributes" memberAttrs
  return { name, ty, isPublic, pos }

/-- Parse members and functions inside a struct body. -/
private partial def parseStructBody (members : List MemberDecl) (funcs : List FuncDef) :
    Parser (List MemberDecl × List FuncDef) := do
  match ← getPeek with
  | .rbrace => return (members, funcs)
  | .keyword "struct.member" =>
    let m ← parseMemberDecl
    parseStructBody (members ++ [m]) funcs
  | .keyword "function.def" =>
    let f ← parseFuncDef
    parseStructBody members (funcs ++ [f])
  | other => failHere s!"expected struct.member or function.def in struct body, got {other}"

/-- Parse a struct definition `struct.def @Name { members... functions... }`.
Only the empty template parameter list `<[]>` is accepted. -/
def parseStructDef (pfx : String := "") : Parser StructDef := do
  let pos ← getPos
  expectKeyword "struct.def"
  let name ← expectSymName
  if (← getPeek) == .langle then
    advance
    expect .lbracket s!"struct '{name}': malformed template parameters"
    expect .rbracket s!"struct '{name}' has template parameters; templates are not \
supported"
    expect .rangle
  expect .lbrace
  let (members, funcs) ← parseStructBody [] []
  expect .rbrace
  return { name := pfx ++ name, members, funcs, pos }

/-- Module attributes. `llzk.lang` is a language tag and its value is metadata;
`llzk.main` selects the entry struct and is accepted only on the root module. -/
private def parseModuleAttrs (isRoot : Bool) : Parser (Option SymName) := do
  unless (← getPeek) == .keyword "attributes" do return none
  advance
  let allowed := if isRoot then ["llzk.lang", "llzk.main"] else ["llzk.lang"]
  let entries ← parseAttrDict "module attributes" allowed (opaqueValues := ["llzk.lang"])
    (typed := ["llzk.main"])
  match entries.find? (·.name == "llzk.main") with
  | none => return none
  | some { value := some (.structTy name), .. } => return some name
  | some entry => throw s!"{entry.pos}: llzk.main must be a struct type"

mutual

/-- Parse struct definitions, nested modules, and free functions at module level. -/
private partial def parseModuleBody (pfx : String) (structs : List StructDef)
    (freeFuncs : List FuncDef) : Parser (List StructDef × List FuncDef) := do
  match ← getPeek with
  | .rbrace => return (structs, freeFuncs)
  | .keyword "struct.def" =>
    let sd ← parseStructDef pfx
    parseModuleBody pfx (structs ++ [sd]) freeFuncs
  | .keyword "module" =>
    let (nestedStructs, nestedFuncs) ← parseNestedModule pfx
    parseModuleBody pfx (structs ++ nestedStructs) (freeFuncs ++ nestedFuncs)
  | .keyword "function.def" =>
    let f ← parseFuncDef pfx
    parseModuleBody pfx structs (freeFuncs ++ [f])
  | other => failHere s!"expected struct.def, function.def, or module at module level, \
got {other}"

/-- Parse a named nested module `module @Name attributes {...}? { ... }`. Its symbols
get the absolute prefix `pfx ++ "Name::"`. Anonymous nested modules are rejected because
their symbols are not reachable by an absolute path. -/
private partial def parseNestedModule (pfx : String) :
    Parser (List StructDef × List FuncDef) := do
  let pos ← getPos
  expectKeyword "module"
  let name ← match ← getPeek with
    | .symName n => advance; pure n
    | _ => throw s!"{pos}: anonymous nested modules are not supported"
  let _ ← parseModuleAttrs false
  expect .lbrace
  let result ← parseModuleBody (pfx ++ name ++ "::") [] []
  expect .rbrace
  return result

end

/-- Parse the root module `module @Name? attributes {...}? { ... }`. The root module name
is not part of symbol paths. -/
def parseModule : Parser Module := do
  let pos ← getPos
  expectKeyword "module"
  if let .symName _ := (← getPeek) then advance
  let main ← parseModuleAttrs true
  expect .lbrace
  let (structs, freeFuncs) ← parseModuleBody "" [] []
  expect .rbrace
  return { structs, freeFuncs, pos, main }

/-! ## Entry point -/

/-- Detect `// -----` split-input-file separators used by upstream LLZK tests. -/
private def hasSplitMarker (input : String) : Option Nat :=
  let lines := input.splitOn "\n"
  (lines.zipIdx.find? fun (l, _) =>
    let t := l.trimAsciiStart
    t.startsWith "// -----" || t.startsWith "//-----").map (·.2 + 1)

/-- Parse bare top-level declarations (no module wrapper) up to end of input. -/
private partial def parseBareTopLevel (structs : List StructDef) (freeFuncs : List FuncDef) :
    Parser (List StructDef × List FuncDef) := do
  match ← getPeek with
  | .eof => return (structs, freeFuncs)
  | .keyword "struct.def" =>
    let sd ← parseStructDef
    parseBareTopLevel (structs ++ [sd]) freeFuncs
  | .keyword "function.def" =>
    let f ← parseFuncDef
    parseBareTopLevel structs (freeFuncs ++ [f])
  | other => failHere s!"expected struct.def or function.def at top level, got {other}"

/-- Parse an LLZK source string into a Module AST: either one root `module { ... }` or
bare top-level declarations. Split-input files (`// -----`) are rejected because their
sections are independent programs; compile each section separately. -/
def parse (input : String) : Except String Module := do
  if let some line := hasSplitMarker input then
    throw s!"{line}:1: split-input-file separator '// -----' is not supported; \
compile each section as a separate file"
  let tokens ← tokenize input
  let parser : Parser Module := do
    let pos ← getPos
    match ← getPeek with
    | .keyword "module" =>
      let m ← parseModule
      unless (← getPeek) == .eof do
        failHere "unexpected content after the root module"
      return m
    | .keyword "struct.def" | .keyword "function.def" =>
      let (structs, freeFuncs) ← parseBareTopLevel [] []
      return { structs, freeFuncs, pos }
    | .eof => failHere "empty input"
    | other => failHere s!"expected 'module' or 'struct.def', got {other}"
  let (m, s) ← parser.run (ParseState.init tokens)
  return { m with fields := s.fields.eraseDups }

end LLZK
