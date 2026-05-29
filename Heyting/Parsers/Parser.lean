/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Parsers.Tokenizer

/-!
# LLZK Parser

Recursive descent parser converting a token stream into the LLZK AST.
Parses the subset of LLZK MLIR textual IR that maps to `StructIR`:
modules, struct definitions, member declarations, compute/constrain
functions, felt operations, constraint equations, and struct operations.

Unsupported constructs are skipped with warnings when possible, or
rejected with errors when they appear in critical positions.
-/

namespace LLZK

/-! ## Parser state -/

/-- Parser state: a cursor into a token array with error accumulation. -/
structure ParseState where
  tokens   : Array PosToken
  cursor   : Nat
  warnings : List String
  deriving Repr

namespace ParseState

/-- Create initial parser state from token list. -/
def init (tokens : List PosToken) : ParseState :=
  { tokens := tokens.toArray, cursor := 0, warnings := [] }

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

/-- Append warning message to parser state. -/
def addWarning (s : ParseState) (msg : String) : ParseState :=
  { s with warnings := s.warnings ++ [msg] }

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

/-- Record non-fatal parser warning. -/
def warn (msg : String) : Parser Unit :=
  modify fun s => s.addWarning msg

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

/-- Consume symbol name token `@name`. -/
def expectSymName : Parser SymName := do
  let s ← get
  match s.peekTok with
  | .symName n => do modify ParseState.advance; return n
  | other => throw s!"{s.peekPos}: expected symbol name (@name), got {other}"

/-- Consume integer literal token. -/
def expectIntLit : Parser Int := do
  let s ← get
  match s.peekTok with
  | .intLit v => do modify ParseState.advance; return v
  | other => throw s!"{s.peekPos}: expected integer literal, got {other}"

/-- Test whether current token is keyword `kw`. -/
def isKeyword (kw : String) : Parser Bool := do
  let s ← get
  match s.peekTok with
  | .keyword k => return k == kw
  | _ => return false

/-- Test whether current token is exactly `tok`. -/
def isToken (tok : Token) : Parser Bool := do
  let s ← get
  return s.peekTok == tok

/-! ## Type parsing -/

/-- Skip tokens matching `<...>` with nesting. State-passing to avoid termination issues. -/
private partial def skipAngleAux (s : ParseState) (depth : Nat) : ParseState :=
  if depth == 0 then s
  else if s.atEnd then s
  else match s.peekTok with
  | .langle => skipAngleAux s.advance (depth + 1)
  | .rangle => skipAngleAux s.advance (depth - 1)
  | _ => skipAngleAux s.advance depth

/-- Parse a type. We handle:
- `!felt.type` (with optional `<"fieldname">`)
- `!struct.type<@Name>` (with optional namespacing `@Mod::@Name`)
- Other `!type` tokens → `Ty.other` -/
def parseType : Parser Ty := do
  let s ← get
  match s.peekTok with
  | .typeName name =>
    if name == "felt.type" then
      set s.advance
      let s' ← get
      if s'.peekTok == .langle then
        set (skipAngleAux s'.advance 1)
      return .felt
    else if name == "struct.type" then
      set s.advance
      let s' ← get
      if s'.peekTok == .langle then
        set s'.advance
        let s'' ← get
        match s''.peekTok with
        | .symName structName =>
          set s''.advance
          let s''' ← get
          set (skipAngleAux s''' 1)
          return .structTy structName
        | other => throw s!"{s''.peekPos}: expected @Name in struct type, got {other}"
      else throw s!"{s'.peekPos}: expected '<' after struct.type"
    else do
      set s.advance
      -- Skip optional angle-bracket parameters for other types (e.g., !array.type<...>)
      let s' ← get
      if s'.peekTok == .langle then
        set (skipAngleAux s'.advance 1)
      return .other name
  | .keyword k =>
    -- Handle bare MLIR builtin types like `index`, `i1`, `i32`, `none`
    if k == "index" || k == "none" || k.startsWith "i" || k.startsWith "f" then
      set s.advance
      return .other k
    else
      throw s!"{s.peekPos}: expected type (!...), got keyword '{k}'"
  | other => throw s!"{s.peekPos}: expected type (!...), got {other}"

/-- Try to parse a type, returning none if not a type token. -/
def tryParseType : Parser (Option Ty) := do
  let s ← get
  match s.peekTok with
  | .typeName _ =>
    try
      let ty ← parseType
      return some ty
    catch _ =>
      set s  -- restore state on failure
      return none
  | _ => return none

/-! ## Statement parsing -/

/-- Skip tokens until we hit a token that plausibly starts a new statement.
A new statement starts with: `%name = ...` (assignment), a statement-starting keyword,
`}` (end of block), or EOF.
We look ahead to distinguish `%name` as an argument (not followed by `=`)
from `%name =` as a new assignment. -/
private partial def skipToNextStmtAux (s : ParseState) : ParseState :=
  if s.atEnd then s
  else match s.peekTok with
  | .eof => s
  | .rbrace => s
  | .ssaName _ =>
    -- Check if next token after the SSA name is `=` → new statement
    let s' := s.advance
    if s'.atEnd then s
    else if s'.peekTok == .equals then s  -- `%name =` → new statement starts here
    else skipToNextStmtAux s'  -- `%name` used as argument, keep skipping
  | .keyword k =>
    -- Check if this keyword starts a statement
    if k == "felt.add" || k == "felt.sub" || k == "felt.mul" ||
       k == "felt.div" || k == "felt.neg" || k == "felt.inv" || k == "felt.const" ||
       k == "constrain.eq" || k == "function.return" ||
       k == "function.call" || k == "function.def" ||
       k == "struct.new" || k == "struct.readm" || k == "struct.writem" ||
       k == "struct.def" || k == "struct.member" || k == "llzk.nondet" ||
       k == "module" then s
    else skipToNextStmtAux s.advance
  | _ => skipToNextStmtAux s.advance

/-- Skip optional type annotations (`: !type` or `: (!type, !type) -> !type`).
Uses the same look-ahead logic as `skipToNextStmtAux` to avoid stopping
prematurely on SSA names that are arguments rather than new statements. -/
private partial def skipTypeAnnotationAux (s : ParseState) : ParseState :=
  if s.atEnd then s
  else match s.peekTok with
  | .eof => s
  | .rbrace => s
  | .ssaName _ =>
    let s' := s.advance
    if s'.atEnd then s
    else if s'.peekTok == .equals then s
    else skipTypeAnnotationAux s'
  | .keyword k =>
    if k == "felt.add" || k == "felt.sub" || k == "felt.mul" ||
       k == "felt.div" || k == "felt.neg" || k == "felt.inv" || k == "felt.const" ||
       k == "constrain.eq" || k == "function.return" ||
       k == "function.call" || k == "function.def" ||
       k == "struct.new" || k == "struct.readm" || k == "struct.writem" ||
       k == "struct.def" || k == "struct.member" || k == "llzk.nondet" ||
       k == "module" then s
    else skipTypeAnnotationAux s.advance
  | _ => skipTypeAnnotationAux s.advance

def skipTypeAnnotation : Parser Unit := do
  let s ← get
  if s.peekTok == .colon then
    set (skipTypeAnnotationAux s.advance)

/-- Skip braces with nesting. -/
private partial def skipBracesAux (s : ParseState) (depth : Nat) : ParseState :=
  if depth == 0 then s
  else if s.atEnd then s
  else match s.peekTok with
  | .lbrace => skipBracesAux s.advance (depth + 1)
  | .rbrace => skipBracesAux s.advance (depth - 1)
  | .eof => s
  | _ => skipBracesAux s.advance depth

/-- Scan tokens between `{` and `}` for the keyword `"llzk.pub"`.
    Returns `true` if found; consumes through the closing `}`.
    Any other tokens are silently skipped. -/
private partial def scanBracesForPub (s : ParseState) (depth : Nat) (found : Bool) :
    ParseState × Bool :=
  if depth == 0 then (s, found)
  else if s.atEnd then (s, found)
  else match s.peekTok with
       | .lbrace              => scanBracesForPub s.advance (depth + 1) found
       | .rbrace              => scanBracesForPub s.advance (depth - 1) found
       | .eof                 => (s, found)
       | .keyword "llzk.pub"  => scanBracesForPub s.advance depth true
       | _                    => scanBracesForPub s.advance depth found

/-- Parse optional `{llzk.pub}` attributes on a `struct.member`.
    Returns `true` if the attribute block was present and contained `llzk.pub`,
    `false` if absent or if it contained no `llzk.pub`.
    All other attribute tokens are silently ignored. -/
def parseIsPub : Parser Bool := do
  let s ← get
  if s.peekTok == .lbrace then
    let (s', found) := scanBracesForPub s.advance 1 false
    set s'
    return found
  else
    return false

/-- Skip optional attributes block `{ ... }`. -/
def skipAttributes : Parser Unit := do
  let _ ← parseIsPub

/-- Skip optional keyword `attributes` followed by `{ ... }`. -/
def skipAttributesKw : Parser Unit := do
  let s ← get
  match s.peekTok with
  | .keyword "attributes" =>
    set s.advance
    skipAttributes
  | _ => pure ()

/-- Parse a binary felt operation. -/
def parseFeltBinop (pos : Pos) (dest : SSAName)
    (mkStmt : Pos → SSAName → SSAName → SSAName → Stmt) : Parser Stmt := do
  let src1 ← expectSSAName
  expect .comma
  let src2 ← expectSSAName
  skipTypeAnnotation
  return mkStmt pos dest src1 src2

/-- Parse a felt.neg operation. -/
def parseFeltNeg (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let src ← expectSSAName
  skipTypeAnnotation
  return .feltNeg pos dest src

/-- Parse a felt.inv operation. -/
def parseFeltInv (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let src ← expectSSAName
  skipTypeAnnotation
  return .feltInv pos dest src

/-- Parse a felt.const operation.
Handles `felt.const 42`, `felt.const 42 <"babybear">`, and `felt.const 42 : !felt.type`. -/
def parseFeltConst (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let value ← expectIntLit
  -- Skip optional `<"fieldname">` (e.g., `<"babybear">`)
  let tok ← getPeek
  if tok == .langle then do
    let s ← get
    set (skipAngleAux s.advance 1)
  skipTypeAnnotation
  return .feltConst pos dest value

/-- Parse struct.new: `%dest = struct.new : !struct.type<@Name>` or shorthand `: <@Name>`. -/
def parseStructNew (pos : Pos) (dest : SSAName) : Parser Stmt := do
  expect .colon
  -- Handle shorthand `<@Name>` (without `!struct.type`)
  let tok ← getPeek
  if tok == .langle then
    advance  -- consume '<'
    let name ← expectSymName
    -- Consume the closing '>' (and nested angle content if present)
    let s ← get
    if s.peekTok == .rangle then
      set s.advance
    else
      set (skipAngleAux s 1)
    return .structNew pos dest name
  else
    let ty ← parseType
    match ty with
    | .structTy name => return .structNew pos dest name
    | _ => throw s!"{pos}: struct.new requires !struct.type<@Name>"

/-- Parse struct.readm: `%dest = struct.readm %self[@member] : ...` -/
def parseReadMember (pos : Pos) (dest : SSAName) : Parser Stmt := do
  let self ← expectSSAName
  expect .lbracket
  let member ← expectSymName
  expect .rbracket
  skipTypeAnnotation
  return .readMember pos dest self member

/-- Parse struct.writem: `struct.writem %self[@member] = %src : ...` -/
def parseWriteMember (pos : Pos) : Parser Stmt := do
  let self ← expectSSAName
  expect .lbracket
  let member ← expectSymName
  expect .rbracket
  expect .equals
  let src ← expectSSAName
  skipTypeAnnotation
  return .writeMember pos self member src

/-- Parse constrain.eq: `constrain.eq %a, %b : !felt.type` -/
def parseConstrainEq (pos : Pos) : Parser Stmt := do
  let src1 ← expectSSAName
  expect .comma
  let src2 ← expectSSAName
  skipTypeAnnotation
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
or void: `function.call @target(%args) : ...`
Handles qualified names like `@Mod::@func`. -/
def parseFuncCall (pos : Pos) (dest : Option SSAName) : Parser Stmt := do
  let mut target ← expectSymName
  -- Handle qualified names: @Mod::@func tokenizes as symName "Mod::" then symName "func"
  while (← getPeek) matches .symName _ do
    let part ← expectSymName
    target := target ++ part
  expect .lparen
  let firstTok ← getPeek
  let args ← if firstTok != .rparen then do
    let a ← expectSSAName
    parseArgsLoop [a]
  else
    pure []
  expect .rparen
  -- Skip optional template instantiation `{(%i)}` or similar
  let tok ← getPeek
  if tok == .lbrace then
    skipAttributes
  skipTypeAnnotation
  return .call pos dest target args

/-- Parse function.return: `function.return %v : ...` or `function.return` -/
def parseFuncReturn (pos : Pos) : Parser Stmt := do
  let tok ← getPeek
  match tok with
  | .ssaName _ =>
    let v ← expectSSAName
    skipTypeAnnotation
    return .funcReturn pos (some v)
  | _ => return .funcReturn pos none

/-- Parse llzk.nondet: `%dest = llzk.nondet : !felt.type` -/
def parseNondet (pos : Pos) (dest : SSAName) : Parser Stmt := do
  expect .colon
  let ty ← parseType
  match ty with
  | .felt => return .nondet pos dest
  | other => throw s!"{pos}: llzk.nondet with non-felt type ({repr other}) not supported"

/-- Parse a single statement. Returns None if we should skip (e.g., unsupported). -/
partial def parseStmt : Parser (Option Stmt) := do
  let pos ← getPos
  let tok ← getPeek
  match tok with
  | .eof => return none
  | .rbrace => return none
  | .ssaName dest => do
    advance  -- consume %dest
    expect .equals s!"{pos}: expected '=' after %{dest}"
    let opTok ← getPeek
    match opTok with
    | .keyword op =>
      advance  -- consume the op keyword
      match op with
      | "felt.add" => some <$> parseFeltBinop pos dest .feltAdd
      | "felt.sub" => some <$> parseFeltBinop pos dest .feltSub
      | "felt.mul" => some <$> parseFeltBinop pos dest .feltMul
      | "felt.div" => some <$> parseFeltBinop pos dest .feltDiv
      | "felt.neg" => some <$> parseFeltNeg pos dest
      | "felt.inv" => some <$> parseFeltInv pos dest
      | "felt.const" => some <$> parseFeltConst pos dest
      | "struct.new" => some <$> parseStructNew pos dest
      | "struct.readm" => some <$> parseReadMember pos dest
      | "function.call" => some <$> parseFuncCall pos (some dest)
      | "llzk.nondet" => some <$> parseNondet pos dest
      | _ =>
        warn s!"{pos}: skipping unsupported operation '{op}'"
        -- Skip remaining tokens until next statement starts
        let s ← get
        set (skipToNextStmtAux s)
        return some (.skipped pos op)
    | _ =>
      warn s!"{pos}: skipping unexpected token after '=': {opTok}"
      let s ← get
      set (skipToNextStmtAux s)
      return some (.skipped pos (toString opTok))
  | .keyword kw =>
    advance  -- consume the keyword
    match kw with
    | "struct.writem" => some <$> parseWriteMember pos
    | "constrain.eq" => some <$> parseConstrainEq pos
    | "function.call" => some <$> parseFuncCall pos none
    | "function.return" => some <$> parseFuncReturn pos
    | _ =>
      warn s!"{pos}: skipping unsupported keyword statement '{kw}'"
      -- Skip remaining tokens until next statement starts
      let s ← get
      set (skipToNextStmtAux s)
      return some (.skipped pos kw)
  | _ =>
    advance
    return some (.skipped pos (toString tok))

/-- Parse a function body (list of statements between `{` and `}`). -/
partial def parseBody : Parser (List Stmt) := do
  let tok ← getPeek
  match tok with
  | .rbrace => return []
  | .eof => return []
  | _ =>
    let stmt? ← parseStmt
    match stmt? with
    | some stmt => do
      let rest ← parseBody
      return stmt :: rest
    | none => return []

/-! ## Top-level declarations -/

/-- Parse comma-separated parameters until `)`. -/
private partial def parseParamsLoop (params : List ParamDecl) : Parser (List ParamDecl) := do
  let tok ← getPeek
  if tok == .comma then
    advance
    let name ← expectSSAName
    expect .colon
    let ty ← parseType
    parseParamsLoop (params ++ [{ name, ty }])
  else
    return params

/-- Parse a parameter list: `(%name: !type, %name: !type)`. -/
def parseParams : Parser (List ParamDecl) := do
  expect .lparen
  let tok ← getPeek
  let params ← if tok != .rparen then do
    let name ← expectSSAName
    expect .colon
    let ty ← parseType
    parseParamsLoop [{ name, ty }]
  else
    pure []
  expect .rparen
  return params

/-- Skip comma-separated multi-return types. -/
private partial def skipMultiRetLoop : Parser Unit := do
  let tok ← getPeek
  if tok == .comma then
    advance
    let _ ← parseType
    skipMultiRetLoop

/-- Parse a function definition:
`function.def @name(%params) -> !type attributes {...} { body }` -/
def parseFuncDef : Parser FuncDef := do
  let pos ← getPos
  expectKeyword "function.def"
  -- Skip optional `private` keyword
  let tok ← getPeek
  match tok with
  | .keyword "private" => advance
  | _ => pure ()
  let name ← expectSymName
  let params ← parseParams
  -- Optional return type: `-> !type`
  let mut retType : Option Ty := none
  let arrowTok ← getPeek
  if arrowTok == .arrow then
    advance
    let tok2 ← getPeek
    if tok2 == .lparen then
      -- Multi-return; parse first type, skip rest
      advance
      let ty ← parseType
      retType := some ty
      skipMultiRetLoop
      expect .rparen
    else
      let ty ← parseType
      retType := some ty
  -- Skip optional attributes
  skipAttributesKw
  -- Parse body
  expect .lbrace
  let body ← parseBody
  expect .rbrace
  return { name, params, returnType := retType, body, pos }

/-- Parse a member declaration: `struct.member @name : !type {llzk.pub}?` -/
def parseMemberDecl : Parser MemberDecl := do
  let pos ← getPos
  expectKeyword "struct.member"
  let name ← expectSymName
  expect .colon
  let ty ← parseType
  -- Parse optional attributes; returns true iff `{llzk.pub}` was present.
  let isPublic ← parseIsPub
  return { name, ty, isPublic, pos }

/-- Skip angle brackets with nesting, used for template params. -/
private partial def skipAngleParser : Parser Unit := do
  let s ← get
  if s.atEnd then return ()
  let tok ← getPeek
  match tok with
  | .langle => do advance; skipAngleParser; skipAngleParser
  | .rangle => advance
  | .eof => return ()
  | _ => do advance; skipAngleParser

/-- Parse members and functions inside a struct body. -/
private partial def parseStructBody (members : List MemberDecl) (funcs : List FuncDef) :
    Parser (List MemberDecl × List FuncDef) := do
  let tok ← getPeek
  match tok with
  | .rbrace => return (members, funcs)
  | .eof => return (members, funcs)
  | .keyword "struct.member" =>
    let m ← parseMemberDecl
    parseStructBody (members ++ [m]) funcs
  | .keyword "function.def" =>
    let f ← parseFuncDef
    parseStructBody members (funcs ++ [f])
  | _ =>
    warn s!"{(← getPos)}: unexpected token in struct body: {tok}, skipping"
    advance
    parseStructBody members funcs

/-- Parse a struct definition:
`struct.def @Name { members... functions... }` -/
def parseStructDef : Parser StructDef := do
  let pos ← getPos
  expectKeyword "struct.def"
  let name ← expectSymName
  -- Skip optional template parameters `<[...]>`
  let tok ← getPeek
  if tok == .langle then
    warn s!"{pos}: struct '{name}' has template parameters — templates not supported, \
skipping parameters"
    advance
    skipAngleParser
  expect .lbrace
  let (members, funcs) ← parseStructBody [] []
  expect .rbrace
  return { name, members, funcs, pos }

/-- Parse struct definitions, nested modules, and free functions at module level. -/
private partial def parseModuleBody (structs : List StructDef) (freeFuncs : List FuncDef) :
    Parser (List StructDef × List FuncDef) := do
  let tok ← getPeek
  match tok with
  | .rbrace => return (structs, freeFuncs)
  | .eof => return (structs, freeFuncs)
  | .keyword "struct.def" =>
    let sd ← parseStructDef
    parseModuleBody (structs ++ [sd]) freeFuncs
  | .keyword "module" =>
    let nested ← parseModule
    parseModuleBody (structs ++ nested.structs) (freeFuncs ++ nested.freeFuncs)
  | .keyword "function.def" =>
    let f ← parseFuncDef
    parseModuleBody structs (freeFuncs ++ [f])
  | _ =>
    warn s!"{(← getPos)}: unexpected token at module level: {tok}, skipping"
    advance
    parseModuleBody structs freeFuncs
where
  /-- Parse a top-level or nested module.
  Handles `module { ... }`, `module attributes {...} { ... }`,
  and `module @Name attributes {...} { ... }`. -/
  parseModule : Parser Module := do
    let pos ← getPos
    expectKeyword "module"
    -- Skip optional module name `@Name`
    let tok ← getPeek
    match tok with
    | .symName _ => advance
    | _ => pure ()
    skipAttributesKw
    expect .lbrace
    let (structs, freeFuncs) ← parseModuleBody [] []
    expect .rbrace
    return { structs, freeFuncs, pos }

/-- Parse a top-level module. Handles optional `@name` after `module`. -/
def parseModule : Parser Module := do
  let pos ← getPos
  expectKeyword "module"
  -- Skip optional module name `@Name`
  let tok ← getPeek
  match tok with
  | .symName _ => advance
  | _ => pure ()
  skipAttributesKw
  expect .lbrace
  let (structs, freeFuncs) ← parseModuleBody [] []
  expect .rbrace
  return { structs, freeFuncs, pos }

/-! ## Entry point -/

/-- Split input on `// -----` separators (used by LLZK test infrastructure). -/
private def splitSections (input : String) : List String :=
  let lines := input.splitOn "\n"
  let rec go (acc : List String) (cur : List String) : List String → List String
    | [] =>
      let seg := "\n".intercalate cur.reverse
      if seg.trimAscii.isEmpty then acc.reverse else (acc ++ [seg]).reverse
    | l :: ls =>
      if l.trimAsciiStart.startsWith "// -----" || l.trimAsciiStart.startsWith "//-----" then
        let seg := "\n".intercalate cur.reverse
        let acc' := if seg.trimAscii.isEmpty then acc else acc ++ [seg]
        go acc' [] ls
      else
        go acc (l :: cur) ls
  go [] [] lines

/-- Parse a single section: either a `module { ... }` or bare declarations. -/
private partial def parseSection (tokens : List PosToken) :
    Except String (Module × List String) := do
  let s := ParseState.init tokens
  let (mod, s') ← (do
    let tok ← getPeek
    match tok with
    | .keyword "module" => parseModule
    | .keyword "struct.def" =>
      -- Bare struct at top level (no module wrapper)
      let pos ← getPos
      let (structs, freeFuncs) ← parseBareTopLevel [] []
      return { structs, freeFuncs, pos }
    | .keyword "function.def" =>
      let pos ← getPos
      let (structs, freeFuncs) ← parseBareTopLevel [] []
      return { structs, freeFuncs, pos }
    | .eof => return { structs := [], freeFuncs := [], pos := ⟨0, 0⟩ }
    | other =>
      let pos ← getPos
      throw s!"{pos}: expected 'module' or 'struct.def', got {other}"
    ).run s
  return (mod, s'.warnings)
where
  parseBareTopLevel (structs : List StructDef) (freeFuncs : List FuncDef) :
      Parser (List StructDef × List FuncDef) := do
    let tok ← getPeek
    match tok with
    | .eof => return (structs, freeFuncs)
    | .keyword "struct.def" =>
      let sd ← parseStructDef
      parseBareTopLevel (structs ++ [sd]) freeFuncs
    | .keyword "function.def" =>
      let f ← parseFuncDef
      parseBareTopLevel structs (freeFuncs ++ [f])
    | .keyword "module" =>
      let mod ← parseModule
      parseBareTopLevel (structs ++ mod.structs) (freeFuncs ++ mod.freeFuncs)
    | _ =>
      warn s!"{(← getPos)}: unexpected token at top level: {tok}, skipping"
      advance
      parseBareTopLevel structs freeFuncs

/-- Parse an LLZK source string into a Module AST.
Handles `// -----` split-input-file separators by parsing each section
independently and merging the resulting structs. -/
def parse (input : String) : Except String (Module × List String) := do
  let sections := splitSections input
  let mut allStructs : List StructDef := []
  let mut allFreeFuncs : List FuncDef := []
  let mut allWarnings : List String := []
  for sect in sections do
    let tokens ← tokenize sect
    -- Skip sections that are only CHECK/RUN comments (empty after tokenization)
    let nonEof := tokens.filter fun pt => pt.tok != .eof
    if nonEof.isEmpty then continue
    match ← parseSection tokens with
    | (mod, warnings) =>
      allStructs := allStructs ++ mod.structs
      allFreeFuncs := allFreeFuncs ++ mod.freeFuncs
      allWarnings := allWarnings ++ warnings
  return ({ structs := allStructs, freeFuncs := allFreeFuncs, pos := ⟨1, 1⟩ }, allWarnings)

end LLZK
