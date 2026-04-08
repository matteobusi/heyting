import Heyting.Parser.AST

/-!
# LLZK Tokenizer

Converts a string of LLZK MLIR textual IR into a token stream.
Handles MLIR-specific tokens: `%var`, `@name` (including quoted `@"name"`),
`!type`, numeric literals, keywords, and punctuation.
-/

namespace LLZK

/-! ## Token types -/

/-- Token type for LLZK MLIR. -/
inductive Token where
  | ssaName (name : String)     -- `%foo`, `%0`
  | symName (name : String)     -- `@foo`, `@"$super"`
  | typeName (name : String)    -- `!felt.type`, `!struct.type`
  | intLit (value : Int)        -- `42`, `-1`
  | keyword (kw : String)       -- `module`, `struct.def`, `felt.add`, etc.
  | lparen                      -- `(`
  | rparen                      -- `)`
  | lbrace                      -- `{`
  | rbrace                      -- `}`
  | langle                      -- `<`
  | rangle                      -- `>`
  | lbracket                    -- `[`
  | rbracket                    -- `]`
  | comma                       -- `,`
  | colon                       -- `:`
  | equals                      -- `=`
  | arrow                       -- `->`
  | eof
  deriving Repr, Inhabited

instance : BEq Token where
  beq a b := match a, b with
    | .ssaName n1, .ssaName n2 => n1 == n2
    | .symName n1, .symName n2 => n1 == n2
    | .typeName n1, .typeName n2 => n1 == n2
    | .intLit v1, .intLit v2 => v1 == v2
    | .keyword k1, .keyword k2 => k1 == k2
    | .lparen, .lparen => true
    | .rparen, .rparen => true
    | .lbrace, .lbrace => true
    | .rbrace, .rbrace => true
    | .langle, .langle => true
    | .rangle, .rangle => true
    | .lbracket, .lbracket => true
    | .rbracket, .rbracket => true
    | .comma, .comma => true
    | .colon, .colon => true
    | .equals, .equals => true
    | .arrow, .arrow => true
    | .eof, .eof => true
    | _, _ => false

instance : ToString Token where
  toString
    | .ssaName n => s!"%{n}"
    | .symName n => s!"@{n}"
    | .typeName n => s!"!{n}"
    | .intLit v => toString v
    | .keyword k => k
    | .lparen => "("
    | .rparen => ")"
    | .lbrace => "{"
    | .rbrace => "}"
    | .langle => "<"
    | .rangle => ">"
    | .lbracket => "["
    | .rbracket => "]"
    | .comma => ","
    | .colon => ":"
    | .equals => "="
    | .arrow => "->"
    | .eof => "<eof>"

/-- A token with source position. -/
structure PosToken where
  tok : Token
  pos : Pos
  deriving Repr

/-! ## Tokenizer -/

/-- Character classification helpers. -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '.' || c == '$'

private def isIdentStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '.'

-- Tokenizer operates on a substring represented by (input, offset, line, col).
-- All functions take and return this 4-tuple to avoid structure issues.

/-- Get character at position, or null if past end. -/
private def charAt (input : String) (offset : Nat) : Char :=
  if h : offset < input.length then
    input.toList[offset]
  else '\x00'

/-- Check if offset is past end of input. -/
private def pastEnd (input : String) (offset : Nat) : Bool :=
  offset >= input.length

/-- Advance offset by one character, updating line/col. -/
private def advanceOne (input : String) (offset line col : Nat) : Nat × Nat × Nat :=
  if pastEnd input offset then (offset, line, col)
  else
    let c := charAt input offset
    if c == '\n' then (offset + 1, line + 1, 1)
    else (offset + 1, line, col + 1)

/-- Skip whitespace characters. -/
private def skipWhitespace (input : String) (offset line col : Nat) :
    Nat × Nat × Nat :=
  if pastEnd input offset then (offset, line, col)
  else
    let c := charAt input offset
    if c == ' ' || c == '\t' || c == '\r' then
      skipWhitespace input (offset + 1) line (col + 1)
    else if c == '\n' then
      skipWhitespace input (offset + 1) (line + 1) 1
    else (offset, line, col)
termination_by input.length - offset
decreasing_by all_goals simp [pastEnd] at *; omega

/-- Skip to end of line (for line comments). -/
private def skipToEOL (input : String) (offset line col : Nat) :
    Nat × Nat × Nat :=
  if pastEnd input offset then (offset, line, col)
  else
    let c := charAt input offset
    if c == '\n' then (offset + 1, line + 1, 1)
    else skipToEOL input (offset + 1) line (col + 1)
termination_by input.length - offset
decreasing_by all_goals simp [pastEnd] at *; omega

/-- Skip whitespace and `//` line comments. -/
private partial def skipWS (input : String) (offset line col : Nat) :
    Nat × Nat × Nat :=
  let (o, l, c) := skipWhitespace input offset line col
  if pastEnd input o then (o, l, c)
  else if charAt input o == '/' && !pastEnd input (o + 1) && charAt input (o + 1) == '/' then
    let (o', l', c') := skipToEOL input (o + 2) l (c + 2)
    skipWS input o' l' c'
  else (o, l, c)

/-- Read an identifier: letters, digits, underscores, dots, `$`.
Also handles `::` namespace separators. -/
private def readIdent (input : String) (offset : Nat) (acc : String := "") :
    String × Nat :=
  if pastEnd input offset then (acc, offset)
  else
    let c := charAt input offset
    if isIdentChar c then
      readIdent input (offset + 1) (acc.push c)
    else if c == ':' && !pastEnd input (offset + 1) && charAt input (offset + 1) == ':' then
      readIdent input (offset + 2) (acc ++ "::")
    else (acc, offset)
termination_by input.length - offset
decreasing_by all_goals simp [pastEnd] at *; omega

/-- Read a quoted name after the opening `"`. -/
private def readQuoted (input : String) (offset : Nat) (acc : String := "") :
    String × Nat :=
  if pastEnd input offset then (acc, offset)
  else
    let c := charAt input offset
    if c == '"' then (acc, offset + 1)
    else if c == '\\' && !pastEnd input (offset + 1) then
      readQuoted input (offset + 2) (acc.push (charAt input (offset + 1)))
    else readQuoted input (offset + 1) (acc.push c)
termination_by input.length - offset
decreasing_by all_goals simp [pastEnd] at *; omega

/-- Read digits for a numeric literal. -/
private def readDigits (input : String) (offset : Nat) (acc : String := "") :
    String × Nat :=
  if pastEnd input offset then (acc, offset)
  else
    let c := charAt input offset
    if c.isDigit then readDigits input (offset + 1) (acc.push c)
    else (acc, offset)
termination_by input.length - offset
decreasing_by all_goals simp [pastEnd] at *; omega

/-- Read a type name: identifier chars after `!`. -/
private def readTypeName (input : String) (offset : Nat) (acc : String := "") :
    String × Nat :=
  if pastEnd input offset then (acc, offset)
  else
    let c := charAt input offset
    if isIdentChar c then readTypeName input (offset + 1) (acc.push c)
    else (acc, offset)
termination_by input.length - offset
decreasing_by all_goals simp [pastEnd] at *; omega

/-- Produce the next token from the input at the given position. -/
def nextToken (input : String) (offset line col : Nat) :
    Except String (PosToken × Nat × Nat × Nat) := do
  let (o, l, c) := skipWS input offset line col
  if pastEnd input o then
    return ({ tok := .eof, pos := ⟨l, c⟩ }, o, l, c)
  let pos : Pos := ⟨l, c⟩
  let ch := charAt input o
  match ch with
  | '%' =>
    let (name, o') := readIdent input (o + 1)
    let colEnd := c + 1 + name.length
    if name.isEmpty then .error s!"{pos}: unexpected '%'"
    else return ({ tok := .ssaName name, pos }, o', l, colEnd)
  | '@' =>
    if !pastEnd input (o + 1) && charAt input (o + 1) == '"' then
      let (name, o') := readQuoted input (o + 2)
      let colEnd := c + 3 + name.length  -- approximate
      return ({ tok := .symName name, pos }, o', l, colEnd)
    else
      let (name, o') := readIdent input (o + 1)
      let colEnd := c + 1 + name.length
      if name.isEmpty then .error s!"{pos}: unexpected '@'"
      else return ({ tok := .symName name, pos }, o', l, colEnd)
  | '!' =>
    let (name, o') := readTypeName input (o + 1)
    let colEnd := c + 1 + name.length
    if name.isEmpty then .error s!"{pos}: unexpected '!'"
    else return ({ tok := .typeName name, pos }, o', l, colEnd)
  | '(' => return ({ tok := .lparen, pos }, o + 1, l, c + 1)
  | ')' => return ({ tok := .rparen, pos }, o + 1, l, c + 1)
  | '{' => return ({ tok := .lbrace, pos }, o + 1, l, c + 1)
  | '}' => return ({ tok := .rbrace, pos }, o + 1, l, c + 1)
  | '<' => return ({ tok := .langle, pos }, o + 1, l, c + 1)
  | '>' => return ({ tok := .rangle, pos }, o + 1, l, c + 1)
  | '[' => return ({ tok := .lbracket, pos }, o + 1, l, c + 1)
  | ']' => return ({ tok := .rbracket, pos }, o + 1, l, c + 1)
  | ',' => return ({ tok := .comma, pos }, o + 1, l, c + 1)
  | ':' => return ({ tok := .colon, pos }, o + 1, l, c + 1)
  | '=' => return ({ tok := .equals, pos }, o + 1, l, c + 1)
  | '#' =>
    -- Hash-prefixed tokens like `#felt.field<...>`, treat as keyword
    let (ident, o') := readIdent input (o + 1)
    let colEnd := c + 1 + ident.length
    return ({ tok := .keyword (s!"#{ident}"), pos }, o', l, colEnd)
  | '"' =>
    -- Quoted string literal, emit as keyword (used in attributes)
    let (str, o') := readQuoted input (o + 1)
    let colEnd := c + 2 + str.length  -- approximate
    return ({ tok := .keyword s!"\"{str}\"", pos }, o', l, colEnd)
  | '-' =>
    if !pastEnd input (o + 1) && charAt input (o + 1) == '>' then
      return ({ tok := .arrow, pos }, o + 2, l, c + 2)
    else if !pastEnd input (o + 1) && (charAt input (o + 1)).isDigit then
      let (digits, o') := readDigits input (o + 1)
      match digits.toInt? with
      | some n => return ({ tok := .intLit (-n), pos }, o', l, c + 1 + digits.length)
      | none => .error s!"{pos}: invalid number '-{digits}'"
    else .error s!"{pos}: unexpected '-'"
  | _ =>
    if ch.isDigit then
      let (digits, o') := readDigits input o
      match digits.toInt? with
      | some n => return ({ tok := .intLit n, pos }, o', l, c + digits.length)
      | none => .error s!"{pos}: invalid number '{digits}'"
    else if isIdentStartChar ch then
      let (ident, o') := readIdent input o
      return ({ tok := .keyword ident, pos }, o', l, c + ident.length)
    else .error s!"{pos}: unexpected character '{ch}'"

/-- Tokenize an entire input string into a list of tokens. -/
partial def tokenize (input : String) : Except String (List PosToken) := do
  let mut offset := 0
  let mut line := 1
  let mut col := 1
  let mut tokens : List PosToken := []
  let mut done := false
  while !done do
    let (pt, o', l', c') ← nextToken input offset line col
    tokens := tokens ++ [pt]
    if pt.tok == .eof then done := true
    else
      offset := o'
      line := l'
      col := c'
  return tokens

end LLZK
