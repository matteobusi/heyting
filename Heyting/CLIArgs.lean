/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-! Lightweight CLI argument parser for Heyting.

This module provides a small, dependency-free parser that supports:
- subcommand (first non-flag positional argument)
- positional args (input, output)
- boolean flags (e.g. --json, --auto)
- options with values (e.g. --input <path>, --prime-field <name>)

We avoid pulling external libraries to keep the build hermetic. The
parser is intentionally conservative and returns `Except String` on
invalid input so the caller can print a friendly error message.
-/

namespace Heyting.CLIArgs

/-- Parsed CLI options before command dispatch. -/
structure Options where
  cmd : String := ""
  llzk? : Option String := none
  output? : Option String := none
  json : Bool := false
  auto : Bool := false
  /-- Path to a JSON file of public circuit inputs (field elements). -/
  input? : Option String := none
  /-- Path to a JSON array supplying `llzk.nondet` values. -/
  oracle? : Option String := none
  prime? : Option String := none
  deriving Repr

/-- Parse one option payload, returning the value together with the remaining args. -/
def parseOptionWithValue (args : List String) : Except String (String × List String) :=
  match args with
  | [] => .error "expected value after option"
  | v :: rest => .ok (v, rest)

/-- Parse CLI args into Options. Accepts arbitrary ordering of flags.
    First positional (non-flag) token is taken as the command. Next two
    positional tokens (if present) are interpreted as the .llzk source file
    and output path respectively. -/
partial def parse (rawArgs : List String) : Except String Options :=
  let rec loop (acc : Options) (positional : List String)
      (rem : List String) : Except String Options :=
    match rem with
    | [] =>
      -- Fill in positional inputs if not already present
      let acc := match positional with
        | [] => acc
        | [a] =>
            if acc.cmd == "" then
              { acc with cmd := a }
            else if acc.llzk?.isNone then
              { acc with llzk? := some a }
            else
              acc
        | [a, b] =>
          let acc :=
            if acc.cmd == "" then
              { acc with cmd := a }
            else if acc.llzk?.isNone then
              { acc with llzk? := some a }
            else
              acc
          let acc := if acc.output?.isNone then { acc with output? := some b } else acc
          acc
        | a :: b :: rest =>
          -- Extra positionals are ignored after assigning command, source, and output.
          let acc := if acc.cmd == "" then { acc with cmd := a } else acc
          let acc := if acc.llzk?.isNone then { acc with llzk? := some b } else acc
          let acc := if acc.output?.isNone then { acc with output? := some rest.head! } else acc
          acc
      .ok acc
    | tok :: rest =>
      if tok.startsWith "--" then
        match tok with
        | "--json" => loop { acc with json := true } positional rest
        | "--auto" => loop { acc with auto := true } positional rest
        | "--input" =>
          match parseOptionWithValue rest with
          | .error e => .error s!"{tok}: {e}"
          | .ok (v, rest') => loop { acc with input? := some v } positional rest'
        | "--oracle" =>
          match parseOptionWithValue rest with
          | .error e => .error s!"{tok}: {e}"
          | .ok (v, rest') => loop { acc with oracle? := some v } positional rest'
        | "--prime-field" =>
          match parseOptionWithValue rest with
          | .error e => .error s!"{tok}: {e}"
          | .ok (v, rest') => loop { acc with prime? := some v } positional rest'
        | "--output" | "--out" =>
          match parseOptionWithValue rest with
          | .error e => .error s!"{tok}: {e}"
          | .ok (v, rest') => loop { acc with output? := some v } positional rest'
        | _ => .error s!"unknown option: {tok}"
      else
        -- positional argument
        loop acc (positional ++ [tok]) rest
  loop {} [] rawArgs

end Heyting.CLIArgs
