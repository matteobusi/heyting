import Heyting.CLIArgs

namespace Heyting.CLIArgs.Tests

def parsedDialect : Bool :=
  match parse ["compile", "input.llzk", "out", "--dialect"] with
  | .ok opts => opts.cmd == "compile" && opts.llzk? == some "input.llzk" &&
      opts.output? == some "out" && opts.dialect
  | .error _ => false

#guard parsedDialect

def legacyUnchanged : Bool :=
  match parse ["compile", "input.llzk", "out"] with
  | .ok opts => !opts.dialect && !opts.legacy
  | .error _ => false

#guard legacyUnchanged

def parsedLegacy : Bool :=
  match parse ["compile", "input.llzk", "out", "--legacy"] with
  | .ok opts => opts.legacy && !opts.dialect
  | .error _ => false

#guard parsedLegacy

def parsedOracle : Bool :=
  match parse ["compile", "input.llzk", "out", "--auto", "--oracle", "oracle.json"] with
  | .ok opts => opts.auto && opts.oracle? == some "oracle.json"
  | .error _ => false

#guard parsedOracle

end Heyting.CLIArgs.Tests
