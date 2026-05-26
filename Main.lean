/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.CLI

/-!
# Main

Executable entry point forwarding to `Heyting.CLI.main`.
-/

def main (args : List String) : IO Unit :=
  Heyting.CLI.main args
