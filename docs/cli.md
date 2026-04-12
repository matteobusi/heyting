---
title: Hey CLI
---

Overview

The Heyting compiler provides a small command-line interface via the `hey` executable. The CLI is deliberately minimal while the project evolves. The main command is `compile`, which emits an R1CS JSON file from an LLZK input.

Usage

  hey compile [options] <input.llzk> <output>
  hey help

Options

- `--json`
  Produce a human-readable R1CS JSON file (default behavior of `compile`).

- `--witness <path>`
  Use a user-supplied witness JSON file to populate StructIR witness values. (Not implemented yet — passing this option will raise an informative error.)

- `--auto`
  Automatically run compute bodies to produce a witness from the program's `compute` functions. (Not implemented yet — this is planned and passing the flag will raise an informative error.)

Examples

  lake exe hey compile example.llzk out/system.json

Notes on features not yet implemented

- Witness generation from compute bodies (`--auto`) is a staged feature. The project will implement a pure Lean interpreter for StructIR compute bodies first (so proofs can be added later), followed by an optional native codegen path for performance. Until then, `--auto` raises an explanatory error.

- User-supplied witness loading (`--witness`) will accept a JSON array of entries in the form `{ "path": [ints], "member": int, "value": "repr" }`. The `value` field uses the same stringified field representation as the R1CS JSON output. Until implemented, the CLI raises an explanatory error when `--witness` is used.

Where to find the CLI code

  Heyting/CLI.lean
