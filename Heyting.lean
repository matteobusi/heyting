/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Heyting.Core.Language
import Heyting.Core.Pass
import Heyting.Core.VarIdEncoding
import Heyting.Core.Dialect
import Heyting.Core.Semantics
import Heyting.Core.Module
import Heyting.Core.ModuleSemantics
import Heyting.Core.DialectPass

import Heyting.Dialects.Felt
import Heyting.Dialects.ConstrainEq
import Heyting.Dialects.Call
import Heyting.Dialects.CallPass
import Heyting.Dialects.FeltPass

import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Languages.StructIR

import Heyting.Core.TrinitaryCC

import Heyting.Passes.FlatIRToR1CS
import Heyting.Passes.FlatIRCompact
import Heyting.Passes.StructIRToFlatIR
import Heyting.Passes.Pipeline
import Heyting.Passes.Tactics
import Heyting.Passes.Lowering

import Heyting.Parsers.Main

import Heyting.Backends.R1CSJSON
import Heyting.Backends.FieldBytes
import Heyting.Backends.R1CSBinary
import Heyting.Backends.WitnessBinary
import Heyting.CLI

/-!
# Heyting

Umbrella import for core languages, passes, parsers, backends, and CLI.
-/
