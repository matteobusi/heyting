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
import Heyting.Core.StructuralPass

import Heyting.Dialects.Felt
import Heyting.Dialects.ConstrainEq
import Heyting.Dialects.Call
import Heyting.Dialects.StructObject
import Heyting.Dialects.Oracle
import Heyting.Dialects.WitnessExecution
import Heyting.Dialects.TypedSourceSemantics
import Heyting.Dialects.OracleErasure
import Heyting.Dialects.CallPass
import Heyting.Dialects.CallErasure
import Heyting.Dialects.ObjectResidualSemantics
import Heyting.Dialects.ObjectCallSemantics
import Heyting.Dialects.StructObjectPass
import Heyting.Dialects.CallSemantics
import Heyting.Dialects.FeltPass
import Heyting.Dialects.R1CSLike
import Heyting.Dialects.R1CSLikePass

import Heyting.Languages.FlatIR
import Heyting.Languages.R1CS
import Heyting.Languages.StructIR

import Heyting.Core.TrinitaryCC
import Heyting.Core.WitnessCodec
import Heyting.Core.WitnessSemantics

import Heyting.Passes.FlatIRToR1CS
import Heyting.Passes.FlatIRWitnessCodec
import Heyting.Passes.FlatIRCompact
import Heyting.Passes.StructIRToFlatIR
import Heyting.Legacy.Pipeline
import Heyting.Passes.Tactics
import Heyting.Passes.Lowering
import Heyting.Passes.ASTToDialect
import Heyting.Passes.DialectPipeline

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
