/-
Copyright (c) 2025 Heyting Authors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Matteo Busi
-/
import Heyting.Core.Pass
import Heyting.Core.VarIdEncoding
import Heyting.Languages.StructInlineIR
import Heyting.Languages.MemberlessIR

namespace StructInlineIRToMemberlessIR

open StructInlineIR MemberlessIR

variable {F : Type} [Field F] {n : Nat}

def compileStmt {n : Nat} {F : Type} [Field F] {i : Fin n}
    (stmt : StructInlineIR.ConstrainStmt n F) : MemberlessIR.Stmt n i F :=
  match stmt with
  | .feltAdd dest src1 src2 => .feltAdd dest src1 src2
  | .feltSub dest src1 src2 => .feltSub dest src1 src2
  | .feltMul dest src1 src2 => .feltMul dest src1 src2
  | .feltDiv dest src1 src2 => .feltDiv dest src1 src2
  | .feltNeg dest src => .feltNeg dest src
  | .feltConst dest c => .feltConst dest c
  | .constrainEq src1 src2 => .constrainEq src1 src2
  | .readMember dest self member => .constrainEq dest (Nat.pair self member)

def compileStmts {n : Nat} {F : Type} [Field F] {i : Fin n}
    (stmts : List (StructInlineIR.ConstrainStmt n F)) :
    List (MemberlessIR.Stmt n i F) :=
  stmts.map compileStmt

def compileFunc (i : Fin n) (f : StructInlineIR.StructDef n F) : MemberlessIR.Func n i F where
  numParams := f.constrain.numParams
  body := compileStmts (i := i) f.constrain.body

def compile (m : StructInlineIR.Module (n + 1) F) : MemberlessIR.Module (n + 1) F :=
  fun i => compileFunc i (m i)

def compileWitness (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) : Nat → F :=
  let _ := m
  fun k => ws (VarIdEncoding.decode k)

def extractWitness (m : StructInlineIR.Module (n + 1) F)
    (mw : Nat → F) : StructInlineIR.Witness F :=
  let _ := m
  fun vid => mw (VarIdEncoding.encode vid)

def witnessRel (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) (mw : Nat → F) : Prop :=
  let _ := m
  ∀ k, mw k = compileWitness m ws k

omit [Field F] in
theorem witnessRel_compileWitness (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) :
    witnessRel m ws (compileWitness m ws) := by
  intro k
  rfl

omit [Field F] in
theorem compileWitness_extractWitness (m : StructInlineIR.Module (n + 1) F)
    (mw : Nat → F) :
    compileWitness m (extractWitness m mw) = mw := by
  funext k
  simp [compileWitness, extractWitness, VarIdEncoding.encode_decode]

omit [Field F] in
theorem extractWitness_compileWitness (m : StructInlineIR.Module (n + 1) F)
    (ws : StructInlineIR.Witness F) :
    extractWitness m (compileWitness m ws) = ws := by
  funext v
  simp [compileWitness, extractWitness, VarIdEncoding.decode_encode]

instance Pass (n : Nat) (F : Type) [Field F] :
    Pass (StructInlineIR.Language n F) (MemberlessIR.instLanguage n F) where
  compile := compile
  witnessRel := witnessRel

end StructInlineIRToMemberlessIR
