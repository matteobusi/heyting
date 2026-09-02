import Heyting.Dialects.CallSemantics
import Mathlib.Algebra.Field.Rat

namespace Dialect.CallPass.Tests

open Dialect
open Dialect.CallPass
open Dialect.CallSemantics

abbrev F := ℚ

def ix0 : Fin 2 := ⟨0, by omega⟩
def ix1 : Fin 2 := ⟨1, by omega⟩
def target0 : Fin ix1.val := ⟨0, by simp [ix1]⟩

def callee : StructDef SourceSet 2 ix0 F where
  name := "double"
  members := []
  compute := {
    numParams := 1
    body := [.op feltSourceIx (.add 1 0 0)]
    returnVar := some 1
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def caller : StructDef SourceSet 2 ix1 F where
  name := "caller"
  members := []
  compute := {
    numParams := 1
    body := [.op callSourceIx (.call (some 1) target0 0 [0])]
    returnVar := some 1
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def directModule : Module SourceSet 2 F where
  structs
    | ⟨0, _⟩ => callee
    | ⟨1, _⟩ => caller

#guard (eraseComputeFunc directModule ix1).map
    (fun result => (result.1.map Stmt.dest, result.1.map Stmt.reads, result.2)) ==
  some ([some 3, some 4, some 1], [[0, 0], [], [3, 4]], 5)

def inputEnv : LocalVar → F := fun v => if v = 0 then 3 else 0

#guard (CallSemantics.evalComputeBody directModule ix1 caller.compute.body inputEnv).map
    (fun env => env 1) == some 6

#guard (eraseComputeFunc directModule ix1).bind
    (fun result => (CallSemantics.evalTargetComputeBody result.1 inputEnv).map
      (fun env => env 1)) == some 6

def badSelectorBody : List (Stmt SourceSet ⟨2, ix1.val, 0⟩ F) :=
  [.op callSourceIx (.call (some 1) target0 1 [0])]

#guard (eraseBodyInto (callerMembers := 0) directModule ix1 ix1 .compute id 2
  badSelectorBody).isNone

def badArityBody : List (Stmt SourceSet ⟨2, ix1.val, 0⟩ F) :=
  [.op callSourceIx (.call (some 1) target0 0 [])]

#guard (eraseBodyInto (callerMembers := 0) directModule ix1 ix1 .compute id 2
  badArityBody).isNone

def ix30 : Fin 3 := ⟨0, by omega⟩
def ix31 : Fin 3 := ⟨1, by omega⟩
def ix32 : Fin 3 := ⟨2, by omega⟩
def target30 : Fin ix31.val := ⟨0, by simp [ix31]⟩
def target31 : Fin ix32.val := ⟨1, by simp [ix32]⟩

def nestedLeaf : StructDef SourceSet 3 ix30 F where
  name := "leaf"
  members := []
  compute := {
    numParams := 1
    body := [.op feltSourceIx (.add 1 0 0)]
    returnVar := some 1
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def nestedMiddle : StructDef SourceSet 3 ix31 F where
  name := "middle"
  members := []
  compute := {
    numParams := 1
    body := [.op callSourceIx (.call (some 1) target30 0 [0])]
    returnVar := some 1
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def nestedRoot : StructDef SourceSet 3 ix32 F where
  name := "root"
  members := []
  compute := {
    numParams := 1
    body := [.op callSourceIx (.call (some 1) target31 0 [0])]
    returnVar := some 1
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def nestedModule : Module SourceSet 3 F where
  structs
    | ⟨0, _⟩ => nestedLeaf
    | ⟨1, _⟩ => nestedMiddle
    | ⟨2, _⟩ => nestedRoot

#guard (eraseComputeFunc nestedModule ix32).map
    (fun result => (result.1.map Stmt.dest, result.1.map Stmt.reads, result.2)) ==
  some
    ([some 5, some 6, some 3, some 7, some 1],
     [[0, 0], [], [5, 6], [], [3, 7]], 8)

#guard (CallSemantics.evalComputeBody nestedModule ix32 nestedRoot.compute.body inputEnv).map
    (fun env => env 1) == some 6

#guard (eraseComputeFunc nestedModule ix32).bind
    (fun result => (CallSemantics.evalTargetComputeBody result.1 inputEnv).map
      (fun env => env 1)) == some 6

/-! Return-through-parameter: copy must read caller argument, not fresh storage. -/

def returnParamCallee : StructDef SourceSet 2 ix0 F where
  name := "return_param"
  members := []
  compute := {
    numParams := 1
    body := []
    returnVar := some 0
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def returnParamModule : Module SourceSet 2 F where
  structs
    | ⟨0, _⟩ => returnParamCallee
    | ⟨1, _⟩ => caller

#guard (CallSemantics.evalComputeBody returnParamModule ix1 caller.compute.body inputEnv).map
    (fun env => env 1) == some 3

#guard (eraseComputeFunc returnParamModule ix1).bind
    (fun result => (CallSemantics.evalTargetComputeBody result.1 inputEnv).map
      (fun env => env 1)) == some 3

def undefinedReturnCallee : StructDef SourceSet 2 ix0 F where
  name := "undefined_return"
  members := []
  compute := {
    numParams := 1
    body := []
    returnVar := some 1
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := []
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def undefinedReturnModule : Module SourceSet 2 F where
  structs
    | ⟨0, _⟩ => undefinedReturnCallee
    | ⟨1, _⟩ => caller

#guard (eraseComputeFunc undefinedReturnModule ix1).isNone

/-! Constraint call: callee-local arithmetic feeds its emitted equality. -/

def constrainCallee : StructDef SourceSet 2 ix0 F where
  name := "equals_six"
  members := []
  compute := {
    numParams := 1
    body := []
    returnVar := some 0
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := [
      .op feltSourceIx (.const 1 6),
      .op constrSourceIx (.eq 0 1)]
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def constrainCaller : StructDef SourceSet 2 ix1 F where
  name := "constraint_caller"
  members := []
  compute := {
    numParams := 1
    body := []
    returnVar := some 0
    wf_caps := by rfl
    wf_ssa := by rfl
  }
  constrain := {
    numParams := 1
    body := [.op callSourceIx (.call none target0 0 [0])]
    returnVar := none
    wf_caps := by rfl
    wf_ssa := by rfl
  }

def constrainModule : Module SourceSet 2 F where
  structs
    | ⟨0, _⟩ => constrainCallee
    | ⟨1, _⟩ => constrainCaller

#guard (eraseConstrainFunc constrainModule ix1).map
    (fun result => (result.1.map Stmt.dest, result.1.map Stmt.reads, result.2)) ==
  some ([some 2, none], [[], [0, 2]], 3)

#guard (eraseComputeDef constrainModule ix1).isSome
#guard (eraseConstrainDef constrainModule ix1).isSome

end Dialect.CallPass.Tests
