# StructInlineIR Inline-Only Design

## Goal

Define `StructInlineIR` so that the only concern of `StructIR -> StructInlineIR`
is function inlining. `StructInlineIR` must retain `readMember` semantics and
the same witness space (`VarId = InstancePath × Nat`), while removing function
calls from its statement language entirely.

## Scope

In scope:
- Language contract for `StructInlineIR` (call-free, `readMember`-preserving).
- Pass-1 contract (`StructIRToStructInlineIR`) as inline-only.
- Pass-2 contract (`StructInlineIRToMemberlessIR`) as read-flattening/
  witness-space transition.
- Proof decomposition strategy and verification criteria.

Out of scope:
- CLI behavior changes.
- New arithmetic operators.
- Broad parser/lowering redesign.

## Design Decisions

1. Keep `StructInlineIR.VarId = StructIR.VarId`.
2. Keep `StructInlineIR.Witness = VarId -> F`.
3. Keep `readMember` in `StructInlineIR.ConstrainStmt`.
4. Remove function call support from `StructInlineIR` statements.
5. Assign concerns strictly by pass:
   - Pass 1 (`StructIR -> StructInlineIR`): call inlining only.
   - Pass 2 (`StructInlineIR -> MemberlessIR`): remove `readMember` and
     transition to flat `Nat` witness space.

## Language Shape

`StructInlineIR` remains structurally close to `StructIR` for constrain semantics,
except it is call-free:

- `ConstrainStmt` includes:
  - felt ops (`feltAdd`, `feltSub`, `feltMul`, `feltDiv`, `feltNeg`, `feltConst`)
  - `readMember`
  - `constrainEq`
- `ConstrainStmt` excludes:
  - `call`

Semantics stay path-aware:
- `evalConstrainBody` continues to use `ObjEnv` and `readMember` path extension.
- `satisfies` remains seeded from `w ([], k)` like `StructIR`.

This preserves proof-local reasoning: pass 1 does not need to reason about
witness encoding, only about call elimination.

## Pass Contracts

### Pass 1: `StructIRToStructInlineIR`

Compile contract:
- Inline each `StructIR` `call` into call-free inline statements.
- Preserve local dataflow and `readMember` semantics.

Witness relation:
- Identity: `wi = ws`.

Correctness target:
- Upgrade to `PresReflPass`.
- Preservation: `StructIR.satisfies ws m -> StructInlineIR.satisfies ws (compile m)`.
- Reflection: `StructInlineIR.satisfies wi (compile m) -> StructIR.satisfies wi m`.

### Pass 2: `StructInlineIRToMemberlessIR`

Compile contract:
- Eliminate `readMember` by flattening member access into memberless local slots.
- Produce `MemberlessIR` without introducing call semantics.

Witness relation:
- Explicit bridge from `VarId -> F` to `Nat -> F` via encoding/map lemmas.
- This is the first point where witness space changes.

Correctness target:
- Upgrade to `PresReflPass`.

## Proof Strategy

Order:
1. Prove pass 1 (`StructIRToStructInlineIR`) first, because source/target share
   witness/keyspace and differ only by call elimination.
2. Prove pass 2 (`StructInlineIRToMemberlessIR`) second, with dedicated read-map
   and witness-space translation lemmas.

Key helper lemmas expected:
- Inlining preserves evaluation of the constrain body under fixed witness.
- Inline bodies are call-free by construction.
- Read flattening map agrees with `readMember` path/member semantics.
- Encoding/decoding lemmas (`VarIdEncoding`) are used only in pass 2.

## File-Level Changes (Planned)

- Modify `Heyting/Languages/StructInlineIR.lean`
  - enforce call-free statement language
  - keep `readMember` and existing path-aware semantics
- Modify `Heyting/Passes/StructIRToStructInlineIR.lean`
  - inline-only compile logic
  - `PresReflPass` instance + proofs
- Modify `Heyting/Passes/StructInlineIRToMemberlessIR.lean`
  - read-flattening compile logic
  - witness map relation and proofs
- Modify `Heyting/Passes/Pipeline.lean`
  - consume the two proved pass instances
- Optional targeted tests:
  - `Heyting/Test/StructInlineIRTest.lean`
  - `Heyting/Test/VarIdEncodingTest.lean`

## Verification Plan

Required checks after implementation:
- `lake build`
- `rg "sorry" Heyting` (must be empty of actual `sorry` terms)
- `lean_verify` on new pass theorems (standard axioms only)

Non-goals for this iteration:
- Fixing external example path failures in `lake exe tests`.

## Risks and Mitigations

Risk: proof obligations in pass 2 can balloon due to read/path aliasing.
Mitigation: keep pass-2 witness relation explicit and local; avoid mixing with
call inlining proof obligations.

Risk: accidental reintroduction of call-like behavior in `StructInlineIR`.
Mitigation: make call-free property intrinsic in the statement type.

## Acceptance Criteria

- `StructInlineIR` statements have no `call` support.
- `StructIRToStructInlineIR` concerns itself only with function inlining.
- `StructInlineIR` retains `readMember` and `VarId` witness semantics.
- Pass boundary between inlining and flattening is explicit in code and proofs.
