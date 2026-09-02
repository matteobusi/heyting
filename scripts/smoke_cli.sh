#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/hey"
INPUT="$ROOT/scripts/multiply.llzk"
OUT_BASE="${TMPDIR:-/tmp}/heyting-smoke"

rm -rf "$OUT_BASE"
mkdir -p "$OUT_BASE/json" "$OUT_BASE/json_auto" "$OUT_BASE/bin" "$OUT_BASE/bin_auto" \
  "$OUT_BASE/dialect"

if ! command -v snarkjs >/dev/null 2>&1; then
  echo "snarkjs not found in PATH" >&2
  exit 1
fi

echo "[1/15] build hey"
lake build hey >/dev/null

echo "[2/15] default dialect json r1cs"
"$BIN" compile --json "$INPUT" "$OUT_BASE/json/multiply"
test -f "$OUT_BASE/json/multiply.r1cs.json"

echo "[3/15] default dialect json r1cs + witness"
"$BIN" compile --json --auto "$INPUT" "$OUT_BASE/json_auto/multiply"
test -f "$OUT_BASE/json_auto/multiply.r1cs.json"
test -f "$OUT_BASE/json_auto/multiply.witness.json"

echo "[4/15] legacy binary r1cs"
"$BIN" compile --legacy "$INPUT" "$OUT_BASE/bin/multiply"
test -f "$OUT_BASE/bin/multiply.r1cs"

echo "[5/15] legacy binary r1cs + witness"
"$BIN" compile --legacy --auto "$INPUT" "$OUT_BASE/bin_auto/multiply"
test -f "$OUT_BASE/bin_auto/multiply.r1cs"
test -f "$OUT_BASE/bin_auto/multiply.wtns"

echo "[6/15] snarkjs r1cs info"
R1CS_INFO="$(snarkjs r1cs info "$OUT_BASE/bin_auto/multiply.r1cs")"
printf '%s\n' "$R1CS_INFO"
printf '%s\n' "$R1CS_INFO" | grep -q "# of Constraints:"

echo "[7/15] legacy witness check"
WTNS_CHECK="$(snarkjs wtns check "$OUT_BASE/bin_auto/multiply.r1cs" "$OUT_BASE/bin_auto/multiply.wtns")"
printf '%s\n' "$WTNS_CHECK"
printf '%s\n' "$WTNS_CHECK" | grep -q "WITNESS IS CORRECT"

echo "[8/15] explicit dialect-native r1cs"
"$BIN" compile --dialect "$ROOT/tests/dialect_subset.llzk" "$OUT_BASE/dialect/subset"
test -f "$OUT_BASE/dialect/subset.r1cs"
snarkjs r1cs info "$OUT_BASE/dialect/subset.r1cs" >/dev/null

echo "[9/15] dialect StructObject erasure"
"$BIN" compile --dialect "$ROOT/tests/struct_ops.llzk" "$OUT_BASE/dialect/struct_ops"
test -f "$OUT_BASE/dialect/struct_ops.r1cs"
snarkjs r1cs info "$OUT_BASE/dialect/struct_ops.r1cs" >/dev/null

echo "[10/15] dialect public members"
"$BIN" compile --dialect "$ROOT/tests/pub_members.llzk" "$OUT_BASE/dialect/pub_members"
test -f "$OUT_BASE/dialect/pub_members.r1cs"
snarkjs r1cs info "$OUT_BASE/dialect/pub_members.r1cs" >/dev/null

echo "[11/15] dialect witness generation"
"$BIN" compile --dialect --auto "$INPUT" "$OUT_BASE/dialect/multiply"
snarkjs wtns check "$OUT_BASE/dialect/multiply.r1cs" \
  "$OUT_BASE/dialect/multiply.wtns" | grep -q "WITNESS IS CORRECT"

echo "[12/15] dialect nonzero oracle witness"
"$BIN" compile --dialect --input "$ROOT/tests/nondet.input.json" \
  --oracle "$ROOT/tests/nondet.oracle.json" "$ROOT/tests/nondet.llzk" \
  "$OUT_BASE/dialect/nondet"
snarkjs wtns check "$OUT_BASE/dialect/nondet.r1cs" \
  "$OUT_BASE/dialect/nondet.wtns" | grep -q "WITNESS IS CORRECT"

echo "[13/15] oracle exhaustion boundary"
if "$BIN" compile --dialect --input "$ROOT/tests/nondet.input.json" \
    "$ROOT/tests/nondet.llzk" "$OUT_BASE/dialect/oracle_underflow" \
    >/dev/null 2>&1; then
  echo "dialect witness generation unexpectedly accepted an exhausted oracle" >&2
  exit 1
fi

echo "[14/15] division validity boundary"
if "$BIN" compile --auto "$ROOT/tests/felt_ops.llzk" \
    "$OUT_BASE/dialect/div_zero" >/dev/null 2>&1; then
  echo "dialect witness generation unexpectedly accepted division by zero" >&2
  exit 1
fi

echo "[15/15] run test suite"
"$ROOT/tests/run_tests.sh"

echo "smoke ok: $OUT_BASE"
