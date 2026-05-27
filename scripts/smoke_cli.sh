#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/hey"
INPUT="$ROOT/scripts/multiply.llzk"
OUT_BASE="${TMPDIR:-/tmp}/heyting-smoke"

rm -rf "$OUT_BASE"
mkdir -p "$OUT_BASE/json" "$OUT_BASE/json_auto" "$OUT_BASE/bin" "$OUT_BASE/bin_auto"

if ! command -v snarkjs >/dev/null 2>&1; then
  echo "snarkjs not found in PATH" >&2
  exit 1
fi

echo "[1/8] build hey"
lake build hey >/dev/null

echo "[2/8] json r1cs"
"$BIN" compile --json "$INPUT" "$OUT_BASE/json/multiply"
test -f "$OUT_BASE/json/multiply.r1cs.json"

echo "[3/8] json r1cs + witness"
"$BIN" compile --json --auto "$INPUT" "$OUT_BASE/json_auto/multiply"
test -f "$OUT_BASE/json_auto/multiply.r1cs.json"
test -f "$OUT_BASE/json_auto/multiply.witness.json"

echo "[4/8] binary r1cs"
"$BIN" compile "$INPUT" "$OUT_BASE/bin/multiply"
test -f "$OUT_BASE/bin/multiply.r1cs"

echo "[5/8] binary r1cs + witness"
"$BIN" compile --auto "$INPUT" "$OUT_BASE/bin_auto/multiply"
test -f "$OUT_BASE/bin_auto/multiply.r1cs"
test -f "$OUT_BASE/bin_auto/multiply.wtns"

echo "[6/8] snarkjs r1cs info"
R1CS_INFO="$(snarkjs r1cs info "$OUT_BASE/bin_auto/multiply.r1cs")"
printf '%s\n' "$R1CS_INFO"
printf '%s\n' "$R1CS_INFO" | grep -q "# of Constraints:"

echo "[7/8] snarkjs witness check"
WTNS_CHECK="$(snarkjs wtns check "$OUT_BASE/bin_auto/multiply.r1cs" "$OUT_BASE/bin_auto/multiply.wtns")"
printf '%s\n' "$WTNS_CHECK"
printf '%s\n' "$WTNS_CHECK" | grep -q "WITNESS IS CORRECT"

echo "[8/8] run test suite"
"$ROOT/tests/run_tests.sh"

echo "smoke ok: $OUT_BASE"
