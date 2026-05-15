#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/hey"
INPUT="$ROOT/scripts/multiply.llzk"
OUT_BASE="${TMPDIR:-/tmp}/heyting-smoke"

rm -rf "$OUT_BASE"
mkdir -p "$OUT_BASE/json" "$OUT_BASE/json_auto" "$OUT_BASE/bin" "$OUT_BASE/bin_auto"

echo "[1/5] build hey"
lake build hey >/dev/null

echo "[2/5] json r1cs"
"$BIN" compile --json "$INPUT" "$OUT_BASE/json/multiply"
test -f "$OUT_BASE/json/multiply.r1cs.json"

echo "[3/5] json r1cs + witness"
"$BIN" compile --json --auto "$INPUT" "$OUT_BASE/json_auto/multiply"
test -f "$OUT_BASE/json_auto/multiply.r1cs.json"
test -f "$OUT_BASE/json_auto/multiply.witness.json"

echo "[4/5] binary r1cs"
"$BIN" compile "$INPUT" "$OUT_BASE/bin/multiply"
test -f "$OUT_BASE/bin/multiply.r1cs"

echo "[5/5] binary r1cs + witness"
"$BIN" compile --auto "$INPUT" "$OUT_BASE/bin_auto/multiply"
test -f "$OUT_BASE/bin_auto/multiply.r1cs"
test -f "$OUT_BASE/bin_auto/multiply.wtns"

echo "smoke ok: $OUT_BASE"
