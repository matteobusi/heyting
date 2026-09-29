#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
python3 "$ROOT/scripts/check_active_imports.py"
BIN="$ROOT/.lake/build/bin/hey"
INPUT="$ROOT/scripts/multiply.llzk"
OUT_BASE="${TMPDIR:-/tmp}/heyting-smoke"

rm -rf "$OUT_BASE"
mkdir -p "$OUT_BASE/json" "$OUT_BASE/json_auto" "$OUT_BASE/bin" "$OUT_BASE/features"

if ! command -v snarkjs >/dev/null 2>&1; then
  echo "snarkjs not found in PATH" >&2
  exit 1
fi

echo "[1/14] build hey"
lake build hey >/dev/null

echo "[2/14] json r1cs"
"$BIN" compile --json "$INPUT" "$OUT_BASE/json/multiply"
test -f "$OUT_BASE/json/multiply.r1cs.json"

echo "[3/14] json r1cs + witness"
"$BIN" compile --json --auto "$INPUT" "$OUT_BASE/json_auto/multiply"
test -f "$OUT_BASE/json_auto/multiply.r1cs.json"
test -f "$OUT_BASE/json_auto/multiply.witness.json"

echo "[4/14] binary r1cs + witness"
"$BIN" compile --auto "$INPUT" "$OUT_BASE/bin/multiply"
test -f "$OUT_BASE/bin/multiply.r1cs"
test -f "$OUT_BASE/bin/multiply.wtns"
R1CS_INFO="$(snarkjs r1cs info "$OUT_BASE/bin/multiply.r1cs")"
printf '%s\n' "$R1CS_INFO"
printf '%s\n' "$R1CS_INFO" | grep -q "# of Constraints:"
WTNS_CHECK="$(snarkjs wtns check "$OUT_BASE/bin/multiply.r1cs" "$OUT_BASE/bin/multiply.wtns")"
printf '%s\n' "$WTNS_CHECK"
printf '%s\n' "$WTNS_CHECK" | grep -q "WITNESS IS CORRECT"

echo "[5/14] constraint-only dialect subset"
"$BIN" compile "$ROOT/tests/dialect_subset.llzk" "$OUT_BASE/features/subset"
test -f "$OUT_BASE/features/subset.r1cs"
snarkjs r1cs info "$OUT_BASE/features/subset.r1cs" >/dev/null

echo "[6/14] StructObject and public members"
"$BIN" compile --auto "$ROOT/tests/struct_ops.llzk" "$OUT_BASE/features/struct_ops"
snarkjs wtns check "$OUT_BASE/features/struct_ops.r1cs" \
  "$OUT_BASE/features/struct_ops.wtns" | grep -q "WITNESS IS CORRECT"
"$BIN" compile "$ROOT/tests/pub_members.llzk" "$OUT_BASE/features/pub_members"
snarkjs r1cs info "$OUT_BASE/features/pub_members.r1cs" >/dev/null

echo "[7/14] nested call witness"
"$BIN" compile --auto "$ROOT/tests/nested_calls.llzk" "$OUT_BASE/features/nested_calls"
snarkjs wtns check "$OUT_BASE/features/nested_calls.r1cs" \
  "$OUT_BASE/features/nested_calls.wtns" | grep -q "WITNESS IS CORRECT"

echo "[8/14] nonzero Oracle witness"
"$BIN" compile --input "$ROOT/tests/nondet.input.json" \
  --oracle "$ROOT/tests/nondet.oracle.json" "$ROOT/tests/nondet.llzk" \
  "$OUT_BASE/features/nondet"
snarkjs wtns check "$OUT_BASE/features/nondet.r1cs" \
  "$OUT_BASE/features/nondet.wtns" | grep -q "WITNESS IS CORRECT"

echo "[9/14] adversarial full-feature witness"
"$BIN" compile --input "$ROOT/tests/adversarial_full.input.json" \
  --oracle "$ROOT/tests/adversarial_full.oracle.json" \
  "$ROOT/tests/adversarial_full.llzk" "$OUT_BASE/features/adversarial"
snarkjs wtns check "$OUT_BASE/features/adversarial.r1cs" \
  "$OUT_BASE/features/adversarial.wtns" | grep -q "WITNESS IS CORRECT"

# Negative check: the command must fail and its output must contain the expected message,
# so an unrelated failure (bad path, parse error) cannot pass as the intended rejection.
expect_rejection() {
  local pattern="$1"; shift
  local log
  if log="$("$@" 2>&1)"; then
    echo "compiler unexpectedly accepted: $*" >&2
    exit 1
  fi
  if ! grep -q -- "$pattern" <<<"$log"; then
    echo "rejection lacked expected message '$pattern' for: $*" >&2
    echo "$log" >&2
    exit 1
  fi
}

echo "[10/14] adversarial source-constraint rejection"
expect_rejection "typed-source checker: constraint failed" \
  "$BIN" compile --input "$ROOT/tests/adversarial_full.input.json" \
    --oracle "$ROOT/tests/adversarial_full.bad.oracle.json" \
    "$ROOT/tests/adversarial_full.llzk" "$OUT_BASE/features/adversarial_bad"
test ! -e "$OUT_BASE/features/adversarial_bad.r1cs"

echo "[11/14] Oracle exhaustion boundary"
expect_rejection "oracle input exhausted" \
  "$BIN" compile --input "$ROOT/tests/nondet.input.json" \
    "$ROOT/tests/nondet.llzk" "$OUT_BASE/features/oracle_underflow"

echo "[12/14] division validity boundary"
expect_rejection "division by zero" \
  "$BIN" compile --auto "$ROOT/tests/felt_ops.llzk" "$OUT_BASE/features/div_zero"

echo "[13/14] retired pipeline flags rejected"
expect_rejection "unknown option: --legacy" \
  "$BIN" compile --legacy "$INPUT" "$OUT_BASE/features/legacy"
expect_rejection "unknown option: --dialect" \
  "$BIN" compile --dialect "$INPUT" "$OUT_BASE/features/dialect"

echo "[14/14] run test suite"
"$ROOT/tests/run_tests.sh"

echo "smoke ok: $OUT_BASE"
