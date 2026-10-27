#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/hey"
INPUT="$ROOT/scripts/multiply.llzk"
INPUTS="$ROOT/scripts/multiply.input.json"
OUT_BASE="${TMPDIR:-/tmp}/heyting-smoke"

rm -rf "$OUT_BASE"
mkdir -p "$OUT_BASE/json" "$OUT_BASE/json_auto" "$OUT_BASE/bin" "$OUT_BASE/features"

if ! command -v snarkjs >/dev/null 2>&1; then
  echo "snarkjs not found in PATH" >&2
  exit 1
fi

echo "[1/15] build hey"
lake build hey >/dev/null

echo "[2/15] json r1cs"
"$BIN" compile --json "$INPUT" "$OUT_BASE/json/multiply"
test -f "$OUT_BASE/json/multiply.r1cs.json"

echo "[3/15] json r1cs + witness"
"$BIN" compile --json --input "$INPUTS" "$INPUT" "$OUT_BASE/json_auto/multiply"
test -f "$OUT_BASE/json_auto/multiply.r1cs.json"
test -f "$OUT_BASE/json_auto/multiply.witness.json"

echo "[4/15] binary r1cs + witness"
"$BIN" compile --input "$INPUTS" "$INPUT" "$OUT_BASE/bin/multiply"
test -f "$OUT_BASE/bin/multiply.r1cs"
test -f "$OUT_BASE/bin/multiply.wtns"
R1CS_INFO="$(snarkjs r1cs info "$OUT_BASE/bin/multiply.r1cs")"
printf '%s\n' "$R1CS_INFO"
printf '%s\n' "$R1CS_INFO" | grep -q "# of Constraints:"
WTNS_CHECK="$(snarkjs wtns check "$OUT_BASE/bin/multiply.r1cs" "$OUT_BASE/bin/multiply.wtns")"
printf '%s\n' "$WTNS_CHECK"
printf '%s\n' "$WTNS_CHECK" | grep -q "WITNESS IS CORRECT"

echo "[5/15] constraint-only dialect subset"
"$BIN" compile "$ROOT/tests/dialect_subset.llzk" "$OUT_BASE/features/subset"
test -f "$OUT_BASE/features/subset.r1cs"
snarkjs r1cs info "$OUT_BASE/features/subset.r1cs" >/dev/null

echo "[6/15] StructObject and public members"
"$BIN" compile --input "$ROOT/tests/struct_ops.input.json" "$ROOT/tests/struct_ops.llzk" \
  "$OUT_BASE/features/struct_ops"
snarkjs wtns check "$OUT_BASE/features/struct_ops.r1cs" \
  "$OUT_BASE/features/struct_ops.wtns" | grep -q "WITNESS IS CORRECT"
"$BIN" compile "$ROOT/tests/pub_members.llzk" "$OUT_BASE/features/pub_members"
snarkjs r1cs info "$OUT_BASE/features/pub_members.r1cs" >/dev/null

echo "[7/15] nested call witness"
"$BIN" compile --input "$ROOT/tests/nested_calls.input.json" \
  "$ROOT/tests/nested_calls.llzk" "$OUT_BASE/features/nested_calls"
snarkjs wtns check "$OUT_BASE/features/nested_calls.r1cs" \
  "$OUT_BASE/features/nested_calls.wtns" | grep -q "WITNESS IS CORRECT"

echo "[8/15] nonzero Oracle witness"
"$BIN" compile --input "$ROOT/tests/nondet.input.json" \
  --oracle "$ROOT/tests/nondet.oracle.json" "$ROOT/tests/nondet.llzk" \
  "$OUT_BASE/features/nondet"
snarkjs wtns check "$OUT_BASE/features/nondet.r1cs" \
  "$OUT_BASE/features/nondet.wtns" | grep -q "WITNESS IS CORRECT"

echo "[9/15] adversarial full-feature witness"
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

echo "[10/15] adversarial source-constraint rejection"
expect_rejection "typed-source checker: constraint failed" \
  "$BIN" compile --input "$ROOT/tests/adversarial_full.input.json" \
    --oracle "$ROOT/tests/adversarial_full.bad.oracle.json" \
    "$ROOT/tests/adversarial_full.llzk" "$OUT_BASE/features/adversarial_bad"
test ! -e "$OUT_BASE/features/adversarial_bad.r1cs"

echo "[11/15] Oracle exhaustion boundary"
expect_rejection "oracle input exhausted" \
  "$BIN" compile --input "$ROOT/tests/nondet.input.json" \
    "$ROOT/tests/nondet.llzk" "$OUT_BASE/features/oracle_underflow"

echo "[12/15] division validity boundary"
expect_rejection "division by zero" \
  "$BIN" compile --input "$ROOT/tests/felt_ops.zero.input.json" "$ROOT/tests/felt_ops.llzk" \
    "$OUT_BASE/features/div_zero"

echo "[13/15] input and field boundaries"
echo '{"arg0": "3"}' >"$OUT_BASE/features/partial.input.json"
expect_rejection "missing input signal" \
  "$BIN" compile --input "$OUT_BASE/features/partial.input.json" "$INPUT" \
    "$OUT_BASE/features/missing_input"
expect_rejection "entry struct takes 3 inputs, got 0" \
  "$BIN" compile --auto "$INPUT" "$OUT_BASE/features/auto_no_input"
expect_rejection 'program uses field "bn128" but compilation targets "babybear"' \
  "$BIN" compile --prime-field babybear "$INPUT" "$OUT_BASE/features/field_mismatch"
"$BIN" compile "$INPUT" "$OUT_BASE/features/field_default" | grep -q "field: bn128"
echo '["3", "1"]' >"$OUT_BASE/features/extra.oracle.json"
expect_rejection "llzk.nondet reads only" \
  "$BIN" compile --input "$ROOT/tests/nondet.input.json" \
    --oracle "$OUT_BASE/features/extra.oracle.json" "$ROOT/tests/nondet.llzk" \
    "$OUT_BASE/features/oracle_extra"

echo "[14/15] Groth16 public statement"
# Statement wires must be exactly [public output, public input]; the private input stays out.
G16="$OUT_BASE/groth16"
mkdir -p "$G16"
snarkjs powersoftau new bn128 8 "$G16/pot0.ptau" >/dev/null
snarkjs powersoftau contribute "$G16/pot0.ptau" "$G16/pot1.ptau" --name=smoke -e=smoke >/dev/null
snarkjs powersoftau prepare phase2 "$G16/pot1.ptau" "$G16/pot.ptau" >/dev/null
"$BIN" compile --input "$ROOT/tests/public_io.input.json" "$ROOT/tests/public_io.llzk" \
  "$G16/pio" >/dev/null
snarkjs groth16 setup "$G16/pio.r1cs" "$G16/pot.ptau" "$G16/pio.zkey" >/dev/null
snarkjs zkey export verificationkey "$G16/pio.zkey" "$G16/vk.json" >/dev/null
snarkjs groth16 prove "$G16/pio.zkey" "$G16/pio.wtns" "$G16/proof.json" "$G16/public.json"
python3 -c 'import json,sys; p=json.load(open(sys.argv[1])); assert p == ["42", "6"], p' \
  "$G16/public.json"
snarkjs groth16 verify "$G16/vk.json" "$G16/public.json" "$G16/proof.json" | grep -q "OK"
echo '["42", "7"]' >"$G16/forged.json"
if snarkjs groth16 verify "$G16/vk.json" "$G16/forged.json" "$G16/proof.json" | grep -q "OK!"; then
  echo "forged public statement verified" >&2
  exit 1
fi

echo "[15/15] run test suite"
"$ROOT/tests/run_tests.sh"

echo "smoke ok: $OUT_BASE"
