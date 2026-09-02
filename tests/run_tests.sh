#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/.lake/build/bin/hey"
TESTS_DIR="$ROOT/tests"
OUT_BASE="${TMPDIR:-/tmp}/heyting-tests"

# Color output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

rm -rf "$OUT_BASE"
mkdir -p "$OUT_BASE"

echo "================================"
echo "Heyting Test Suite"
echo "================================"
echo

# Build compiler
echo -e "${YELLOW}[build]${NC} Building hey compiler..."
lake build hey >/dev/null 2>&1
echo -e "${GREEN}✓${NC} Build complete"
echo

# Test counter
TOTAL=0
PASSED=0
FAILED=0

# Run test on a single .llzk file
run_test() {
  local test_file="$1"
  local test_name="$(basename "$test_file" .llzk)"
  local out_dir="$OUT_BASE/$test_name"
  
  TOTAL=$((TOTAL + 1))
  
  mkdir -p "$out_dir"
  
  echo -e "${YELLOW}[test]${NC} $test_name"
  
  # The unflagged path is dialect-native.
  if "$BIN" compile "$test_file" "$out_dir/$test_name" >"$out_dir/compile.log" 2>&1; then
    # Check output files exist
    if [ -f "$out_dir/$test_name.r1cs" ]; then
      echo -e "${GREEN}  ✓${NC} Compilation succeeded"
      echo -e "${GREEN}  ✓${NC} R1CS output generated"
      
      # Optional: run snarkjs r1cs info if available
      if command -v snarkjs >/dev/null 2>&1; then
        if snarkjs r1cs info "$out_dir/$test_name.r1cs" >"$out_dir/r1cs_info.log" 2>&1; then
          constraints=$(grep "# of Constraints:" "$out_dir/r1cs_info.log" | awk '{print $NF}')
          echo -e "${GREEN}  ✓${NC} snarkjs validation passed ($constraints constraints)"
        else
          echo -e "${YELLOW}  !${NC} snarkjs validation failed (see $out_dir/r1cs_info.log)"
        fi
      fi
      
      # Differential reference coverage: every fixture must also compile via
      # the quarantined legacy pipeline.
      if ! "$BIN" compile --legacy "$test_file" "$out_dir/$test_name.legacy" \
          >"$out_dir/legacy.log" 2>&1; then
        echo -e "${RED}  ✗${NC} Legacy differential compilation failed"
        cat "$out_dir/legacy.log"
        FAILED=$((FAILED + 1))
        echo
        return
      fi

      # Constraint-only fixtures have no compute program from which to derive
      # a witness. Felt division needs explicit nonzero inputs. All other
      # fixtures are valid under default-zero inputs.
      if [ "$test_name" != "dialect_subset" ]; then
        local witness_args=(--auto)
        local legacy_witness_args=(--auto)
        if [ "$test_name" = "felt_ops" ]; then
          witness_args=(--input "$ROOT/tests/felt_ops.input.json")
          legacy_witness_args=(--input "$ROOT/tests/felt_ops.input.json")
        elif [ "$test_name" = "nondet" ]; then
          witness_args=(--input "$ROOT/tests/nondet.input.json" \
            --oracle "$ROOT/tests/nondet.oracle.json")
          legacy_witness_args=(--input "$ROOT/tests/nondet.input.json")
        fi
        if ! "$BIN" compile "${witness_args[@]}" "$test_file" \
            "$out_dir/$test_name.witness" >"$out_dir/dialect_witness.log" 2>&1; then
          echo -e "${RED}  ✗${NC} Dialect witness generation failed"
          cat "$out_dir/dialect_witness.log"
          FAILED=$((FAILED + 1))
          echo
          return
        fi
        if [ "$test_name" != "nondet" ]; then
          if ! "$BIN" compile --legacy "${legacy_witness_args[@]}" "$test_file" \
              "$out_dir/$test_name.legacy_witness" >"$out_dir/legacy_witness.log" 2>&1; then
            echo -e "${RED}  ✗${NC} Legacy witness generation failed"
            cat "$out_dir/legacy_witness.log"
            FAILED=$((FAILED + 1))
            echo
            return
          fi
        fi
        if command -v snarkjs >/dev/null 2>&1; then
          snarkjs wtns check "$out_dir/$test_name.witness.r1cs" \
            "$out_dir/$test_name.witness.wtns" >/dev/null
          if [ "$test_name" = "nondet" ]; then
            echo -e "${GREEN}  ✓${NC} Dialect oracle witness validated"
          else
            snarkjs wtns check "$out_dir/$test_name.legacy_witness.r1cs" \
              "$out_dir/$test_name.legacy_witness.wtns" >/dev/null
            echo -e "${GREEN}  ✓${NC} Dialect/legacy witnesses validated"
          fi
        fi
      fi

      PASSED=$((PASSED + 1))
    else
      echo -e "${RED}  ✗${NC} R1CS output not found"
      echo -e "${RED}  ✗${NC} Test failed"
      cat "$out_dir/compile.log"
      FAILED=$((FAILED + 1))
    fi
  else
    echo -e "${RED}  ✗${NC} Compilation failed"
    cat "$out_dir/compile.log"
    FAILED=$((FAILED + 1))
  fi
  echo
}

# Run all tests
if [ -d "$TESTS_DIR" ]; then
  for test_file in "$TESTS_DIR"/*.llzk; do
    if [ -f "$test_file" ]; then
      run_test "$test_file"
    fi
  done
else
  echo -e "${RED}Error: tests/ directory not found${NC}"
  exit 1
fi

# Summary
echo "================================"
echo "Test Summary"
echo "================================"
echo "Total:  $TOTAL"
echo -e "Passed: ${GREEN}$PASSED${NC}"
if [ $FAILED -gt 0 ]; then
  echo -e "Failed: ${RED}$FAILED${NC}"
else
  echo -e "Failed: $FAILED"
fi
echo
echo "Output directory: $OUT_BASE"

if [ $FAILED -gt 0 ]; then
  exit 1
fi
