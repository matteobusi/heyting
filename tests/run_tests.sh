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
  
  # Try to compile - capture both stdout and stderr
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
