#!/bin/bash
set -e -o pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

TESTS_PASSED=0
TESTS_FAILED=0

print_info() { echo -e "${BLUE}INFO:${NC} $1"; }
print_test() { echo -e "${YELLOW}TEST:${NC} $1"; }
print_pass() { echo -e "${GREEN}✓ PASS:${NC} $1"; TESTS_PASSED=$((TESTS_PASSED + 1)); }
print_fail() { echo -e "${RED}✗ FAIL:${NC} $1"; TESTS_FAILED=$((TESTS_FAILED + 1)); }

print_summary() {
  echo ""
  echo "========================================"
  if [ $TESTS_FAILED -eq 0 ]; then
    echo -e "${GREEN}All tests passed${NC} ($TESTS_PASSED/$((TESTS_PASSED + TESTS_FAILED)))"
  else
    echo -e "${RED}Some tests failed${NC} ($TESTS_PASSED passed, $TESTS_FAILED failed)"
  fi
  echo "========================================"
}

cleanup() {
  if [ -n "${CONTAINER_ID:-}" ]; then
    echo "Cleaning up container: $CONTAINER_ID"
    docker rm -f "$CONTAINER_ID" >/dev/null 2>&1 || true
  fi
}
trap cleanup EXIT

if [ $# -lt 1 ]; then
  echo "Usage: $0 <image:tag>"
  exit 2
fi

IMAGE_TAG="$1"

print_info "Testing image: $IMAGE_TAG"

# Run the container in detached mode as root, override entrypoint to sleep
CONTAINER_ID=$(docker run -d --init --user root --entrypoint sleep "$IMAGE_TAG" 3600)
print_info "Container ID: $CONTAINER_ID"

echo ""
echo "========================================"
echo "Running Base Image Tests"
echo "========================================"
echo ""

# 1) PATH includes /.sprite/bin/
print_test "Checking if /.sprite/bin/ is in PATH"
if docker exec "$CONTAINER_ID" bash -c 'echo "$PATH"' | grep -q '/.sprite/bin'; then
  print_pass "/.sprite/bin/ is in PATH"
else
  print_fail "/.sprite/bin/ is NOT in PATH"
fi

# 2) /home/sprite/.claude/ and /home/sprite/.gemini files exist
echo ""
print_test "Checking Claude and Gemini instruction/extension files exist"

check_file() {
  local path="$1"
  if docker exec "$CONTAINER_ID" test -e "$path"; then
    print_pass "$path exists"
    return 0
  else
    print_fail "$path is missing"
    return 1
  fi
}

# Claude files
check_file "/home/sprite/.claude/CLAUDE.md"
check_file "/home/sprite/.claude/llm.txt"
check_file "/home/sprite/.claude/llm-dev.txt"

# Gemini extension files
check_file "/home/sprite/.gemini/extensions/sprite-context/gemini-extension.json"
check_file "/home/sprite/.gemini/extensions/sprite-context/llm.txt"
check_file "/home/sprite/.gemini/extensions/sprite-context/llm-dev.txt"

# 3) /.sprite/llm.txt exists
echo ""
print_test "Checking /.sprite/llm.txt exists"
if docker exec "$CONTAINER_ID" test -f "/.sprite/llm.txt"; then
  print_pass "/.sprite/llm.txt exists"
else
  print_fail "/.sprite/llm.txt is missing"
fi

echo ""
print_summary

if [ $TESTS_FAILED -gt 0 ]; then
  exit 1
fi
exit 0


