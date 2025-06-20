#!/bin/bash
set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${YELLOW}Running all tests...${NC}"
echo

# Track if any tests fail
FAILED=0

# Function to run tests and check result
run_test() {
    local test_name=$1
    local test_command=$2
    
    echo -e "${YELLOW}Running $test_name...${NC}"
    if eval "$test_command"; then
        echo -e "${GREEN}✓ $test_name passed${NC}"
    else
        echo -e "${RED}✗ $test_name failed${NC}"
        FAILED=1
    fi
    echo
}

# Run tests for each package in packages/
for package_dir in packages/*/; do
    if [ -d "$package_dir" ] && [ -f "$package_dir/Makefile" ]; then
        package_name=$(basename "$package_dir")
        (run_test "package/$package_name tests" "cd $package_dir && make test")
    fi
done

pwd

# Run lib tests
run_test "lib tests" "go test ./lib/..."

# Run server tests
run_test "server tests" "go test ./server/..."

# Summary
echo
if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
else
    echo -e "${RED}Some tests failed!${NC}"
    exit 1
fi 