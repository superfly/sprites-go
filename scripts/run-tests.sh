#!/bin/bash
set -e
set -o pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${YELLOW}Running all tests...${NC}"
echo

# Function to run tests and fail immediately on error
run_test() {
    local test_name=$1
    local test_command=$2
    
    echo -e "${YELLOW}Running $test_name...${NC}"
    if eval "$test_command"; then
        echo -e "${GREEN}✓ $test_name passed${NC}"
        echo
    else
        echo -e "${RED}✗ $test_name failed${NC}"
        exit 1
    fi
}

# Run tests for each package in packages/
for package_dir in packages/*/; do
    if [ -d "$package_dir" ] && [ -f "$package_dir/Makefile" ]; then
        package_name=$(basename "$package_dir")
        run_test "package/$package_name tests" "(cd $package_dir && make test)"
    fi
done

# Run client tests
run_test "client tests" "go test -v -failfast ./client/..."

# Run lib tests
run_test "lib tests" "go test -v -failfast ./lib/..."

# Run server tests
run_test "server tests" "go test -v -failfast ./server/..."

# Run integration tests (Docker-based)
run_test "integration tests" "(cd tests && go mod tidy && go test -v -failfast -timeout 10m -run TestExecIntegration)"

# All tests passed if we reach here
echo
echo -e "${GREEN}All tests passed!${NC}" 