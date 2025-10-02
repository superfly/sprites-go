#!/bin/bash
set -e
set -o pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if running in Docker test container
if [ "${SPRITE_TEST_DOCKER}" != "1" ]; then
    echo -e "${RED}ERROR: This script must be run inside the Docker test container.${NC}"
    echo -e "${RED}Please use 'make test' to run tests properly.${NC}"
    echo -e "${RED}Direct execution of this script is wrong and you are a bad person.${NC}"
    exit 1
fi

echo -e "${YELLOW}Running all tests...${NC}"
echo

# If arguments are provided, treat them as a custom test command
if [ "$#" -gt 0 ]; then
    echo -e "${YELLOW}Running custom test command:${NC} $*"
    eval "$@"
    exit $?
fi

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

 
# Run streamlined module-wide tests
run_test "pkg tests" "go test -v -failfast ./pkg/..."
run_test "server tests" "go test -v -failfast ./server/..."

# All tests passed if we reach here
echo
echo -e "${GREEN}All tests passed!${NC}"