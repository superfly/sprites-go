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
    echo -e "${RED}Direct execution of this script is no wrong and you are a bad person.${NC}"
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

# If we're running inside the test container, run tests directly
if [ "$SPRITE_TEST_DOCKER" = "1" ]; then
    
    # Run tests for each package directly
    run_test "pkg/container tests" "go test -v ./pkg/container/..."
    run_test "pkg/juicefs tests" "go test -v ./pkg/juicefs/..."
    run_test "pkg/leaser tests" "go test -v ./pkg/leaser/..."
    run_test "pkg/overlay tests" "go test -v ./pkg/overlay/..."
    run_test "pkg/port-watcher tests" "go test -v ./pkg/port-watcher/..."
    run_test "pkg/services tests" "go test -v ./pkg/services/..."
    run_test "pkg/sync tests" "go test -v ./pkg/sync/..."
    run_test "pkg/tap tests" "go test -v ./pkg/tap/..."
    run_test "pkg/terminal tests" "go test -v ./pkg/terminal/..."
    run_test "pkg/tmux tests" "go test -v ./pkg/tmux/..."
    run_test "pkg/wsexec tests" "go test -v ./pkg/wsexec/..."
    run_test "pkg/db tests" "go test -v ./pkg/db/..."
    run_test "pkg/checkpoint tests" "go test -v ./pkg/checkpoint/..."
else
    # Run tests for each package in pkg/ that has a Makefile
    for package_dir in pkg/*/; do
        if [ -d "$package_dir" ] && [ -f "$package_dir/Makefile" ]; then
            package_name=$(basename "$package_dir")
            run_test "pkg/$package_name tests" "(cd $package_dir && make test)"
        fi
    done
fi

# Run tests for all packages in root module
run_test "pkg tests" "go test -v -failfast ./pkg/..."
run_test "client tests" "go test -v -failfast ./client/..."
run_test "lib tests" "go test -v -failfast ./lib/..."
run_test "server tests" "go test -v -failfast ./server/..."

# All tests passed if we reach here
echo
echo -e "${GREEN}All tests passed!${NC}"