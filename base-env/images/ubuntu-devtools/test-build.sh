#!/bin/bash
set -e -o pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test counters
TESTS_PASSED=0
TESTS_FAILED=0

print_info() {
    echo -e "${BLUE}INFO:${NC} $1"
}

print_test() {
    echo -e "${YELLOW}TEST:${NC} $1"
}

print_pass() {
    echo -e "${GREEN}✓ PASS:${NC} $1"
    TESTS_PASSED=$((TESTS_PASSED + 1))
}

print_fail() {
    echo -e "${RED}✗ FAIL:${NC} $1"
    TESTS_FAILED=$((TESTS_FAILED + 1))
}

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

# Cleanup function
cleanup() {
    if [ -n "$CONTAINER_ID" ]; then
        echo "Cleaning up container: $CONTAINER_ID"
        docker rm -f "$CONTAINER_ID" >/dev/null 2>&1 || true
    fi
}

trap cleanup EXIT

# Get the directory of this script
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$SCRIPT_DIR"

echo "========================================"
echo "Building ubuntu-devtools Docker image"
echo "========================================"
print_info "This builds the base system image (without tmux, gh, or system scripts)"
print_info "Those binaries are added in the main Dockerfile assembly stage"
echo ""

# Build the image (default final stage)
IMAGE_TAG="sprite-ubuntu-devtools:test-$(date +%s)"
docker build -t "$IMAGE_TAG" .

echo ""
echo "========================================"
echo "Running container for tests"
echo "========================================"

# Run the container in detached mode as root user
# Override entrypoint since /.pilot/tini doesn't exist in this base image
# Use --init to run an init process inside the container
# Run as root to avoid permission issues during testing
CONTAINER_ID=$(docker run -d --init --user root --entrypoint sleep "$IMAGE_TAG" 3600)
echo "Container ID: $CONTAINER_ID"

echo ""
echo "========================================"
echo "Running Tests"
echo "========================================"
echo ""

# Test 1: Check if /.sprite/bin/ is in PATH
print_test "Checking if /.sprite/bin/ is in PATH"
if docker exec "$CONTAINER_ID" bash -c 'echo "$PATH"' | grep -q '/.sprite/bin'; then
    print_pass "/.sprite/bin/ is in PATH"
else
    print_fail "/.sprite/bin/ is NOT in PATH"
fi

# Test 2: Check if /.sprite/bin/ directory exists
print_test "Checking if /.sprite/bin/ directory exists"
if docker exec "$CONTAINER_ID" test -d "/.sprite/bin"; then
    print_pass "/.sprite/bin/ directory exists"
else
    print_fail "/.sprite/bin/ directory does NOT exist"
fi

# Test 3: Verify PATH in a login shell
print_test "Checking PATH in login shell"
if docker exec "$CONTAINER_ID" bash -l -c 'echo "$PATH"' | grep -q '/.sprite/bin'; then
    print_pass "/.sprite/bin/ is in PATH in login shell"
else
    print_fail "/.sprite/bin/ is NOT in PATH in login shell"
fi

# Test 4: List contents of /.sprite/bin/ 
echo ""
print_test "Listing contents of /.sprite/bin/"
echo "Contents:"
docker exec "$CONTAINER_ID" ls -lah "/.sprite/bin/" 2>/dev/null || print_fail "Could not list /.sprite/bin/"
echo ""

# Function to test if a command exists in /.sprite/bin/
test_command_in_sprite_bin() {
    local cmd=$1
    local optional=${2:-false}
    
    if [ "$optional" = "true" ]; then
        print_test "Checking if $cmd is in /.sprite/bin/ (optional in this image)"
    else
        print_test "Checking if $cmd is in /.sprite/bin/"
    fi
    
    # Check if the file exists directly
    if docker exec "$CONTAINER_ID" test -f "/.sprite/bin/$cmd"; then
        # Also check if it's executable
        if docker exec "$CONTAINER_ID" test -x "/.sprite/bin/$cmd"; then
            print_pass "$cmd exists at /.sprite/bin/$cmd and is executable"
        else
            print_fail "$cmd exists at /.sprite/bin/$cmd but is NOT executable"
        fi
        return 0
    else
        if [ "$optional" = "true" ]; then
            print_info "$cmd is NOT in /.sprite/bin/ (expected - added in main Dockerfile)"
            return 0
        else
            print_fail "$cmd is NOT in /.sprite/bin/"
            # Debug: show where it is if anywhere
            local location=$(docker exec "$CONTAINER_ID" which "$cmd" 2>/dev/null || echo "not found")
            if [ "$location" != "not found" ]; then
                echo "  (found at: $location)"
            fi
            return 1
        fi
    fi
}

# These binaries are added in the main Dockerfile, not in ubuntu-devtools
# Mark them as optional for this image
print_info "Note: sprite-browser, sprite-console, curl-sprite-api, tmux, and gh"
print_info "are assembled in the main Dockerfile, not in this base image"
echo ""

test_command_in_sprite_bin "sprite-browser" true
test_command_in_sprite_bin "sprite-console" true
test_command_in_sprite_bin "curl-sprite-api" true
test_command_in_sprite_bin "tmux" true
test_command_in_sprite_bin "gh" true

# Note: Even install-language-deps will be in the assembled image
echo ""
print_info "All /.sprite/bin/ binaries are assembled in the main Dockerfile"
print_info "This base image just sets up the directory structure and PATH"

# Test BROWSER environment variable
echo ""
print_test "Checking BROWSER environment variable"
BROWSER_VAR=$(docker exec "$CONTAINER_ID" bash -c 'echo "$BROWSER"')
if [ "$BROWSER_VAR" = "/.sprite/bin/sprite-browser" ]; then
    print_pass "BROWSER is set to /.sprite/bin/sprite-browser"
else
    print_fail "BROWSER is not set correctly (got: '$BROWSER_VAR')"
fi

# Test that basic shells are available
echo ""
print_info "Verifying shells are installed:"
for shell in bash zsh fish tcsh ksh; do
    print_test "Checking if $shell is installed"
    if docker exec "$CONTAINER_ID" which "$shell" >/dev/null 2>&1; then
        print_pass "$shell is installed"
    else
        print_fail "$shell is NOT installed"
    fi
done

# Test that kitty is available
echo ""
print_test "Checking if kitty is installed and in PATH"
if docker exec "$CONTAINER_ID" which kitty >/dev/null 2>&1; then
    print_pass "kitty is installed and in PATH"
else
    print_fail "kitty is NOT installed or not in PATH"
fi

# Test hostname resolution
echo ""
print_info "Verifying hostname resolution:"
print_info "Note: /etc/hosts entries are added in the main Dockerfile assembly"

print_test "Checking if 'sprite' resolves to 127.0.0.1 (IPv4) - optional in this image"
IPV4_RESULT=$(docker exec "$CONTAINER_ID" getent hosts sprite | grep -E "^127\.0\.0\.1" || true)
if [ -n "$IPV4_RESULT" ]; then
    print_pass "'sprite' resolves to 127.0.0.1"
else
    print_info "'sprite' does NOT resolve to 127.0.0.1 (expected - added in main Dockerfile)"
fi

print_test "Checking if 'sprite' resolves to fdf::1 (IPv6) - optional in this image"
IPV6_RESULT=$(docker exec "$CONTAINER_ID" getent ahosts sprite | grep -E "^fdf::1" || true)
if [ -n "$IPV6_RESULT" ]; then
    print_pass "'sprite' resolves to fdf::1"
else
    print_info "'sprite' does NOT resolve to fdf::1 (expected - added in main Dockerfile)"
fi

print_test "Checking if 'localhost' resolves to fdf::1 (IPv6) - optional in this image"
LOCALHOST_IPV6_RESULT=$(docker exec "$CONTAINER_ID" getent ahosts localhost | grep -E "^fdf::1" || true)
if [ -n "$LOCALHOST_IPV6_RESULT" ]; then
    print_pass "'localhost' resolves to fdf::1"
else
    print_info "'localhost' does NOT resolve to fdf::1 (expected - added in main Dockerfile)"
fi

# Print summary
print_summary

# Exit with appropriate code
if [ $TESTS_FAILED -gt 0 ]; then
    exit 1
fi

exit 0

