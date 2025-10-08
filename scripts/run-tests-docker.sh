#!/bin/bash
set -euo pipefail

# Run tests in Docker with parallel execution enabled by default.
#
# Usage:
#   ./scripts/run-tests-docker.sh              # All tests, -p=4 -failfast -timeout=15m
#   ./scripts/run-tests-docker.sh -v           # All tests with verbose output
#   ./scripts/run-tests-docker.sh -p=8         # All tests with 8 parallel packages
#   ./scripts/run-tests-docker.sh ./pkg/...    # Just pkg tests
#   ./scripts/run-tests-docker.sh -run TestFoo # Specific test pattern

IMAGE_NAME="sprite-env-tests"

# Check for running test containers
RUNNING_CONTAINERS=$(docker ps --filter "ancestor=$IMAGE_NAME" --format "{{.ID}}" 2>/dev/null || true)
if [ -n "$RUNNING_CONTAINERS" ]; then
    echo "ERROR: Found running test containers. Stop them first:"
    echo "  docker stop $RUNNING_CONTAINERS"
    exit 1
fi

# Build image if needed
if ! docker image inspect "$IMAGE_NAME" >/dev/null 2>&1; then
    echo "Building test image..."
    docker build -f Dockerfile.test -t "$IMAGE_NAME" .
fi

# Create cache volumes if needed
docker volume inspect sprite-go-home >/dev/null 2>&1 || docker volume create sprite-go-home >/dev/null
docker volume inspect sprite-go-mod >/dev/null 2>&1 || docker volume create sprite-go-mod >/dev/null

# Check for leftover loopback devices
EXISTING_LOOPS=$(docker run --rm --privileged "$IMAGE_NAME" losetup -a 2>/dev/null || true)
if [ -n "$EXISTING_LOOPS" ]; then
    echo "ERROR: Loopback devices still attached from previous test runs:"
    echo "$EXISTING_LOOPS"
    echo ""
    echo "Clean them up with:"
    echo "  docker run --rm --privileged $IMAGE_NAME losetup -D"
    exit 1
fi

# Run tests via the test script
docker run \
    --rm \
    --init \
    --privileged \
    --cgroupns=host \
    -v "$(pwd)":/workspace \
    -v sprite-go-home:/root \
    -v sprite-go-mod:/go/pkg \
    -e SPRITE_TEST_DOCKER=1 \
    -e SPRITE_URL="http://localhost:8080" \
    -e SPRITE_TOKEN="test-token-12345" \
    -e SPRITE_DISABLE_ADMIN_CHANNEL=true \
    -e SPRITE_TEST_QUIET_PHX=true \
    ${SPRITE_LOG_LEVEL:+-e SPRITE_LOG_LEVEL="$SPRITE_LOG_LEVEL"} \
    "$IMAGE_NAME" \
    ./scripts/run-tests.sh $@

EXIT_CODE=$?

# Verify cleanup
REMAINING_LOOPS=$(docker run --rm --privileged "$IMAGE_NAME" losetup -a 2>/dev/null || true)
if [ -n "$REMAINING_LOOPS" ]; then
    echo ""
    echo "ERROR: Tests did not clean up loopback devices:"
    echo "$REMAINING_LOOPS"
    exit 1
fi

exit $EXIT_CODE
