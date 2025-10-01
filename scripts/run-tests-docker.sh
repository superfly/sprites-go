#!/bin/bash
set -euo pipefail

IMAGE_NAME="sprite-env-tests"

# Check for running test containers and fail if any exist
RUNNING_CONTAINERS=$(docker ps --filter "ancestor=$IMAGE_NAME" --format "{{.ID}}" 2>/dev/null || true)
if [ -n "$RUNNING_CONTAINERS" ]; then
    echo "ERROR: Found running test containers from image $IMAGE_NAME:"
    docker ps --filter "ancestor=$IMAGE_NAME" --format "table {{.ID}}\t{{.Names}}\t{{.Status}}\t{{.RunningFor}}"
    echo ""
    echo "Please stop these containers before running tests:"
    echo "  docker stop $RUNNING_CONTAINERS"
    echo "Or force kill all test containers:"
    echo "  docker stop $RUNNING_CONTAINERS && docker rm $RUNNING_CONTAINERS"
    exit 1
fi

# Check if image exists, build if needed
if ! docker image inspect "$IMAGE_NAME" >/dev/null 2>&1; then
    echo "Test image not found, building..."
    echo "Building test Docker image..."
    docker build -f Dockerfile.test -t "$IMAGE_NAME" .
else
    echo "Using existing test image: $IMAGE_NAME"
fi

# Create volumes for caching if they don't exist
if ! docker volume inspect sprite-go-home >/dev/null 2>&1; then
    echo "Creating Go home cache volume..."
    docker volume create sprite-go-home
fi

if ! docker volume inspect sprite-go-mod >/dev/null 2>&1; then
    echo "Creating Go module cache volume..."
    docker volume create sprite-go-mod
fi

# Run the container in foreground mode - it will stop automatically when tests complete
echo "Running tests in container..."
docker run \
    --rm \
    --privileged \
    --cgroupns=host \
    -v "$(pwd)":/workspace \
    -v sprite-go-home:/root \
    -v sprite-go-mod:/go \
    -e SPRITE_TEST_DOCKER=1 \
    -e SPRITE_URL="http://localhost:8080" \
    -e SPRITE_TOKEN="test-token-12345" \
    -e SPRITE_DISABLE_ADMIN_CHANNEL=true \
    -e SPRITE_TEST_QUIET_PHX=true \
    "$IMAGE_NAME" \
    ${@:-go test -v ./...}