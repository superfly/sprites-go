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

EXTRA_ARGS="$*"

# Run a single container with the provided go test command
run_in_container() {
    local name="$1"
    local cmd="$2"
    echo "Running $name tests in container..."
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
        bash -lc "$cmd"
}

# Build default args unless provided by user
build_default_args() {
    local user_args="$1"
    local defaults=""
    if ! echo " $user_args " | grep -qE '(^|[[:space:]])-v($|[[:space:]])'; then
        defaults+=" -v"
    fi
    if ! echo " $user_args " | grep -qE '(^|[[:space:]])-failfast($|[[:space:]])'; then
        defaults+=" -failfast"
    fi
    if ! echo " $user_args " | grep -qE '(^|[[:space:]])-timeout(=|[[:space:]]|$)'; then
        defaults+=" -timeout=5m"
    fi
    echo "$defaults"
}

# If first arg looks like a package path (directory or with /...), run only that path's tests
if [ "$#" -gt 0 ] && [[ ! "$1" =~ ^- ]]; then
    ORIGINAL_PATH="$1"
    CANDIDATE_DIR="$ORIGINAL_PATH"
    if [[ "$ORIGINAL_PATH" == */... ]]; then
        CANDIDATE_DIR="${ORIGINAL_PATH%/...}"
    fi
    if [ -d "$CANDIDATE_DIR" ] || [ -d "./$CANDIDATE_DIR" ]; then
        shift
        EXTRA_ARGS="$*"
        DEFAULT_ARGS="$(build_default_args "$EXTRA_ARGS")"
        if [[ "$ORIGINAL_PATH" == */... ]]; then
            PKG_ARG="$ORIGINAL_PATH"
        else
            PKG_ARG="./$(echo "$CANDIDATE_DIR" | sed 's#^\./##')/..."
        fi
        CMD="go test$DEFAULT_ARGS $EXTRA_ARGS $PKG_ARG"
        if run_in_container "$PKG_ARG" "$CMD"; then
            echo "PASS $PKG_ARG"
            echo "All tests passed."
            exit 0
        else
            echo "FAIL $PKG_ARG"
            exit 1
        fi
    fi
fi

# Enumerate pkg subdirectories that contain tests and run each in its own container
ANY_PKG_RAN=0
DEFAULT_ARGS="$(build_default_args "$EXTRA_ARGS")"
for dir in pkg/*; do
    if [ -d "$dir" ]; then
        if find "$dir" -type f -name "*_test.go" -print -quit | grep -q .; then
            ANY_PKG_RAN=1
            PKG_NAME="$(basename "$dir")"
            CMD="go test$DEFAULT_ARGS $EXTRA_ARGS ./$dir/..."
            if run_in_container "pkg/$PKG_NAME" "$CMD"; then
                echo "PASS pkg/$PKG_NAME"
            else
                echo "FAIL pkg/$PKG_NAME"
                exit 1
            fi
        fi
    fi
done

if [ "$ANY_PKG_RAN" -eq 0 ]; then
    echo "No pkg/* tests found. Skipping pkg tests."
fi

# Run server tests in their own container
SERVER_CMD="go test$DEFAULT_ARGS $EXTRA_ARGS ./server/..."
if run_in_container "server" "$SERVER_CMD"; then
    echo "PASS server"
    echo "All tests passed."
else
    echo "FAIL server"
    exit 1
fi