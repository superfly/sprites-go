#!/bin/bash
set -euo pipefail

# Build the universal test image (no source copied; bind-mount at runtime)
docker build -f Dockerfile.test -t sprite-env-tests .

# Run tests inside the container against the live workspace (entrypoint handles JuiceFS)
docker run --rm --privileged \
  -e SPRITE_TEST_DOCKER=1 \
  -v "$(pwd)":/workspace \
  -w /workspace \
  sprite-env-tests \
  ./scripts/run-tests.sh "$@"


