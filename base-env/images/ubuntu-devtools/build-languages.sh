#!/bin/bash
set -e

echo "Building sprite languages image..."

# Use host network on Linux only (unsupported on macOS/Windows)
NETWORK_ARGS=()
if [ "$(uname -s)" = "Linux" ]; then
  NETWORK_ARGS+=(--network host)
fi

# Build the runnable languages-complete stage explicitly
docker build \
    "${NETWORK_ARGS[@]}" \
    --progress plain \
    --build-arg BUILDKIT_INLINE_CACHE=1 \
    --target languages-complete \
    -t sprite-languages-complete \
    .

echo "Build completed successfully!"
echo ""
echo "To test the image:"
echo "  docker run --rm -it sprite-languages-complete bash"
echo ""
echo "To check installed languages:"
echo "  docker run --rm sprite-languages-complete bash -c 'node --version && python3 --version && ruby --version'"

