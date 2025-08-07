#!/bin/bash
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

echo "=== JavaScript SDK Tests ==="

# Check if Node.js is available
if ! command -v node &> /dev/null; then
    echo "Error: Node.js is not installed"
    exit 1
fi

NODE_VERSION=$(node --version | sed 's/v//' | cut -d. -f1)
if [ "$NODE_VERSION" -lt 18 ]; then
    echo "Error: Node.js 18 or higher is required (found v$(node --version))"
    exit 1
fi

echo "Using Node.js $(node --version)"

# Install dependencies if needed
if [ ! -d "node_modules" ]; then
    echo "Installing dependencies..."
    npm install
fi

# Build the TypeScript sources
echo "Building TypeScript sources..."
npm run build

# Run unit tests
echo "Running unit tests..."
npm test

# Run integration tests
echo "Running integration tests..."
npm run test:integration

# Test CLI wrapper with test harness
if [ -n "$SPRITE_CLIENT_BINARY" ] && [ "$SPRITE_CLIENT_BINARY" = "$(pwd)/sprite-cli" ]; then
    echo "Running test harness against JavaScript CLI..."
    cd ../test-harness
    ./sprite-test-harness
    cd ../javascript
fi

echo "JavaScript SDK tests completed successfully!"