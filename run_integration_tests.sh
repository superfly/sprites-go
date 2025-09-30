#!/bin/bash

# Integration test runner for the Go SDK
# This script runs the integration tests that require a real API token
# Tests cover: sprite creation, exec commands (echo, pwd, env, dir, error handling, pipes, TTY mode), and sprite deletion

set -e

echo "Running Go SDK Integration Tests"
echo "================================"

# Check if test token is provided
if [ -z "$SPRITES_TEST_TOKEN" ]; then
    echo "Error: SPRITES_TEST_TOKEN environment variable is required"
    echo "Please set it with: export SPRITES_TEST_TOKEN=your_token_here"
    exit 1
fi

echo "Using test token: ${SPRITES_TEST_TOKEN:0:10}..."

# Run the integration tests
echo "Running integration tests..."
go test -v -run "TestSprite" -timeout 2m

echo ""
echo "Integration tests completed successfully!"
