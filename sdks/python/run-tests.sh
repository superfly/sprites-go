#!/bin/bash
set -e

echo "Installing Python SDK and dependencies..."
cd /sdks/python

# Install the SDK in development mode
pip3 install -e .

# Install test dependencies
pip3 install pytest pytest-cov pytest-timeout pytest-mock

# Set environment for tests
export PYTHONPATH=/sdks/python
export SPRITE_SERVER_BINARY=dummy  # Integration tests use the running server

# Run tests
echo "Running Python SDK tests..."
python3 -m pytest tests/ -v --tb=short --timeout=60

echo "Python SDK tests completed successfully!"