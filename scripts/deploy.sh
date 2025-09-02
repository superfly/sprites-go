#!/bin/bash

# Save the current working directory
ORIGINAL_DIR=$(pwd)

# Change to the cmd directory
cd cmd || exit 1

# Run the deploy command
echo "Running deploy with config replacement..."
go run deploy.go -replace-config

# Capture the exit code
EXIT_CODE=$?

# Change back to the original directory
cd "$ORIGINAL_DIR"

# Exit with the same code as the go command
exit $EXIT_CODE
