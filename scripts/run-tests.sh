#!/bin/bash
set -e
set -o pipefail

# Check if running in Docker test container
if [ "${SPRITE_TEST_DOCKER}" != "1" ]; then
    echo "ERROR: This script must be run inside the Docker test container."
    echo "Please use 'make test' to run tests properly, don't be a bad person."
    exit 1
fi

# If arguments are provided, pass them directly as-is to go test
# Otherwise, use default packages with default flags
if [ "$#" -gt 0 ]; then
    TEST_ARGS="$@"
else
    TEST_ARGS="-failfast -p=8 ./pkg/... ./server/..."
fi

# Run tests through tparse for pretty output
if [ -n "${CI}" ] || [ -n "${GITHUB_ACTIONS}" ]; then
    # In CI: tee JSON to file for later processing
    mkdir -p test-results
    go test -json $TEST_ARGS | tee test-results/test.json | tparse -progress
    TEST_EXIT_CODE=$?
    
    # Generate markdown summary from JSON
    if [ -f test-results/test.json ]; then
        chmod 644 test-results/test.json
        cat test-results/test.json | tparse -format markdown > test-results/test-summary.md
        chmod 644 test-results/test-summary.md
    fi
else
    # Local: just pipe through tparse, no need to save
    go test -json $TEST_ARGS | tparse -progress
    TEST_EXIT_CODE=$?
fi

exit ${TEST_EXIT_CODE}