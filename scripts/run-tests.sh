#!/bin/bash
set -e
set -o pipefail

# Check if running in Docker test container
if [ "${SPRITE_TEST_DOCKER}" != "1" ]; then
    echo "ERROR: This script must be run inside the Docker test container."
    echo "Please use 'make test' to run tests properly, don't be a bad person."
    exit 1
fi

# Ensure dnsmasq is installed and has required capabilities inside the test container
if ! command -v dnsmasq >/dev/null 2>&1; then
    apt-get update >/dev/null 2>&1 || true
    apt-get install -y dnsmasq dnsmasq-base libcap2-bin >/dev/null 2>&1 || true
fi
if [ -x /usr/sbin/dnsmasq ]; then
    # Create dedicated user if missing and set required caps for nft + bind 53
    id -u sprite-net >/dev/null 2>&1 || useradd -r -s /usr/sbin/nologin sprite-net || true
    command -v setcap >/dev/null 2>&1 && setcap 'cap_net_bind_service,cap_net_admin+ep' /usr/sbin/dnsmasq || true
fi

# If arguments are provided, pass them directly as-is to go test
# Otherwise, use default packages with default flags (verbose by default)
if [ "$#" -gt 0 ]; then
    TEST_ARGS="$@"
else
    TEST_ARGS="-v -failfast -p=8 ./pkg/... ./server/..."
fi

# Ensure a default test timeout unless already provided
case " $TEST_ARGS " in
  *" -timeout="*) ;;
  *) TEST_ARGS="-timeout=180s $TEST_ARGS" ;;
esac

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