#!/bin/bash
set -e

echo "Starting SDK test suite..."

# Start the sprite server in the background with a long-running process
echo "Starting sprite server..."
/usr/local/bin/spritectl -config /etc/sprite/test-config.json -- sleep infinity &
SERVER_PID=$!

# Give server a moment to start
sleep 3

# Wait for sprite server to be ready
echo "Waiting for sprite server to be ready..."
for i in {1..30}; do
    # Check if the port is listening
    if nc -z localhost 28080 2>/dev/null; then
        echo "Server is ready and listening on port 28080!"
        break
    fi
    if [ $i -eq 30 ]; then
        echo "Error: Server failed to start within 30 seconds"
        echo "Server process status:"
        ps aux | grep spritectl || true
        echo "Port check:"
        netstat -tlnp | grep 28080 || true
        kill $SERVER_PID 2>/dev/null || true
        exit 1
    fi
    sleep 1
done

# Run tests for each SDK
echo ""
echo "=== Running Python SDK tests ==="
cd /sdks/python
if [ -f run-tests.sh ]; then
    ./run-tests.sh
else
    echo "Warning: No run-tests.sh found for Python SDK"
fi

# Build and run test harness against the real sprite client
echo ""
echo "=== Building test harness ==="
cd /sdks/test-harness
go build -o sprite-test-harness .

echo ""
echo "=== Running test harness against real sprite client ==="
export SPRITE_URL="http://localhost:28080"
export SPRITE_TOKEN="f0e4c2f76c58916ec258f246851bea091d14d4247a2fc3e18694461b1816e13b"
export SPRITE_CLIENT_BINARY=/usr/local/bin/sprite
./sprite-test-harness

# Run test harness against Python CLI wrapper
echo ""
echo "=== Running test harness against Python CLI wrapper ==="
export SPRITE_URL="http://localhost:28080"
export SPRITE_TOKEN="f0e4c2f76c58916ec258f246851bea091d14d4247a2fc3e18694461b1816e13b"
export SPRITE_CLIENT_BINARY=/sdks/python/sprite-cli
./sprite-test-harness

echo ""
echo "=== All tests completed successfully! ==="

# Clean up
echo "Stopping sprite server..."
kill $SERVER_PID 2>/dev/null || true
wait $SERVER_PID 2>/dev/null || true