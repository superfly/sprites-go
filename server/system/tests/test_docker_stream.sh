#!/bin/bash
# Test script for Docker TTY exec endpoint

set -e

# Default values
API_URL="${SPRITE_API_URL:-http://localhost:8080}"
API_TOKEN="${SPRITE_HTTP_API_TOKEN:-}"

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo "Testing Docker TTY exec endpoint..."

# Test 1: Regular NDJSON mode
echo -n "Test 1: Regular NDJSON mode... "
RESPONSE=$(curl -s -X POST \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer ${API_TOKEN}" \
  -d '{
    "command": ["echo", "hello world"],
    "timeout": 5000000000,
    "docker_tty": false
  }' \
  "${API_URL}/exec")

if echo "$RESPONSE" | grep -q '"type":"stdout".*"data":"hello world"'; then
  echo -e "${GREEN}PASS${NC}"
else
  echo -e "${RED}FAIL${NC}"
  echo "Response: $RESPONSE"
  exit 1
fi

# Test 2: Docker stream mode (binary format)
echo -n "Test 2: Docker stream mode... "
# We'll use a Python script to parse the binary format
PYTHON_SCRIPT=$(cat <<'EOF'
import sys
import struct

data = sys.stdin.buffer.read()
stdout_parts = []
stderr_parts = []

i = 0
while i < len(data):
    if i + 8 > len(data):
        break
    
    # Parse header
    stream_type = data[i]
    size = struct.unpack('>I', data[i+4:i+8])[0]
    
    if i + 8 + size > len(data):
        break
    
    # Extract payload
    payload = data[i+8:i+8+size]
    
    if stream_type == 1:  # stdout
        stdout_parts.append(payload.decode('utf-8', errors='replace'))
    elif stream_type == 2:  # stderr
        stderr_parts.append(payload.decode('utf-8', errors='replace'))
    
    i += 8 + size

print("STDOUT:", ''.join(stdout_parts))
print("STDERR:", ''.join(stderr_parts))
EOF
)

RESPONSE=$(curl -s -X POST \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer ${API_TOKEN}" \
  -d '{
    "command": ["bash", "-c", "echo stdout message && echo stderr message >&2"],
    "timeout": 5000000000,
    "docker_stream": true
  }' \
  "${API_URL}/exec" | python3 -c "$PYTHON_SCRIPT")

if echo "$RESPONSE" | grep -q "STDOUT: stdout message" && echo "$RESPONSE" | grep -q "STDERR: stderr message"; then
  echo -e "${GREEN}PASS${NC}"
else
  echo -e "${RED}FAIL${NC}"
  echo "Response: $RESPONSE"
  exit 1
fi

# Test 3: Content-Type header check
echo -n "Test 3: Content-Type header check... "
CONTENT_TYPE=$(curl -s -X POST -I \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer ${API_TOKEN}" \
  -d '{
    "command": ["echo", "test"],
    "timeout": 5000000000,
    "docker_stream": true
  }' \
  "${API_URL}/exec" | grep -i "content-type:" | cut -d' ' -f2 | tr -d '\r')

if [[ "$CONTENT_TYPE" == "application/vnd.docker.raw-stream" ]]; then
  echo -e "${GREEN}PASS${NC}"
else
  echo -e "${RED}FAIL${NC}"
  echo "Expected: application/vnd.docker.raw-stream"
  echo "Got: $CONTENT_TYPE"
  exit 1
fi

echo -e "\n${GREEN}All tests passed!${NC}"