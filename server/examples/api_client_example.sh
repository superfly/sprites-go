#!/bin/bash

# Example script demonstrating sprite-env HTTP API usage

# Configuration
API_URL="${API_URL:-http://localhost:8090}"
API_TOKEN="${SPRITE_HTTP_API_TOKEN:-your-secret-token}"

# Helper function to make authenticated requests
api_request() {
    local method=$1
    local endpoint=$2
    local data=$3
    local mode="${4:-api}"  # Default to api mode
    
    if [ "$mode" = "api" ]; then
        auth_header="state=api:${API_TOKEN}"
    else
        # For proxy mode, the third parameter in data is the port
        auth_header="state=${mode}"
    fi
    
    if [ -z "$data" ]; then
        curl -s -X "$method" \
            -H "fly-replay-src: ${auth_header}" \
            "${API_URL}${endpoint}"
    else
        curl -s -X "$method" \
            -H "fly-replay-src: ${auth_header}" \
            -H "Content-Type: application/json" \
            -d "$data" \
            "${API_URL}${endpoint}"
    fi
}

echo "=== Sprite-env API Client Example ==="
echo "Using API server at: ${API_URL}"
echo ""

# Example 1: Execute a simple command
echo "=== Example 1: Execute a simple command ==="
response=$(api_request POST /exec '{
    "command": ["echo", "Hello from sprite-env API!"],
    "timeout": 5000000000
}')
echo "$response"
echo

# Example 2: Execute a command with both stdout and stderr
echo "=== Example 2: Command with stdout and stderr ==="
response=$(api_request POST /exec '{
    "command": ["sh", "-c", "echo This is stdout; echo This is stderr >&2"],
    "timeout": 5000000000
}')
echo "$response"
echo

# Example 3: Execute a long-running command with timeout
echo "=== Example 3: Long-running command (will timeout) ==="
response=$(api_request POST /exec '{
    "command": ["sleep", "10"],
    "timeout": 2000000000
}')
echo "$response"
echo

# Example 4: Create a checkpoint
echo "=== Example 4: Create checkpoint ==="
checkpoint_id="checkpoint-$(date +%Y%m%d-%H%M%S)"
response=$(api_request POST /checkpoint "{
    \"checkpoint_id\": \"${checkpoint_id}\"
}")
echo "$response"
echo

# Example 5: Restore from checkpoint
echo "=== Example 5: Restore from checkpoint ==="
response=$(api_request POST /restore "{
    \"checkpoint_id\": \"${checkpoint_id}\"
}")
echo "$response"
echo

# Example 6: Error handling - invalid command
echo "=== Example 6: Error handling ==="
response=$(api_request POST /exec '{
    "command": [],
    "timeout": 5000000000
}')
echo "$response"
echo

# Example 7: Proxy mode - access internal service
echo "=== Example 7: Proxy to internal service on port 3000 ==="
# This assumes you have a service running on port 3000
response=$(api_request GET /health "" "proxy:${API_TOKEN}:3000")
echo "$response"
echo

# Example 8: Proxy mode with POST request
echo "=== Example 8: Proxy POST to internal service ==="
# This proxies a POST request to an internal API
response=$(api_request POST /api/data '{"key": "value"}' "proxy:${API_TOKEN}:3000")
echo "$response"
echo

# Example 9: Using curl directly with proper formatting
echo "=== Example 9: Direct curl commands ==="
echo "Direct checkpoint command:"
echo "curl -X POST ${API_URL}/checkpoint \\"
echo "  -H 'fly-replay-src: state=api:${API_TOKEN}' \\"
echo "  -H 'Content-Type: application/json' \\"
echo "  -d '{\"checkpoint_id\": \"manual-checkpoint\"}'"
echo

echo "Direct proxy command:"
echo "curl -X GET ${API_URL}/api/status \\"
echo "  -H 'fly-replay-src: state=proxy:${API_TOKEN}:3000'"
echo

# Note about authentication
echo "=== Authentication Notes ==="
echo "- Set SPRITE_HTTP_API_TOKEN environment variable on the server"
echo "- Use 'state=api:token' for API endpoints (exec, checkpoint, restore)"
echo "- Use 'state=proxy:token:port' for proxying to internal services"
echo "- The fly-replay-src header can contain multiple semicolon-separated values"

echo "=== Examples Complete ==="
echo ""