#!/bin/sh
set -e

echo "Starting sprite-env test server..."

# Change to workspace directory
cd /workspace

# Build the server from the root directory
echo "Building sprite-server..."
go build -o /opt/sprite/sprite-server ./server

# Create test config with API token
cat > /opt/sprite/config.json << 'EOF'
{
  "log_level": "info",
  "log_json": false,
  "api_listen_addr": ":8080",
  "api_token": "test-token-12345",
  
  "process_command": ["sleep", "3600"],
  "process_working_dir": "/tmp",
  "process_environment": ["TEST_VAR=test_value"],
  "process_graceful_shutdown_timeout": "30s",
  
  "juicefs_enabled": false,
  "overlay_enabled": false,
  "container_enabled": false
}
EOF

# Start the server
echo "Starting server on port 8080..."
cd /opt/sprite
export SPRITE_HTTP_API_TOKEN=test-token-12345
exec ./sprite-server --config config.json
