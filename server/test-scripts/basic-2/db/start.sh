#!/bin/bash

echo "DB: Running start.sh"

_term() {
  echo "DB: Received SIGTERM. Shutting down Litestream replication..."
  # Simulate Litestream cleanup if any
  echo "DB: Litestream replication stopped."
  exit 0
}

_int() {
  echo "DB: Received SIGINT. Shutting down Litestream replication..."
  # Simulate Litestream cleanup if any
  echo "DB: Litestream replication stopped."
  exit 0
}

trap _term SIGTERM
trap _int SIGINT

echo "DB: Starting Litestream replication..."
# Simulate Litestream startup delay (e.g., 300ms)
sleep 0.3
echo "DB: Litestream replication started successfully. Monitoring for changes."
echo "DB: Started" # Retain original "Started" message for consistency with previous version

# Keep the script running
while true; do
  # In a real script, Litestream would be running here.
  # For simulation, we just sleep.
  sleep 1 &
  wait $! # Wait for sleep to ensure signal interruption works
done