#!/bin/sh
echo "Running healthy_start.sh"

# Set up signal handlers
_term() {
  echo "healthy_start.sh: received SIGTERM"
  exit 0
}
_int() {
  echo "healthy_start.sh: received SIGINT"
  exit 0
}
trap _term SIGTERM
trap _int SIGINT

echo "Starting component..."
sleep 0.3
echo "Component started successfully"
echo "Component health: healthy"

# Keep running
while true; do
    sleep 1
done 