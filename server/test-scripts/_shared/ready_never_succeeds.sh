#!/bin/sh
echo "Running ready_never_succeeds.sh" >&2
echo "Checking component readiness..." >&2

# Set up signal handlers
_term() {
  echo "ready_never_succeeds.sh: received SIGTERM" >&2
  exit 0
}
_int() {
  echo "ready_never_succeeds.sh: received SIGINT" >&2  
  exit 0
}
trap _term SIGTERM
trap _int SIGINT

# Keep checking forever but never find ready state
while true; do
    echo "Still checking for readiness..." >&2
    sleep 1
done 