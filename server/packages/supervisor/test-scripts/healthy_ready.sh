#!/bin/sh
echo "Running healthy_ready.sh" >&2

# Set up signal handlers
_term() {
  echo "healthy_ready.sh: received SIGTERM" >&2
  exit 0
}
_int() {
  echo "healthy_ready.sh: received SIGINT" >&2
  exit 0
}
trap _term SIGTERM
trap _int SIGINT

echo "Waiting for component health status..." >&2

# Read from stdin line by line, looking for the health check message  
while read line; do
    echo "healthy_ready.sh: saw: $line" >&2
    
    if echo "$line" | grep -q "Component health: healthy"; then
        echo "healthy_ready.sh: found healthy status - ready!" >&2
        echo "Component ready"
        exit 0
    fi
done

# If we reach here, stdin closed without finding the ready message
echo "healthy_ready.sh: stdin closed without finding health status" >&2
exit 1 