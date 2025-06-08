#!/bin/bash
trap 'echo "db-ready.sh: received signal $1"' SIGTERM SIGINT SIGKILL

echo "db-ready.sh: waiting for replication health status..." >&2

# Read from stdin line by line, looking for the health check message
while read line; do
    echo "db-ready.sh: saw: $line" >&2
    
    if echo "$line" | grep -q "db: replication health: healthy"; then
        echo "db-ready.sh: found healthy status - ready!" >&2
        echo "db ready"
        exit 0
    fi
done

# If we reach here, stdin closed without finding the ready message
echo "db-ready.sh: stdin closed without finding health status" >&2
exit 1 