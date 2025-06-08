#!/bin/bash
echo "DB: Running ready.sh" >&2
echo "DB: Waiting for Litestream replication to start..." >&2

# Read from stdin line by line, looking for the ready message
while read line; do
    echo "DB: ready.sh saw: $line" >&2
    
    if echo "$line" | grep -q "DB: Litestream replication started successfully. Monitoring for changes."; then
        echo "DB: Found ready message - DB component is ready." >&2
        echo "DB: Ready"
        exit 0
    fi
done

# If we reach here, stdin closed without finding the ready message
echo "DB: ready.sh: stdin closed without finding ready message" >&2
exit 1