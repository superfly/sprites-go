#!/bin/bash
echo "FS: Running ready.sh" >&2
echo "FS: Waiting for JuiceFS to mount and be ready..." >&2

# Read from stdin line by line, looking for the ready message
while read line; do
    echo "FS: ready.sh saw: $line" >&2
    
    if echo "$line" | grep -q "FS: JuiceFS mounted and running. Monitoring file system operations."; then
        echo "FS: Found ready message - FS component is ready." >&2
        echo "FS: Ready"
        exit 0
    fi
done

# If we reach here, stdin closed without finding the ready message
echo "FS: ready.sh: stdin closed without finding ready message" >&2
exit 1