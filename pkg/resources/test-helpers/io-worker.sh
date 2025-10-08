#!/bin/bash
# IO worker that reads and writes data
# Usage: io-worker.sh <size_mb> <iterations>

size_mb=${1:-10}
iterations=${2:-5}
testfile="/tmp/io-test-$$"

echo "Starting IO workload: ${size_mb}MB x ${iterations} iterations"

for ((i=1; i<=iterations; i++)); do
    # Write data
    dd if=/dev/urandom of="$testfile" bs=1M count=$size_mb 2>/dev/null
    
    # Read data back
    dd if="$testfile" of=/dev/null bs=1M 2>/dev/null
    
    echo "Completed iteration $i/$iterations"
    sleep 0.1
done

# Cleanup
rm -f "$testfile"

echo "IO workload complete"


