#!/bin/bash
# Memory hog that allocates and holds memory
# Usage: memory-hog.sh <size_mb> <duration_seconds>

size_mb=${1:-100}
duration=${2:-5}

# Create a large string in memory
data=""
mb_size=$((1024 * 1024))
chunk_size=$((mb_size / 100))  # 10KB chunks

echo "Allocating ${size_mb}MB of memory..."

# Build up memory usage
for ((mb=0; mb<size_mb; mb++)); do
    for ((i=0; i<100; i++)); do
        # Generate 10KB of data
        new_data=$(head -c $chunk_size </dev/urandom | base64 2>/dev/null || dd if=/dev/urandom bs=1024 count=10 2>/dev/null | base64)
        data="${data}${new_data}"
    done
    if ((mb % 10 == 0)); then
        echo "Allocated $((mb))MB..."
    fi
done

echo "Holding ${size_mb}MB for ${duration}s..."
sleep $duration

echo "Memory hog complete"


