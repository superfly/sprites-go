#!/bin/bash
# CPU burner that runs for a specified duration
# Usage: cpu-burner.sh <duration_seconds>

duration=${1:-5}
end=$(($(date +%s) + duration))

# Burn CPU by doing math in a loop
while [ $(date +%s) -lt $end ]; do
    # Do some CPU-intensive work
    for i in {1..1000}; do
        echo "scale=10; 4*a(1)" | bc -l > /dev/null 2>&1 || echo $((i * i * i))
    done
done

echo "CPU burn complete after ${duration}s"


