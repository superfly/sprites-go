#!/bin/bash
trap 'echo "fs-ready.sh: received signal $1"' SIGTERM SIGINT SIGKILL

# Simulate juicefs mount startup
echo "fs: checking juicefs mount status..."
sleep 0.2
echo "fs: juicefs mount is active"
echo "fs: checking filesystem health..."
sleep 0.3
echo "fs: filesystem is healthy"
echo "fs: checking metadata service..."
sleep 0.2
echo "fs: metadata service is healthy"
echo "fs ready"
exit 0 