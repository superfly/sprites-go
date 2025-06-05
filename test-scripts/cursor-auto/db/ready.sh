#!/bin/bash
trap 'echo "db-ready.sh: received signal $1"' SIGTERM SIGINT SIGKILL

# Simulate litestream replication startup
echo "db: waiting for litestream replication to start..."
sleep 0.3
echo "db: litestream replication started"
echo "db: waiting for replication to catch up..."
sleep 0.2
echo "db: replication caught up"
echo "db ready"
exit 0 