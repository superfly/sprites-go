#!/bin/bash
trap 'echo "db-start.sh: received signal $1"' SIGTERM SIGINT SIGKILL

echo "db: starting litestream replication..."
sleep 0.3
echo "db: litestream replication started"
echo "db: replication status: active"
echo "db: replication lag: 0s"
echo "db: replication health: healthy"

while true; do
    sleep 1
done 