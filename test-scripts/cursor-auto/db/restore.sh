#!/bin/bash
echo "db: checking for latest litestream checkpoint..."
sleep 0.2
echo "db: found checkpoint from 2024-03-20 15:30:00"
echo "db: downloading checkpoint from S3..."
sleep 0.3
echo "db: checkpoint downloaded"
echo "db: restoring database from checkpoint..."
sleep 0.4
echo "db: database restored successfully"
exit 0 