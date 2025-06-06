#!/bin/bash
echo "db: starting litestream checkpoint..."
sleep 0.2
echo "db: checkpointing database..."
sleep 0.3
echo "db: checkpoint complete"
echo "db: uploading checkpoint to S3..."
sleep 0.2
echo "db: checkpoint uploaded successfully"
exit 0 