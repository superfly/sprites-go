#!/bin/bash
set -e

if [ -z "$CHECKPOINT_ID" ]; then
    echo "ERROR: No checkpoint ID provided"
    echo "Usage: $0 <checkpoint-id>"
    exit 1
fi

# Derive JuiceFS paths from SPRITE_WRITE_DIR
JUICEFS_BASE="${SPRITE_WRITE_DIR}/juicefs"
JUICEFS_MOUNT_POINT="${JUICEFS_BASE}/data"
ACTIVE_DIR="${JUICEFS_MOUNT_POINT}/active"
CHECKPOINTS_DIR="${JUICEFS_MOUNT_POINT}/checkpoints"
CHECKPOINT_PATH="$CHECKPOINTS_DIR/$CHECKPOINT_ID"

# Ensure checkpoints directory exists
mkdir -p "$CHECKPOINTS_DIR"

# Check if active directory exists
if [ ! -d "$ACTIVE_DIR" ]; then
    echo "ERROR: Active directory does not exist at $ACTIVE_DIR"
    exit 1
fi

# Check if checkpoint already exists
if [ -e "$CHECKPOINT_PATH" ]; then
    echo "ERROR: Checkpoint $CHECKPOINT_ID already exists at $CHECKPOINT_PATH"
    exit 1
fi

# Clone active directory to checkpoint
echo "Creating checkpoint $CHECKPOINT_ID..."
juicefs clone "$ACTIVE_DIR" "$CHECKPOINT_PATH"

echo "Checkpoint created successfully at $CHECKPOINT_PATH"
exit 0 