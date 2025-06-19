#!/bin/bash
set -e

# Get checkpoint ID from first argument or environment variable
CHECKPOINT_ID="${1:-${SPRITE_RESTORE_ID}}"

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

# Check if checkpoint exists
if [ ! -e "$CHECKPOINT_PATH" ]; then
    echo "ERROR: Checkpoint $CHECKPOINT_ID does not exist at $CHECKPOINT_PATH"
    exit 1
fi

# If active directory exists, back it up
if [ -d "$ACTIVE_DIR" ]; then
    # Create backup name with timestamp
    TIMESTAMP=$(date +%s)
    BACKUP_NAME="pre-restore-${CHECKPOINT_ID}-${TIMESTAMP}"
    BACKUP_PATH="$CHECKPOINTS_DIR/$BACKUP_NAME"
    
    echo "Backing up current active directory to $BACKUP_PATH..."
    mv "$ACTIVE_DIR" "$BACKUP_PATH"
    echo "Backup completed"
fi

# Clone checkpoint to active directory
echo "Restoring from checkpoint $CHECKPOINT_ID..."
juicefs clone "$CHECKPOINT_PATH" "$ACTIVE_DIR"

echo "Restore completed successfully from $CHECKPOINT_PATH to $ACTIVE_DIR"
exit 0 