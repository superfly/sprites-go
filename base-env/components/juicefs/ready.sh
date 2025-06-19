#!/bin/bash
set -e

# Derive JuiceFS mount point from SPRITE_WRITE_DIR
JUICEFS_BASE="${SPRITE_WRITE_DIR}/juicefs"
JUICEFS_MOUNT_POINT="${JUICEFS_BASE}/data"

# Read from stdin looking for "juicefs is ready"
while IFS= read -r line; do
    echo "$line"  # Echo the line for transparency
    if [[ "$line" == *"juicefs is ready"* ]]; then
        # JuiceFS is ready, create the active directory
        mkdir -p "${JUICEFS_MOUNT_POINT}/active"
        echo "JuiceFS ready: created active directory at ${JUICEFS_MOUNT_POINT}/active"
        exit 0
    fi
done

# If we get here, we didn't see the ready message
echo "ERROR: Did not receive 'juicefs is ready' message"
exit 1 