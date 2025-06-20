#!/bin/bash
set -euo pipefail

# Debug function
function debug() {
    if [[ "${APP_STORAGE_DEBUG:-false}" == "true" ]]; then
        echo "$@"
    fi
}

# Define paths based on SPRITE_WRITE_DIR
SPRITE_WRITE_DIR="/dev/fly_vol"
JUICEFS_BASE="${SPRITE_WRITE_DIR}/juicefs"
JUICEFS_DATA="${JUICEFS_BASE}/data"
APP_STORAGE_IMG="${JUICEFS_DATA}/active/app-storage.img"

# Create mount points
mkdir -p /mnt/app-storage

# Mount the sparse image
mount -o loop "$APP_STORAGE_IMG" /mnt/app-storage

# Create directories for overlay
mkdir -p /mnt/app-storage/{upper,work}

mkdir -p /mnt/newroot

# Mount the overlay
mount -t overlay overlay -o lowerdir=/mnt/app-image,upperdir=/mnt/app-storage/upper,workdir=/mnt/app-storage/work /mnt/newroot