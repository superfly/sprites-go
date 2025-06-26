#!/bin/bash
set -e

# This script handles privileged mount operations
# Called by entrypoint.sh with sudo

echo "Setting up sprite home directory in durable storage..."

# Create the system directory structure in durable storage
mkdir -p /data/.system/home

# Check if sprite home directory exists in durable storage
if [ ! -d "/data/.system/home/sprite" ]; then
    echo "Initializing sprite home directory..."
    
    # Copy the original home directory to durable storage with permissions
    cp -a /home/sprite /data/.system/home/
    
    # Ensure proper ownership
    chown -R sprite:sprite /data/.system/home/sprite
    
    echo "Sprite home directory initialized in /data/.system/home/sprite"
else
    echo "Using existing sprite home directory from durable storage"
fi

# Bind mount the durable home directory over the original location
mount --bind /data/.system/home/sprite /home/sprite

echo "Sprite home directory mounted from durable storage" 