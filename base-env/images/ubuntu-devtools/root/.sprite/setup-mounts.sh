#!/bin/bash
set -e

# This script handles migration from /data/.system/home to /home/
# Called by entrypoint.sh with sudo

echo "Checking for existing sprite home directory in durable storage..."

# Check if /data/.system/home exists and has content
if [ -d "/data/.system/home" ] && [ "$(ls -A /data/.system/home 2>/dev/null)" ]; then
    echo "Found existing sprite home directory in /data/.system/home"
    echo "Moving files to /home/..."
    
    # Move all contents from /data/.system/home to /home/ recursively
    # Using rsync to handle potential conflicts and preserve permissions
    rsync -av /data/.system/home/ /home/
    
    # Ensure proper ownership of moved files
    chown -R sprite:sprite /home/sprite
    
    echo "Files moved successfully from /data/.system/home to /home/"
    
    # Remove the /data/.system/home directory
    rm -rf /data/.system/home
    
    echo "Cleaned up /data/.system/home directory"
else
    echo "No existing sprite home directory found in /data/.system/home"
fi

echo "Sprite home directory setup complete" 