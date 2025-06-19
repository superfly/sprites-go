#!/bin/bash
set -e

# Check required environment variables
missing_vars=""
found_vars=""
for var in "S3_ACCESS_KEY" "S3_SECRET_KEY" "S3_ENDPOINT" "BUCKET_NAME"; do
    if [ -z "${!var}" ]; then
        missing_vars="$missing_vars $var"
    else
        found_vars="$found_vars $var"
    fi
done

if [ ! -z "$missing_vars" ]; then
    echo "ERROR: The following required environment variables are missing:$missing_vars"
    if [ ! -z "$found_vars" ]; then
        echo "Found environment variables:$found_vars"
    fi
    exit 1
fi

# Check if vde device exists
if ! lsblk | grep -q "vde"; then
  echo "Error: vde device not found"
  exit 1
fi

# Check if a partition with the litestream_data label exists
if ! blkid | grep -q "LABEL=\"litestream_data\""; then
  echo "No litestream_data partition found, creating a 2GB partition..."
  
  # Create a new partition using parted
  parted -s /dev/vde mklabel gpt
  parted -s /dev/vde mkpart primary ext4 0% 2GiB
  
  # Wait a moment for the kernel to recognize the new partition
  sleep 2
  
  # Format the partition with ext4 and add a label
  mkfs.ext4 -L litestream_data /dev/vde1
  
  echo "Partition created and formatted with ext4 (label: litestream_data)"
fi

# Create mount directory if it doesn't exist
mkdir -p /data/litestream

# Mount the partition if it's not already mounted
if ! grep -q "/data/litestream" /proc/mounts; then
  mount LABEL=litestream_data /data/litestream
  echo "Mounted litestream_data partition at /data/litestream"
else
  echo "litestream_data partition is already mounted at /data/litestream"
fi

# Ensure sqlite db exists and isn't empty
DB_PATH="/data/litestream/juicefs.db"

if sqlite3 "$DB_PATH" ".tables" 2>/dev/null | grep -q .; then
  echo "Using sqlite db on disk"
else
  rm -f "$DB_PATH"
  echo "Restoring sqlite db from object storage"
  litestream restore -if-replica-exists "$DB_PATH"
fi

exec litestream replicate -config /etc/litestream.yml