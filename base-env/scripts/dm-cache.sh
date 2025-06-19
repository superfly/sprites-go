#!/bin/bash
# The -x option prints each command before execution for debugging
# -e: exit on error, -u: error on undefined variables, -o pipefail: exit on pipe failures
set -euox pipefail

# Configuration
PHYSICAL_CACHE="/dev/fly_vol/physical-cache.img"
OBJECT_STORAGE_CACHE="/data/object-storage-cache.img"
DRBD_RESOURCE_NAME="cache_drbd"
DRBD_CONFIG_FILE="/etc/drbd.d/cache.res"
DRBD_DEVICE="/dev/drbd0"

# Calculate the size: total size of /dev/fly_vol minus 5GB
FLY_VOL_SIZE_KB=$(df -k /dev/fly_vol | awk 'NR==2 {print $2}')
RESERVE_GB=5
RESERVE_KB=$((RESERVE_GB * 1024 * 1024))
IMAGE_SIZE_KB=$((FLY_VOL_SIZE_KB - RESERVE_KB))

# Ensure we don't end up with a negative or too small size
if [ "$IMAGE_SIZE_KB" -lt 1024 ]; then
    echo "Error: Not enough space in /dev/fly_vol to create cache images"
    exit 1
fi

echo "Using disk images with size: $((IMAGE_SIZE_KB / 1024 / 1024))GB"

# Create physical cache disk image if it doesn't exist (WITHOUT FILESYSTEM)
if [ ! -f "$PHYSICAL_CACHE" ]; then
    echo "Creating physical cache disk image at $PHYSICAL_CACHE"
    mkdir -p "$(dirname "$PHYSICAL_CACHE")"
    dd if=/dev/zero of="$PHYSICAL_CACHE" bs=1K count=0 seek="$IMAGE_SIZE_KB"
else
    echo "Physical cache disk image already exists at $PHYSICAL_CACHE"
fi

# Create object storage cache disk image if it doesn't exist (WITHOUT FILESYSTEM)
if [ ! -f "$OBJECT_STORAGE_CACHE" ]; then
    echo "Creating object storage cache disk image at $OBJECT_STORAGE_CACHE"
    mkdir -p "$(dirname "$OBJECT_STORAGE_CACHE")"
    dd if=/dev/zero of="$OBJECT_STORAGE_CACHE" bs=1K count=0 seek="$IMAGE_SIZE_KB"
else
    echo "Object storage cache disk image already exists at $OBJECT_STORAGE_CACHE"
fi

# Create DRBD configuration if it doesn't exist
if [ ! -f "$DRBD_CONFIG_FILE" ]; then
    echo "Creating DRBD configuration..."
    mkdir -p "$(dirname "$DRBD_CONFIG_FILE")"
    
    # Create a DRBD configuration with valid syntax
    cat > "$DRBD_CONFIG_FILE" << EOF
resource $DRBD_RESOURCE_NAME {
  protocol C;
  
  disk {
    on-io-error detach;
  }
  
  net {
    max-buffers 8000;
    max-epoch-size 8000;
    after-sb-0pri discard-zero-changes;
    after-sb-1pri discard-secondary;
    after-sb-2pri disconnect;
  }
  
  syncer {
    verify-alg sha1;
  }
  
  on localhost {
    device    $DRBD_DEVICE;
    disk      $PHYSICAL_CACHE;
    meta-disk internal;
  }
  
  on remote {
    device    $DRBD_DEVICE;
    disk      $OBJECT_STORAGE_CACHE;
    meta-disk internal;
  }
}
EOF
    echo "DRBD configuration created at $DRBD_CONFIG_FILE"
else
    echo "DRBD configuration already exists at $DRBD_CONFIG_FILE"
fi

# Check if DRBD metadata exists before creating it
if ! drbdadm dump-md $DRBD_RESOURCE_NAME &>/dev/null; then
    echo "DRBD metadata not found. Creating DRBD metadata..."
    drbdadm -- --force create-md $DRBD_RESOURCE_NAME
else
    echo "DRBD metadata already exists, skipping creation"
fi

# Bring up the DRBD resource
echo "Bringing up DRBD resource..."
drbdadm up $DRBD_RESOURCE_NAME

# Set physical cache as primary (with force option)
echo "Setting physical cache as primary..."
drbdadm -- --force primary $DRBD_RESOURCE_NAME

# Configure asynchronous replication
echo "Configuring asynchronous replication..."
drbdadm adjust $DRBD_RESOURCE_NAME
drbdadm -- --protocol=A $DRBD_RESOURCE_NAME

# Wait for DRBD to settle
echo "Waiting for DRBD to initialize..."
sleep 5

# Check if DRBD device has a filesystem, create one if it doesn't
if ! blkid $DRBD_DEVICE | grep -q TYPE; then
    echo "Creating ext4 filesystem on DRBD device $DRBD_DEVICE"
    mkfs.ext4 $DRBD_DEVICE
else
    echo "Filesystem already exists on DRBD device $DRBD_DEVICE"
fi

echo "DRBD setup complete. Physical cache is primary, object storage is asynchronous replica."
echo "DRBD device $DRBD_DEVICE is ready for use with an ext4 filesystem."
