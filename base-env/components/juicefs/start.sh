#!/bin/bash
set -e

# Derive JuiceFS paths from SPRITE_WRITE_DIR
JUICEFS_BASE="${SPRITE_WRITE_DIR}/juicefs"
JUICEFS_CACHE_DIR="${JUICEFS_BASE}/cache"
JUICEFS_META_DB="${JUICEFS_BASE}/metadata.db"
JUICEFS_MOUNT_POINT="${JUICEFS_BASE}/data"

# Create necessary directories
mkdir -p "${JUICEFS_CACHE_DIR}"
mkdir -p "$(dirname ${JUICEFS_META_DB})"
mkdir -p "${JUICEFS_MOUNT_POINT}"

# Set environment variables with default values that can be overridden
export META_URL="sqlite3://${JUICEFS_META_DB}" \
    MOUNT_POINT="${JUICEFS_MOUNT_POINT}" \
    CACHE_DIR="${JUICEFS_CACHE_DIR}"

for var in "SPRITE_S3_ACCESS_KEY" "SPRITE_S3_SECRET_ACCESS_KEY" "SPRITE_S3_ENDPOINT_URL" "SPRITE_S3_BUCKET"; do
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

# Get the configured bucket from environment
CONFIGURED_BUCKET="${SPRITE_S3_BUCKET}"

# Get the bucket from the existing metadata (if it exists)
EXISTING_BUCKET=$(sqlite3 "${JUICEFS_META_DB}" "select json_extract(value, '$.Bucket') from jfs_setting where name='format'" 2>/dev/null || echo "")

if [ -n "$EXISTING_BUCKET" ] && [ "$EXISTING_BUCKET" = "$CONFIGURED_BUCKET" ]; then
    echo "Using sqlite db on disk (bucket matches)"
else
    rm -f "${JUICEFS_META_DB}"
    rm -rf "$CACHE_DIR"
    echo "Restoring juicefs db from $CONFIGURED_BUCKET"
    litestream restore -if-replica-exists "${JUICEFS_META_DB}"
fi

# Ensure cache directory exists
mkdir -p "$CACHE_DIR"

# Calculate cache size as 80% of the available space in the cache directory
# Get the total size of the filesystem in MB where the cache directory is located
TOTAL_SIZE_KB=$(df -k "$CACHE_DIR" | awk 'NR==2 {print $2}')
TOTAL_SIZE_MB=$((TOTAL_SIZE_KB / 1024))
# Calculate 80% of the total size
CACHE_SIZE_MB=$((TOTAL_SIZE_MB * 80 / 100))

# Intentionally not printing access or secret keys for security

# Define volume name for the JuiceFS filesystem
JUICEFS_VOLUME_NAME="juicefs"
# Create mount point directory if it doesn't exist
mkdir -p "$MOUNT_POINT"

# Format the filesystem if it doesn't exist
if ! juicefs status "$META_URL" &>/dev/null; then
    # Format JuiceFS with the specified parameters, using correct S3-compatible endpoint format
    juicefs format \
        --storage s3 \
        --bucket "$SPRITE_S3_ENDPOINT_URL/$SPRITE_S3_BUCKET" \
        --access-key "$SPRITE_S3_ACCESS_KEY" \
        --secret-key "$SPRITE_S3_SECRET_ACCESS_KEY" \
        --trash-days 0 \
        "$META_URL" "$JUICEFS_VOLUME_NAME"
fi

# Calculate buffer size for JuiceFS (1GB or 20% of system memory, whichever is smaller)
MEM_TOTAL_KB=$(grep MemTotal /proc/meminfo | awk '{print $2}')
MEM_TWENTY_PERCENT=$((MEM_TOTAL_KB * 20 / 100))
MEM_ONE_GB=$((1024 * 1024)) # 1GB in KB

if [ $MEM_TWENTY_PERCENT -lt $MEM_ONE_GB ]; then
  BUFFER_SIZE=$MEM_TWENTY_PERCENT
else
  BUFFER_SIZE=$MEM_ONE_GB
fi

# Convert KB to MB for JuiceFS
BUFFER_SIZE_MB=$((BUFFER_SIZE / 1024))

echo "Using buffer size of $BUFFER_SIZE_MB MB"

# Set up command arguments
MOUNT_ARGS="--cache-dir=$CACHE_DIR --cache-size=$CACHE_SIZE_MB --buffer-size=$BUFFER_SIZE_MB"

if [ -n "$FS_MOUNT_OPTIONS" ]; then
    MOUNT_ARGS="$MOUNT_ARGS $FS_MOUNT_OPTIONS"
fi

# Create litestream configuration dynamically
LITESTREAM_CONFIG="/tmp/litestream-juicefs.yml"
cat > "$LITESTREAM_CONFIG" <<EOF
dbs:
  - path: ${JUICEFS_META_DB}
    replicas:
      - type: s3
        endpoint: ${SPRITE_S3_ENDPOINT_URL}
        bucket: ${SPRITE_S3_BUCKET}
        path: juicefs-metadata
        access-key-id: ${SPRITE_S3_ACCESS_KEY}
        secret-access-key: ${SPRITE_S3_SECRET_ACCESS_KEY}
        sync-interval: 1s
EOF

# Execute the mount command with all parameters
exec litestream replicate -config "$LITESTREAM_CONFIG" -exec "juicefs mount $MOUNT_ARGS \"$META_URL\" \"$MOUNT_POINT\""