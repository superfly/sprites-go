#!/bin/bash
# Initialize v0 checkpoint for empty environment

set -e

# Configuration
JUICEFS_MOUNT="${JUICEFS_MOUNT:-/mnt/juicefs}"
DATA_DIR="${JUICEFS_MOUNT}/data"
CHECKPOINTS_DIR="${DATA_DIR}/checkpoints"
V0_DIR="${CHECKPOINTS_DIR}/v0"
ACTIVE_DIR="${DATA_DIR}/active"

echo "Initializing v0 checkpoint for empty environment..."
echo "JuiceFS mount: ${JUICEFS_MOUNT}"
echo "Data directory: ${DATA_DIR}"

# Check if JuiceFS is mounted
if [ ! -d "${DATA_DIR}" ]; then
    echo "Error: JuiceFS data directory not found at ${DATA_DIR}"
    echo "Please ensure JuiceFS is properly mounted."
    exit 1
fi

# Create checkpoints directory if it doesn't exist
if [ ! -d "${CHECKPOINTS_DIR}" ]; then
    echo "Creating checkpoints directory..."
    mkdir -p "${CHECKPOINTS_DIR}"
fi

# Check if v0 already exists
if [ -d "${V0_DIR}" ]; then
    echo "v0 checkpoint already exists at ${V0_DIR}"
    echo "Contents:"
    ls -la "${V0_DIR}"
    exit 0
fi

# Create v0 directory
echo "Creating v0 checkpoint directory..."
mkdir -p "${V0_DIR}"

# Create basic structure for empty environment
echo "Setting up empty environment structure..."

# Create essential directories
mkdir -p "${V0_DIR}/fs"
mkdir -p "${V0_DIR}/home"
mkdir -p "${V0_DIR}/tmp"
mkdir -p "${V0_DIR}/var"

# Create marker file to indicate this is the initial checkpoint
echo "Initial empty environment checkpoint" > "${V0_DIR}/.v0-initial"
echo "Created: $(date -u +"%Y-%m-%dT%H:%M:%SZ")" >> "${V0_DIR}/.v0-initial"

# Create a minimal root filesystem structure if needed
if [ -f "${ACTIVE_DIR}/root-upper.img" ]; then
    echo "Found root-upper.img in active directory"
    # Create an empty sparse file for v0 (minimal size)
    echo "Creating minimal root-upper.img for v0..."
    truncate -s 100M "${V0_DIR}/root-upper.img"
    
    # Format it as ext4 if mkfs.ext4 is available
    if command -v mkfs.ext4 &> /dev/null; then
        mkfs.ext4 -q "${V0_DIR}/root-upper.img" 2>/dev/null || true
    fi
fi

# Set appropriate permissions
chmod 755 "${V0_DIR}"
chmod 755 "${V0_DIR}/fs" 2>/dev/null || true
chmod 755 "${V0_DIR}/home" 2>/dev/null || true
chmod 1777 "${V0_DIR}/tmp" 2>/dev/null || true

echo "v0 checkpoint created successfully at ${V0_DIR}"
echo ""
echo "Contents:"
ls -la "${V0_DIR}"

# Update checkpoint database if it exists
DB_PATH="${DATA_DIR}/checkpoints.db"
if [ -f "${DB_PATH}" ]; then
    echo ""
    echo "Updating checkpoint database..."
    # Check if v0 record exists
    if ! sqlite3 "${DB_PATH}" "SELECT COUNT(*) FROM sprite_checkpoints WHERE path = 'checkpoints/v0';" 2>/dev/null | grep -q "1"; then
        # Insert v0 record if it doesn't exist
        sqlite3 "${DB_PATH}" "INSERT OR IGNORE INTO sprite_checkpoints (path, parent_id) VALUES ('checkpoints/v0', NULL);" 2>/dev/null || true
        echo "Added v0 checkpoint to database"
    else
        echo "v0 checkpoint already in database"
    fi
fi

echo ""
echo "v0 checkpoint initialization complete!"
echo "This represents an empty environment state that can be restored to."