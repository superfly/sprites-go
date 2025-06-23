# Checkpoint Versioning System

## Code Organization

The checkpoint functionality is implemented in `checkpoint.go` within the juicefs package. This includes:
- `CheckpointInfo` struct - Contains checkpoint metadata (ID, create time, history)
- Checkpoint methods:
  - `Checkpoint()` - Creates a checkpoint with auto-generated version
  - `CheckpointWithVersion()` - Creates checkpoint and returns the version used
  - `Restore()` - Restores from a checkpoint (with pre-restore checkpoint)
  - `ListCheckpoints()` - Lists all checkpoints
  - `ListCheckpointsReverse()` - Lists checkpoints in reverse chronological order
  - `ListCheckpointsWithHistory()` - Finds checkpoints with specific version in history
  - `GetCheckpoint()` - Gets details of a specific checkpoint
- Version management functions:
  - `getCurrentVersion()` - Reads current version with file locking
  - `initializeVersion()` - Creates initial version file
  - `appendToHistory()` - Appends restore records to history

## Overview

The checkpoint system uses auto-generated version numbers instead of user-specified IDs. This ensures unique, sequential checkpoint identifiers and tracks the restore history of the active directory.

## Version Flow

1. **Initial State**: 
   - `active/.version` contains `v0`
   - `active/.history` is empty (no restore operations yet)

2. **Creating Checkpoint**:
   - Read current version from `active/.version` (e.g., `v0`)
   - Create checkpoint directory `checkpoints/v0/`
   - Increment `active/.version` to `v1`

3. **Restoring from Checkpoint**:
   - Create a checkpoint of current state (auto-increments version)
   - Save current version from `active/.version`
   - Restore checkpoint content to `active/`
   - Write back the saved version to `active/.version`
   - Append to `active/.history`: `to=<current-version>;time=<timestamp>`

## Version Management

### Initial State
When the JuiceFS system starts, it creates an `active/.version` file containing `v0`, indicating the initial version.

### Creating Checkpoints
- When a checkpoint is created, the system:
  1. Acquires an exclusive lock on `active/.version`
  2. Reads the current version (e.g., `v0`)
  3. Creates a checkpoint directory named with that version (e.g., `checkpoints/v0`)
  4. Increments the version in `active/.version` (e.g., to `v1`)
  5. Releases the lock

- This ensures that each checkpoint has a unique version number and the active directory always reflects the next version to be used.

### API Changes
- Creating a checkpoint no longer requires a checkpoint ID
- POST `/checkpoint` with an empty body (or any body - the checkpoint_id field is ignored)
- The system automatically assigns the next version number

## History Tracking

The `.history` file tracks all restore operations by recording which version the system is at after each restore:
```
to=v0;time=2024-01-15T10:00:00Z
to=v2;time=2024-01-15T10:30:00Z
to=v5;time=2024-01-15T11:00:00Z
```

The `to=` field indicates the current version number after the restore operation completed, not the checkpoint that was restored from. Each checkpoint preserves its own `.history` file, so the full restore chain is maintained.

## Listing Checkpoints

### Default Listing
- `GET /checkpoints` returns checkpoints in reverse chronological order (newest first)
- The active state appears at the top of the list with suffix "(active)" (e.g., "v8 (active)")
- Each checkpoint includes its version ID, creation time, and source ID (if it was created from a restore)

### History Filtering
- `GET /checkpoints?history=v0` returns all checkpoints that have `v0` in their restore history
- This uses a grep-like search through all `.history` files in the checkpoints directory
- Output format: `<checkpoint>/.history: to=<version>;time=<timestamp>`

## Client Usage

### Creating a Checkpoint
```bash
sprite-client checkpoint create
# No longer requires a checkpoint ID argument
```

### Listing Checkpoints
```bash
# List all checkpoints (newest first)
# The active version appears at the top with "(active)" suffix
sprite-client checkpoint list

# Find all checkpoints restored to v0
sprite-client checkpoint list --history v0
```

### Getting Checkpoint Information
```bash
# Get info about a specific checkpoint
sprite-client checkpoint info v3

# Get info about the active state
sprite-client checkpoint info active

# You can also use the current version number to get active info
# e.g., if active is v8, both of these work:
sprite-client checkpoint info v8
sprite-client checkpoint info active
```

### Restoring a Checkpoint
```bash
sprite-client checkpoint restore v0
# Uses the version ID (v0, v1, v2, etc.)
```

## Migration Notes

- Existing checkpoints with custom IDs will continue to work
- The system only enforces version numbering for new checkpoints
- The `.source` file in checkpoints is deprecated in favor of `.history` in the active directory 