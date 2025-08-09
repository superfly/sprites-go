# Checkpoint System Improvements

## Overview
This document describes the improvements made to the checkpoint and restore system to provide better visibility into environment state and proper initialization.

## Key Improvements

### 1. V0 Checkpoint for Empty Environment
- **Purpose**: Provides a baseline "empty environment" checkpoint that represents a clean slate
- **Location**: `checkpoints/v0/`
- **Creation**: Automatically created when environment first boots
- **Script**: `scripts/init_v0_checkpoint.sh` can manually create v0 if needed

### 2. Enhanced Checkpoint Listing
The `sprite checkpoint list` command now shows:
- **Active State**: Shows the current active environment at the top with "(active)" indicator
- **Statistics**: File count, directory count, and total size for each checkpoint
- **Divergence Indicator**: Shows how much the active state has diverged from the last checkpoint

#### Divergence Indicators:
- `✓ (no changes)` - Active is identical to last checkpoint
- `→ (minimal)` - Minor changes (< 10 files/MB)
- `→→ (moderate)` - Moderate changes (< 100 files/MB)
- `→→→ (significant)` - Significant changes (< 1000 files/MB)
- `→→→→ (major)` - Major changes (> 1000 files/MB)

### 3. Example Output

```
ID                        CREATED              FILES      DIRS           SIZE DIVERGENCE
------------------------- -------------------- ---------- ---------- --------------- --------------------
v3 (active)              2024-01-15 10:30:00       1250         85       2.34 GB →→ (moderate) (+42 files)
v3                       2024-01-15 10:00:00       1208         83       2.31 GB 
v2                       2024-01-15 09:30:00       1150         80       2.25 GB 
v1                       2024-01-15 09:00:00        950         75       1.98 GB 
v0                       2024-01-15 08:00:00         10          5       0.10 GB 
```

## Implementation Details

### New Components

1. **`packages/juicefs/checkpoint_stats.go`**
   - Calculates directory statistics (files, dirs, size)
   - Computes divergence between active and checkpoints
   - Provides formatted output with indicators

2. **`scripts/analyze_juicefs_db.py`**
   - Analyzes JuiceFS metadata database
   - Shows checkpoint structure and statistics
   - Helps understand storage usage

3. **`scripts/init_v0_checkpoint.sh`**
   - Creates initial v0 checkpoint
   - Sets up empty environment structure
   - Updates checkpoint database

### API Changes

Extended `CheckpointInfo` struct with optional statistics:
```go
type CheckpointInfo struct {
    ID         string    `json:"id"`
    CreateTime time.Time `json:"create_time"`
    // New statistics fields
    FileCount  int    `json:"file_count,omitempty"`
    DirCount   int    `json:"dir_count,omitempty"`
    TotalSize  int64  `json:"total_size,omitempty"`
    // Divergence info (only for active state)
    DivergenceIndicator string `json:"divergence,omitempty"`
    FilesDiff           int    `json:"files_diff,omitempty"`
    SizeDiff            int64  `json:"size_diff,omitempty"`
}
```

### Server-Side Changes

- `ListCheckpoints()` now attempts to gather statistics
- Falls back to basic listing if stats unavailable
- Includes divergence calculation for active state

### Client-Side Changes

- Enhanced display format with columns for stats
- Human-readable size formatting
- Clear divergence indicators
- Backward compatible with servers that don't provide stats

## Usage

### Creating Checkpoints
```bash
# Create a new checkpoint
sprite checkpoint create

# List all checkpoints with stats
sprite checkpoint list

# Get info about specific checkpoint
sprite checkpoint info v2
```

### Restoring from Checkpoint
```bash
# Restore to a specific checkpoint
sprite restore v0  # Return to empty environment
sprite restore v2  # Restore to checkpoint v2
```

### Monitoring Divergence
The divergence indicator helps understand:
- How much work would be lost if restored
- When it's time to create a new checkpoint
- Overall activity level in the environment

## Notes

### Sparse Disk Images
The system handles sparse disk images (like `root-upper.img`) correctly:
- File size shown is actual disk usage, not allocated size
- Sparse files appear smaller than their nominal size
- Efficient storage for mostly-empty disk images

### Database Structure
Checkpoints are tracked in SQLite database (`checkpoints.db`):
- Auto-incrementing version numbers
- Parent-child relationships for restore tracking
- Creation timestamps for all checkpoints

### Performance Considerations
- Statistics calculation is done efficiently using `filepath.WalkDir`
- Divergence calculation is lightweight (just comparing stats)
- Falls back gracefully if stats calculation fails

## Future Enhancements

Potential improvements for consideration:
1. Add checkpoint tagging/naming for important states
2. Implement checkpoint auto-creation on schedule
3. Add checkpoint size limits and rotation policies
4. Include process state in divergence calculation
5. Add checkpoint diff visualization
6. Implement incremental checkpoints for efficiency