# SQLite-based Checkpoint System

The JuiceFS package now uses SQLite for checkpoint accounting instead of file-based tracking. This provides better consistency and tracking of checkpoint lineage.

## Overview

- All checkpoint metadata is stored in a single SQLite database at `/data/checkpoints.db`
- Checkpoints use auto-incrementing IDs (v0, v1, v2, etc.)
- Each checkpoint record tracks its path and parent checkpoint ID
- The active checkpoint is always the latest record in the database

## Database Schema

```sql
CREATE TABLE checkpoints (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    path TEXT NOT NULL,
    parent_id INTEGER,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (parent_id) REFERENCES checkpoints(id)
);
```

## Checkpoint Operation

When creating a checkpoint, the system performs these steps within a SQLite transaction:

1. Get the current latest checkpoint (e.g., ID=5, path="active/")
2. Clone `active/` to `checkpoints/v5` using JuiceFS clone
3. Update checkpoint 5's path to `checkpoints/v5`
4. Insert a new checkpoint record (ID=6) with path="active/" and parent_id=5
5. Commit the transaction

## Initial State

On first run, the system creates an initial v0 checkpoint:
- ID: 1
- Path: "active/"
- Parent ID: NULL

## Restore Operation

When restoring, you can specify the checkpoint using:
- Numeric ID: `"3"` - restores checkpoint with ID 3
- Version string: `"v3"` - restores from checkpoints/v3
- Full path: `"checkpoints/v3"` - restores from the specified path

The system will look up the checkpoint in the database to verify it exists before performing the restore.

## Example Checkpoint History

After several checkpoint operations, the database might look like:

| ID | Path | Parent ID | Created At |
|----|------|-----------|------------|
| 1 | checkpoints/v0 | NULL | 2024-01-01 10:00:00 |
| 2 | checkpoints/v1 | 1 | 2024-01-01 11:00:00 |
| 3 | checkpoints/v2 | 2 | 2024-01-01 12:00:00 |
| 4 | active/ | 3 | 2024-01-01 13:00:00 |

In this example:
- The current active state (ID=4) was derived from checkpoint v2
- Checkpoint v2 was derived from v1
- Checkpoint v1 was derived from v0
- Checkpoint v0 was the initial state

This allows tracking the full lineage of checkpoints and understanding how the current state evolved.