#!/bin/bash

# Example checkpoint script that demonstrates receiving checkpoint ID
echo "DB Component: Checkpoint requested"

# The checkpoint ID is passed via CHECKPOINT_ID environment variable
if [ -n "$CHECKPOINT_ID" ]; then
    echo "DB Component: Creating checkpoint with ID: $CHECKPOINT_ID"
    
    # Example: Create a checkpoint directory
    checkpoint_dir="/tmp/checkpoints/$CHECKPOINT_ID"
    mkdir -p "$checkpoint_dir"
    
    # Example: Save some state (in real usage, this would backup actual data)
    echo "Database state at $(date)" > "$checkpoint_dir/db_state.txt"
    echo "Checkpoint ID: $CHECKPOINT_ID" >> "$checkpoint_dir/db_state.txt"
    
    echo "DB Component: Checkpoint created successfully at $checkpoint_dir"
else
    echo "DB Component: No checkpoint ID provided, using default"
    # Fallback behavior when no ID is provided
fi

exit 0