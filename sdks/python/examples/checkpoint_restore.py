#!/usr/bin/env python3
"""
Checkpoint and restore example for the Sprites Python SDK

This example demonstrates:
- Creating checkpoints
- Listing checkpoints
- Restoring from checkpoints
- Monitoring checkpoint/restore progress
"""

import os
import sys
import time
from sprites import SpritesClient, StreamMessage

def print_progress(msg: StreamMessage):
    """Print checkpoint/restore progress messages."""
    if msg.type == "info":
        print(f"[INFO] {msg.message}")
    elif msg.type == "progress":
        print(f"[PROGRESS] {msg.message}")
    elif msg.type == "error":
        print(f"[ERROR] {msg.error or msg.message}")
    elif msg.type == "complete":
        print(f"[COMPLETE] {msg.message}")
        if msg.data:
            print(f"  Data: {msg.data}")

def main():
    # Get configuration
    sprite_id = os.environ.get('SPRITE_ID')
    if not sprite_id:
        print("Please set SPRITE_ID environment variable")
        sys.exit(1)
    
    # Initialize client
    try:
        client = SpritesClient()
    except Exception as e:
        print(f"Error: {e}")
        print("Please set SPRITES_TOKEN environment variable")
        sys.exit(1)
    
    # Attach to sprite
    sprite = client.attach(sprite_id)
    print(f"Attached to sprite: {sprite_id}")
    
    # Example 1: Create a file and checkpoint
    print("\n--- Example 1: Create File and Checkpoint ---")
    
    # Create a test file
    result = sprite.exec("echo 'This is version 1' > /tmp/test.txt").run()
    if result.returncode != 0:
        print("Failed to create test file")
        sys.exit(1)
    
    # Verify file content
    result = sprite.exec("cat /tmp/test.txt").run()
    print(f"File content: {result.stdout.decode().strip()}")
    
    # Create checkpoint
    print("\nCreating checkpoint...")
    checkpoint1 = sprite.checkpoint(on_message=print_progress)
    print(f"\nCheckpoint created: {checkpoint1.id}")
    print(f"Created at: {checkpoint1.create_time}")
    
    # Example 2: Modify file and create another checkpoint
    print("\n--- Example 2: Modify File and Create Another Checkpoint ---")
    
    # Modify the file
    result = sprite.exec("echo 'This is version 2' > /tmp/test.txt").run()
    result = sprite.exec("cat /tmp/test.txt").run()
    print(f"Modified file content: {result.stdout.decode().strip()}")
    
    # Create second checkpoint
    print("\nCreating second checkpoint...")
    checkpoint2 = sprite.checkpoint(on_message=print_progress)
    print(f"\nCheckpoint created: {checkpoint2.id}")
    
    # Example 3: List checkpoints
    print("\n--- Example 3: List Checkpoints ---")
    checkpoints = sprite.list_checkpoints()
    print(f"Found {len(checkpoints)} checkpoints:")
    for cp in checkpoints:
        print(f"  - {cp.id}: {cp.create_time}")
        if cp.source_id:
            print(f"    Source: {cp.source_id}")
    
    # Example 4: Restore from first checkpoint
    print("\n--- Example 4: Restore from First Checkpoint ---")
    print(f"Restoring to checkpoint: {checkpoint1.id}")
    sprite.restore(checkpoint1.id, on_message=print_progress)
    
    # Verify file is back to version 1
    print("\nVerifying restored content...")
    result = sprite.exec("cat /tmp/test.txt").run()
    print(f"Restored file content: {result.stdout.decode().strip()}")
    
    # Example 5: Get checkpoint details
    print("\n--- Example 5: Checkpoint Details ---")
    cp_details = sprite.get_checkpoint(checkpoint2.id)
    print(f"Checkpoint {cp_details.id}:")
    print(f"  Created: {cp_details.create_time}")
    print(f"  Source: {cp_details.source_id}")
    print(f"  History: {cp_details.history}")
    
    # Example 6: Find related checkpoints
    print("\n--- Example 6: Find Related Checkpoints ---")
    if checkpoint1.history:
        # Find checkpoints that share history with checkpoint1
        base_id = checkpoint1.history[0] if checkpoint1.history else checkpoint1.id
        related = sprite.list_checkpoints(history_filter=base_id)
        print(f"Checkpoints related to {base_id}:")
        for cp in related:
            print(f"  - {cp.id}")
    
    # Example 7: Error handling
    print("\n--- Example 7: Error Handling ---")
    try:
        sprite.restore("non-existent-checkpoint")
    except Exception as e:
        print(f"Expected error: {e}")
    
    # Create final checkpoint showing complete state
    print("\n--- Creating Final Checkpoint ---")
    
    # Add some more files
    sprite.exec("echo 'Final state' > /tmp/final.txt").run()
    sprite.exec("date > /tmp/timestamp.txt").run()
    
    final_checkpoint = sprite.checkpoint()
    print(f"Final checkpoint: {final_checkpoint.id}")
    
    # Show all files
    print("\nFinal state of /tmp:")
    result = sprite.exec("ls -la /tmp/*.txt 2>/dev/null || echo 'No .txt files'").run()
    print(result.stdout.decode())
    
    print("\n--- All checkpoint examples completed! ---")

if __name__ == "__main__":
    main()