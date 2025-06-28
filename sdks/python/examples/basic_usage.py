#!/usr/bin/env python3
"""
Basic usage example for the Sprites Python SDK

This example demonstrates:
- Connecting to a Sprite
- Running simple commands
- Working with input/output
- Using environment variables
- Error handling
"""

import os
import sys
from sprites import SpritesClient

def main():
    # Get configuration from environment or use defaults
    sprite_id = os.environ.get('SPRITE_ID')
    if not sprite_id:
        print("Please set SPRITE_ID environment variable")
        sys.exit(1)
    
    # Initialize client (will use SPRITES_TOKEN from environment)
    try:
        client = SpritesClient()
    except ValueError as e:
        print(f"Error initializing client: {e}")
        print("Please set SPRITES_TOKEN environment variable")
        sys.exit(1)
    
    # Attach to the sprite
    sprite = client.attach(sprite_id)
    print(f"Attached to sprite: {sprite_id}")
    
    # Example 1: Simple command
    print("\n--- Example 1: Simple Command ---")
    result = sprite.exec("echo 'Hello from Sprite!'").run()
    print(f"Output: {result.stdout.decode()}")
    print(f"Return code: {result.returncode}")
    
    # Example 2: List files
    print("\n--- Example 2: List Files ---")
    result = sprite.exec(["ls", "-la", "/tmp"]).run()
    print(f"Files in /tmp:\n{result.stdout.decode()}")
    
    # Example 3: Working with stdin
    print("\n--- Example 3: Working with stdin ---")
    result = sprite.exec("cat").run(stdin="This is input from Python!")
    print(f"Cat output: {result.stdout.decode()}")
    
    # Example 4: Environment variables
    print("\n--- Example 4: Environment Variables ---")
    result = sprite.exec("echo $MY_VAR", env={"MY_VAR": "Hello from env!"}).run()
    print(f"Env var output: {result.stdout.decode()}")
    
    # Example 5: Working directory
    print("\n--- Example 5: Working Directory ---")
    result = sprite.exec("pwd", cwd="/etc").run()
    print(f"Working directory: {result.stdout.decode().strip()}")
    
    # Example 6: Error handling
    print("\n--- Example 6: Error Handling ---")
    result = sprite.exec("ls /nonexistent/directory").run()
    if result.returncode != 0:
        print(f"Command failed with code {result.returncode}")
        print(f"Error: {result.stderr.decode()}")
    
    # Example 7: Complex shell command
    print("\n--- Example 7: Complex Shell Command ---")
    cmd = """
    for i in {1..5}; do
        echo "Line $i"
    done | grep -E "Line [2-4]" | wc -l
    """
    result = sprite.exec(cmd).run()
    print(f"Number of matching lines: {result.stdout.decode().strip()}")
    
    # Example 8: Timeout handling
    print("\n--- Example 8: Timeout Handling ---")
    try:
        result = sprite.exec("sleep 2").run(timeout=1)
    except TimeoutError:
        print("Command timed out as expected!")
    
    # Example 9: Non-blocking execution
    print("\n--- Example 9: Non-blocking Execution ---")
    exec_cmd = sprite.exec("for i in {1..3}; do echo $i; sleep 1; done")
    exec_cmd.start()
    
    print("Reading output as it arrives:")
    while exec_cmd.returncode is None:
        data = exec_cmd.read_stdout(timeout=0.5)
        if data:
            print(f"  Got: {data.decode().strip()}")
    
    print(f"Final return code: {exec_cmd.returncode}")
    
    # Example 10: Getting system information
    print("\n--- Example 10: System Information ---")
    result = sprite.exec("uname -a").run()
    print(f"System: {result.stdout.decode().strip()}")
    
    result = sprite.exec("python3 --version 2>&1").run()
    print(f"Python version: {result.stdout.decode().strip()}")
    
    print("\n--- All examples completed! ---")

if __name__ == "__main__":
    main()