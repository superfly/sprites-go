#!/usr/bin/env python3
"""
Interactive TTY example for the Sprites Python SDK

This example demonstrates running interactive commands with TTY support.
Since this is an SDK, we programmatically interact with the TTY session.
"""

import os
import sys
import time
from sprites import SpritesClient

def main():
    # Get configuration
    sprite_id = os.environ.get('SPRITE_ID')
    if not sprite_id:
        print("Please set SPRITE_ID environment variable")
        sys.exit(1)
    
    # Initialize client
    try:
        client = SpritesClient()
    except ValueError as e:
        print(f"Error: {e}")
        print("Please set SPRITES_TOKEN environment variable")
        sys.exit(1)
    
    # Attach to sprite
    sprite = client.attach(sprite_id)
    print(f"Attached to sprite: {sprite_id}")
    
    print("\n--- Interactive TTY Example ---")
    print("Starting an interactive bash shell in TTY mode.")
    print("We'll send commands programmatically and read the output.\n")
    
    # Start bash in TTY mode with specific terminal size
    exec_cmd = sprite.exec("/bin/bash", tty=True, initial_window_size=(80, 24))
    exec_cmd.start()
    
    # Give bash time to start
    time.sleep(0.5)
    
    # Function to send command and read response
    def send_and_read(command, wait_time=1.0):
        print(f"Sending: {command.strip()}")
        exec_cmd.send_stdin(command.encode())
        time.sleep(wait_time)
        
        # Read all available output
        output = b''
        while True:
            data = exec_cmd.read_output(timeout=0.1)
            if not data:
                break
            output += data
        
        if output:
            print(f"Output:\n{output.decode('utf-8', errors='replace')}")
        print("-" * 40)
    
    # Send some commands
    send_and_read("echo 'Hello from TTY mode!'\n")
    send_and_read("pwd\n")
    send_and_read("ls -la | head -5\n")
    
    # Demonstrate terminal resize
    print("Resizing terminal to 120x40...")
    exec_cmd.resize_terminal(120, 40)
    send_and_read("echo $COLUMNS $LINES\n")
    
    # Create and edit a file using echo (simpler than using an editor)
    send_and_read("echo 'This is a test file' > test.txt\n")
    send_and_read("cat test.txt\n")
    send_and_read("rm test.txt\n")
    
    # Exit the shell
    print("Exiting shell...")
    exec_cmd.send_stdin(b"exit\n")
    
    # Wait for process to exit
    if exec_cmd.wait(timeout=2):
        print(f"Shell exited with code: {exec_cmd.returncode}")
    else:
        print("Shell didn't exit in time, closing connection")
        exec_cmd.close()
    
    print("\n--- TTY Example with Callbacks ---")
    print("Starting another shell with output callback...")
    
    # Start another shell with a callback
    exec_cmd2 = sprite.exec("/bin/bash", tty=True)
    
    # Set up callback to print output as it arrives
    def on_output(data):
        print(f"[OUTPUT] {data.decode('utf-8', errors='replace')}", end='')
    
    exec_cmd2.on_output = on_output
    exec_cmd2.on_exit = lambda code: print(f"\n[EXIT] Process exited with code: {code}")
    
    exec_cmd2.start()
    time.sleep(0.5)
    
    # Send a few commands
    exec_cmd2.send_stdin(b"echo 'Callback example'\n")
    time.sleep(0.5)
    exec_cmd2.send_stdin(b"date\n")
    time.sleep(0.5)
    exec_cmd2.send_stdin(b"exit\n")
    
    # Wait for exit
    exec_cmd2.wait(timeout=2)
    
    print("\n--- All TTY examples completed! ---")

if __name__ == "__main__":
    main()