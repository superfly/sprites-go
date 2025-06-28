#!/usr/bin/env python3
"""
Advanced usage example for the Sprites Python SDK

This example demonstrates:
- Streaming large output efficiently
- Building a simple terminal interface
- Handling binary data
- Error recovery and reconnection
"""

import os
import sys
import threading
import time
from sprites import SpritesClient

def streaming_example(sprite):
    """Example of efficiently streaming large output."""
    print("\n--- Streaming Large Output Example ---")
    
    # Command that produces a lot of output
    exec_cmd = sprite.exec("find /usr -name '*.so' 2>/dev/null | head -100")
    
    # Track statistics
    lines_received = 0
    bytes_received = 0
    start_time = time.time()
    
    def on_stdout(data):
        nonlocal lines_received, bytes_received
        bytes_received += len(data)
        lines_received += data.count(b'\n')
        # Process each line as it arrives
        for line in data.decode('utf-8', errors='replace').splitlines():
            if line:  # Skip empty lines
                print(f"  Found: {line}")
    
    exec_cmd.on_stdout = on_stdout
    exec_cmd.start()
    exec_cmd.wait()
    
    elapsed = time.time() - start_time
    print(f"\nStreaming complete:")
    print(f"  Lines: {lines_received}")
    print(f"  Bytes: {bytes_received}")
    print(f"  Time: {elapsed:.2f}s")
    print(f"  Throughput: {bytes_received/elapsed:.0f} bytes/sec")


def binary_data_example(sprite):
    """Example of handling binary data."""
    print("\n--- Binary Data Example ---")
    
    # Create a binary file
    print("Creating binary test data...")
    create_cmd = sprite.exec(
        "dd if=/dev/urandom of=/tmp/test.bin bs=1024 count=1 2>/dev/null"
    ).run()
    
    # Read it back as binary
    print("Reading binary data...")
    read_cmd = sprite.exec("cat /tmp/test.bin").run()
    
    binary_data = read_cmd.stdout
    print(f"Read {len(binary_data)} bytes of binary data")
    print(f"First 16 bytes (hex): {binary_data[:16].hex()}")
    
    # Clean up
    sprite.exec("rm /tmp/test.bin").run()


def terminal_interface_example(sprite):
    """Example of building a simple terminal interface."""
    print("\n--- Terminal Interface Example ---")
    print("Building a simple terminal interface wrapper...")
    
    class SimpleTerminal:
        def __init__(self, sprite):
            self.sprite = sprite
            self.exec_cmd = None
            self.output_buffer = []
            self.lock = threading.Lock()
        
        def start(self):
            """Start the terminal session."""
            self.exec_cmd = self.sprite.exec(
                "/bin/bash", 
                tty=True, 
                initial_window_size=(80, 24)
            )
            self.exec_cmd.on_output = self._on_output
            self.exec_cmd.on_exit = self._on_exit
            self.exec_cmd.start()
            
            # Wait for prompt
            time.sleep(0.5)
        
        def _on_output(self, data):
            """Handle output from the terminal."""
            with self.lock:
                self.output_buffer.append(data)
        
        def _on_exit(self, code):
            """Handle terminal exit."""
            print(f"\n[Terminal exited with code {code}]")
        
        def send_command(self, command):
            """Send a command to the terminal."""
            if not command.endswith('\n'):
                command += '\n'
            self.exec_cmd.send_stdin(command.encode())
        
        def get_output(self, timeout=1.0):
            """Get accumulated output."""
            time.sleep(timeout)  # Wait for output
            
            with self.lock:
                if not self.output_buffer:
                    return ""
                
                output = b''.join(self.output_buffer)
                self.output_buffer = []
                return output.decode('utf-8', errors='replace')
        
        def resize(self, cols, rows):
            """Resize the terminal."""
            self.exec_cmd.resize_terminal(cols, rows)
        
        def close(self):
            """Close the terminal."""
            if self.exec_cmd:
                self.exec_cmd.send_stdin(b"exit\n")
                self.exec_cmd.wait(timeout=2)
                self.exec_cmd.close()
    
    # Use the terminal interface
    term = SimpleTerminal(sprite)
    term.start()
    
    print("Terminal started. Sending commands...\n")
    
    # Send commands and get output
    term.send_command("echo 'Terminal interface test'")
    print("Response:", term.get_output())
    
    term.send_command("pwd")
    print("Response:", term.get_output())
    
    # Resize terminal
    print("\nResizing terminal to 100x30...")
    term.resize(100, 30)
    term.send_command("echo $COLUMNS $LINES")
    print("Response:", term.get_output())
    
    # Close terminal
    term.close()
    print("Terminal closed.")


def parallel_execution_example(sprite):
    """Example of running multiple commands in parallel."""
    print("\n--- Parallel Execution Example ---")
    
    commands = [
        ("sleep 1 && echo 'Task 1 complete'", "Task 1"),
        ("sleep 2 && echo 'Task 2 complete'", "Task 2"),
        ("sleep 1.5 && echo 'Task 3 complete'", "Task 3"),
    ]
    
    exec_cmds = []
    
    # Start all commands
    print("Starting commands in parallel...")
    start_time = time.time()
    
    for cmd, name in commands:
        exec_cmd = sprite.exec(cmd)
        exec_cmd.name = name  # Add custom attribute
        exec_cmd.start()
        exec_cmds.append(exec_cmd)
    
    # Wait for all to complete
    print("Waiting for completion...")
    for exec_cmd in exec_cmds:
        exec_cmd.wait()
        output = exec_cmd.stdout.decode().strip()
        print(f"  {exec_cmd.name}: {output}")
    
    elapsed = time.time() - start_time
    print(f"All tasks completed in {elapsed:.1f}s (parallel execution)")


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
    
    # Run examples
    try:
        streaming_example(sprite)
        binary_data_example(sprite)
        terminal_interface_example(sprite)
        parallel_execution_example(sprite)
    except Exception as e:
        print(f"Error in example: {e}")
        import traceback
        traceback.print_exc()
    
    print("\n--- All advanced examples completed! ---")

if __name__ == "__main__":
    main()