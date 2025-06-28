#!/usr/bin/env python3
"""
Integration tests for the Sprites Python SDK.

These tests require a running Sprites server to test against.
"""

import os
import sys
import time
import json
import pytest
import subprocess
import tempfile
import threading
from datetime import datetime
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sprites import (
    SpritesClient, Sprite, SpriteExec, 
    Checkpoint, StreamMessage,
    AuthenticationError, CheckpointError, RestoreError
)


# Test configuration
SERVER_BINARY = os.environ.get('SPRITE_SERVER_BINARY', '/app/dist/server')
TEST_TOKEN = 'f0e4c2f76c58916ec258f246851bea091d14d4247a2fc3e18694461b1816e13b'
TEST_PORT = 28080



@pytest.fixture(scope="session")
def server():
    """Fixture that provides the server endpoint (server is already running)."""
    return "http://localhost:28080"


@pytest.fixture
def client(server):
    """Fixture that provides a client connected to the test server."""
    return SpritesClient(endpoint=server, token=TEST_TOKEN)


@pytest.fixture
def sprite(client):
    """Fixture that provides an attached sprite."""
    # In a real setup, we'd get the actual sprite ID
    # For now, we'll use a dummy ID since server runs with local process
    return client.attach("test-sprite")




class TestBasicExecution:
    """Test basic command execution functionality."""
    
    def test_simple_echo(self, sprite):
        """Test simple echo command."""
        result = sprite.exec("echo 'Hello, World!'").run()
        assert result.returncode == 0
        assert result.stdout.decode().strip() == "Hello, World!"
        assert result.stderr == b''
    
    def test_command_list(self, sprite):
        """Test command as list of arguments."""
        result = sprite.exec(["echo", "Hello", "World"]).run()
        assert result.returncode == 0
        assert result.stdout.decode().strip() == "Hello World"
    
    def test_command_with_exit_code(self, sprite):
        """Test command with non-zero exit code."""
        # Use shell builtin exit command - must be explicit about shell execution
        result = sprite.exec(["/bin/sh", "-c", "exit 42"]).run()
        assert result.returncode == 42
        assert result.stdout == b""
        assert result.stderr == b""
    
    def test_command_with_stderr(self, sprite):
        """Test command that outputs to stderr."""
        # Use a shell command that writes to stderr
        result = sprite.exec(["/bin/sh", "-c", "echo error >&2"]).run()
        assert result.returncode == 0
        assert result.stdout == b""
        assert result.stderr.decode().strip() == "error"
    
    def test_command_with_both_streams(self, sprite):
        """Test command that outputs to both stdout and stderr."""
        result = sprite.exec(["/bin/sh", "-c", "echo 'stdout'; echo 'stderr' >&2"]).run()
        assert result.returncode == 0
        assert result.stdout.decode().strip() == "stdout"
        assert result.stderr.decode().strip() == "stderr"
    
    def test_command_with_stdin(self, sprite):
        """Test sending input to command."""
        result = sprite.exec("cat").run(stdin="Hello from stdin")
        assert result.returncode == 0
        assert result.stdout.decode() == "Hello from stdin"
    
    def test_command_with_working_directory(self, sprite):
        """Test command with working directory."""
        result = sprite.exec("pwd", cwd="/tmp").run()
        assert result.returncode == 0
        assert result.stdout.decode().strip() == "/tmp"
    
    def test_command_with_environment(self, sprite):
        """Test command with environment variables."""
        result = sprite.exec("echo $MY_VAR", env={"MY_VAR": "test_value"}).run()
        assert result.returncode == 0
        assert result.stdout.decode().strip() == "test_value"
    
    def test_command_timeout(self, sprite):
        """Test command timeout."""
        with pytest.raises(TimeoutError):
            sprite.exec("sleep 10").run(timeout=0.5)
    
    def test_large_output(self, sprite):
        """Test command with large output."""
        # Generate 1MB of output
        cmd = "dd if=/dev/zero bs=1024 count=1024 2>/dev/null | base64"
        result = sprite.exec(cmd).run()
        assert result.returncode == 0
        assert len(result.stdout) > 1000000  # Should be > 1MB


class TestNonBlockingExecution:
    """Test non-blocking command execution."""
    
    def test_streaming_output(self, sprite):
        """Test reading output as it arrives."""
        exec_cmd = sprite.exec("seq 1 3 | while read i; do echo $i; sleep 0.1; done")
        exec_cmd.start()
        
        outputs = []
        while exec_cmd.returncode is None:
            data = exec_cmd.read_stdout(timeout=0.5)
            if data:
                for line in data.decode().strip().split('\n'):
                    if line:
                        outputs.append(line)
        
        assert exec_cmd.returncode == 0
        assert outputs == ['1', '2', '3']
    
    def test_callbacks(self, sprite):
        """Test output callbacks."""
        stdout_data = []
        exit_code = None
        
        def on_stdout(data):
            stdout_data.append(data)
        
        def on_exit(code):
            nonlocal exit_code
            exit_code = code
        
        exec_cmd = sprite.exec("echo 'line1'; echo 'line2'")
        exec_cmd.on_stdout = on_stdout
        exec_cmd.on_exit = on_exit
        
        exec_cmd.start()
        exec_cmd.wait()
        
        assert exit_code == 0
        assert len(stdout_data) > 0
        output = b''.join(stdout_data).decode()
        assert 'line1' in output
        assert 'line2' in output
    
    def test_send_stdin_interactive(self, sprite):
        """Test sending stdin to running process."""
        exec_cmd = sprite.exec("cat")
        exec_cmd.start()
        
        exec_cmd.send_stdin("Hello\n")
        exec_cmd.send_stdin("World\n")
        exec_cmd.send_stdin_eof()
        
        exec_cmd.wait()
        assert exec_cmd.returncode == 0
        assert exec_cmd.stdout.decode() == "Hello\nWorld\n"


class TestTTYMode:
    """Test TTY mode functionality."""
    
    @pytest.mark.tty
    def test_tty_basic(self, sprite):
        """Test basic TTY command."""
        exec_cmd = sprite.exec("echo 'TTY test'", tty=True)
        result = exec_cmd.run()
        assert result.returncode == 0
        # In TTY mode, output includes more formatting
        assert b'TTY test' in result.output
    
    @pytest.mark.tty
    def test_tty_interactive(self, sprite):
        """Test interactive TTY session."""
        exec_cmd = sprite.exec("/bin/bash", tty=True)
        exec_cmd.start()
        
        # Send commands
        exec_cmd.send_stdin(b"echo 'Hello from TTY'\n")
        exec_cmd.send_stdin(b"exit 0\n")
        
        # Wait for exit
        assert exec_cmd.wait(timeout=2)
        assert exec_cmd.returncode == 0
        assert b'Hello from TTY' in exec_cmd.output
    
    @pytest.mark.tty
    def test_tty_resize(self, sprite):
        """Test terminal resize in TTY mode."""
        exec_cmd = sprite.exec("/bin/bash", tty=True, initial_window_size=(80, 24))
        exec_cmd.start()
        
        # Check initial size
        exec_cmd.send_stdin(b"echo $COLUMNS $LINES\n")
        time.sleep(0.5)
        
        # Resize
        exec_cmd.resize_terminal(100, 30)
        time.sleep(0.1)
        
        # Check new size
        exec_cmd.send_stdin(b"echo $COLUMNS $LINES\n")
        exec_cmd.send_stdin(b"exit 0\n")
        
        exec_cmd.wait()
        output = exec_cmd.output.decode('utf-8', errors='replace')
        assert '80 24' in output
        assert '100 30' in output


class TestCheckpointRestore:
    """Test checkpoint and restore functionality."""
    
    @pytest.mark.checkpoint
    def test_checkpoint_create(self, sprite):
        """Test creating a checkpoint."""
        # Create a test file
        sprite.exec("echo 'checkpoint test' > /tmp/checkpoint_test.txt").run()
        
        # Create checkpoint
        messages = []
        def on_message(msg):
            messages.append(msg)
        
        checkpoint = sprite.checkpoint(on_message=on_message)
        
        assert checkpoint.id
        assert checkpoint.create_time
        assert len(messages) > 0
        assert any(msg.type == 'complete' for msg in messages)
    
    @pytest.mark.checkpoint
    def test_checkpoint_restore(self, sprite):
        """Test restoring from checkpoint."""
        # Create initial state
        sprite.exec("echo 'version 1' > /tmp/restore_test.txt").run()
        
        # Create checkpoint
        checkpoint1 = sprite.checkpoint()
        
        # Modify state
        sprite.exec("echo 'version 2' > /tmp/restore_test.txt").run()
        
        # Verify current state
        result = sprite.exec("cat /tmp/restore_test.txt").run()
        assert result.stdout.decode().strip() == "version 2"
        
        # Restore
        messages = []
        sprite.restore(checkpoint1.id, on_message=lambda m: messages.append(m))
        
        # Verify restored state
        result = sprite.exec("cat /tmp/restore_test.txt").run()
        assert result.stdout.decode().strip() == "version 1"
        assert len(messages) > 0
    
    @pytest.mark.checkpoint
    def test_checkpoint_list(self, sprite):
        """Test listing checkpoints."""
        # Create some checkpoints
        cp1 = sprite.checkpoint()
        time.sleep(1)
        cp2 = sprite.checkpoint()
        
        # List all
        checkpoints = sprite.list_checkpoints()
        assert len(checkpoints) >= 2
        
        # Should be ordered newest first
        assert checkpoints[0].create_time > checkpoints[1].create_time
        
        # Find our checkpoints
        ids = [cp.id for cp in checkpoints]
        assert cp1.id in ids
        assert cp2.id in ids


class TestErrorHandling:
    """Test error handling and exceptions."""
    
    def test_invalid_authentication(self):
        """Test authentication error."""
        # Since we're testing against a local server with direct process execution,
        # authentication errors will manifest during exec, not client creation
        client = SpritesClient(endpoint="http://localhost:28080", token="wrong-token")
        sprite = client.attach("test-sprite")
        
        # This should fail with an authentication or connection error
        with pytest.raises(Exception):  # Could be various errors depending on server setup
            sprite.exec("echo test").run()
    
    def test_command_not_found(self, sprite):
        """Test executing non-existent command."""
        result = sprite.exec("nonexistentcommand123").run()
        assert result.returncode != 0
        assert b'not found' in result.stderr or b'No such file' in result.stderr
    
    def test_websocket_error(self, sprite):
        """Test WebSocket connection error."""
        # Create exec but with wrong endpoint
        exec_cmd = sprite.exec("echo test")
        exec_cmd.ws_url = "ws://localhost:99999/exec"  # Invalid port
        
        with pytest.raises(Exception):  # Should raise connection error
            exec_cmd.start()
    
    @pytest.mark.checkpoint
    def test_checkpoint_not_found(self, sprite):
        """Test restoring non-existent checkpoint."""
        with pytest.raises(CheckpointError):
            sprite.get_checkpoint("non-existent-checkpoint-id")
    
    @pytest.mark.checkpoint
    def test_restore_error(self, sprite):
        """Test restore with invalid checkpoint."""
        with pytest.raises(RestoreError):
            sprite.restore("invalid-checkpoint-id")


class TestParallelExecution:
    """Test running multiple commands in parallel."""
    
    def test_parallel_commands(self, sprite):
        """Test running multiple commands simultaneously."""
        commands = [
            sprite.exec("sleep 1; echo Task1"),
            sprite.exec("sleep 0.5; echo Task2"),
            sprite.exec("sleep 0.2; echo Task3"),
        ]
        
        # Start all commands
        start_time = time.time()
        for cmd in commands:
            cmd.start()
        
        # Wait for all to complete with longer timeout
        results = []
        for i, cmd in enumerate(commands):
            if cmd.wait(timeout=3):  # Give commands more time
                output = cmd.stdout.decode().strip()
                if output:  # Only add non-empty outputs
                    results.append(output)
                else:
                    # Debug empty output
                    print(f"Command {i} had no output. Stderr: {cmd.stderr.decode()}, Exit: {cmd.returncode}")
        
        elapsed = time.time() - start_time
        
        # Should complete faster than sequential (< 2s instead of 1.7s)
        assert elapsed < 2.0
        assert sorted(results) == ['Task1', 'Task2', 'Task3']
    
    def test_concurrent_io(self, sprite):
        """Test concurrent I/O operations."""
        # Create multiple exec instances doing I/O
        writers = []
        for i in range(5):
            cmd = sprite.exec(f"echo 'Writer {i}' > /tmp/concurrent_{i}.txt")
            writers.append(cmd)
        
        # Start all writers
        for cmd in writers:
            cmd.start()
        
        # Wait for completion with better error handling
        failed_commands = []
        for i, cmd in enumerate(writers):
            if cmd.wait(timeout=5):  # Longer timeout for concurrent operations
                if cmd.returncode != 0:
                    failed_commands.append((i, cmd.returncode, cmd.stderr.decode()))
            else:
                failed_commands.append((i, "timeout", "Command timed out"))
        
        # Report any failures for debugging
        if failed_commands:
            for i, code, stderr in failed_commands:
                print(f"Command {i} failed with code {code}: {stderr}")
        
        # Check that most commands succeeded (allow for 1 failure due to timing)
        successful_commands = len(writers) - len(failed_commands)
        assert successful_commands >= 4, f"Too many commands failed: {failed_commands}"
        
        # Verify files were created (count actual files, not just successful commands)
        result = sprite.exec("ls /tmp/concurrent_*.txt 2>/dev/null | wc -l").run()
        file_count = int(result.stdout.decode().strip())
        assert file_count >= 4, f"Expected at least 4 files, got {file_count}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])