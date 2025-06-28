# Sprites Python SDK

Python client library for interacting with Sprites environments. This SDK provides a programmatic interface to execute commands within Sprites using WebSocket connections.

## Installation

```bash
pip install sprites-sdk
```

## Quick Start

```python
from sprites import SpritesClient

# Initialize the client
client = SpritesClient(token="your-api-token")

# Attach to a sprite
sprite = client.attach("sprite-id")

# Execute a simple command
result = sprite.exec("echo 'Hello from Sprite!'").run()
print(result.stdout.decode())  # Output: Hello from Sprite!
print(result.returncode)  # Output: 0
```

## Configuration

The client can be configured in several ways:

### Using Environment Variables

```bash
export SPRITES_TOKEN="your-api-token"
export SPRITES_ENDPOINT="https://api.sprites.dev"  # Optional, this is the default
```

```python
from sprites import SpritesClient

# Will use environment variables
client = SpritesClient()
```

### Direct Configuration

```python
from sprites import SpritesClient

client = SpritesClient(
    endpoint="https://api.sprites.dev",
    token="your-api-token"
)
```

## New in v0.2.0

- Checkpoint and restore functionality
- Modular code structure
- Better error handling with custom exceptions
- Support for streaming checkpoint/restore progress

## Usage Examples

### Basic Command Execution

```python
# Execute a command and wait for completion
result = sprite.exec("ls -la /tmp").run()
print(result.stdout.decode())

# Execute with argument list (no shell)
result = sprite.exec(["ls", "-la", "/tmp"]).run()
print(result.stdout.decode())

# Provide input to a command
result = sprite.exec("cat").run(stdin="Hello, World!")
print(result.stdout.decode())  # Output: Hello, World!
```

### Non-Blocking Execution

```python
# Start a long-running process
exec = sprite.exec("ping google.com -c 10")
exec.start()

# Read output as it arrives
while exec.returncode is None:
    data = exec.read_stdout(timeout=1)
    if data:
        print(data.decode(), end='')

# Wait for completion
exec.wait()
```

### Interactive TTY Sessions

```python
# Start an interactive shell with TTY
exec = sprite.exec("/bin/bash", tty=True, initial_window_size=(80, 24))
exec.start()

# Send commands
exec.send_stdin(b"ls -la\n")
exec.send_stdin(b"echo 'Hello from TTY'\n")

# Read output (raw bytes in TTY mode)
output = exec.read_output(timeout=1)
print(output.decode())

# Resize terminal
exec.resize_terminal(120, 40)

# Clean up
exec.close()
```

### Working with Callbacks

```python
# Set up callbacks for streaming output
exec = sprite.exec("find / -name '*.log' 2>&1")

def on_stdout(data):
    print(f"STDOUT: {data.decode()}", end='')

def on_stderr(data):
    print(f"STDERR: {data.decode()}", end='')

def on_exit(code):
    print(f"\nProcess exited with code: {code}")

exec.on_stdout = on_stdout
exec.on_stderr = on_stderr
exec.on_exit = on_exit

# Start and wait
exec.start()
exec.wait()
```

### Environment Variables and Working Directory

```python
# Set environment variables
result = sprite.exec("env", env={"MY_VAR": "my_value", "ANOTHER": "123"}).run()
print(result.stdout.decode())

# Change working directory
result = sprite.exec("pwd", cwd="/tmp").run()
print(result.stdout.decode().strip())  # Output: /tmp
```

### Checkpoint and Restore

```python
# Create a checkpoint
checkpoint = sprite.checkpoint()
print(f"Created checkpoint: {checkpoint.id}")

# Create checkpoint with progress monitoring
def on_progress(msg):
    print(f"{msg.type}: {msg.message}")

checkpoint = sprite.checkpoint(on_message=on_progress)

# List checkpoints
checkpoints = sprite.list_checkpoints()
for cp in checkpoints:
    print(f"{cp.id}: {cp.create_time}")

# Restore from checkpoint
sprite.restore("checkpoint-id", on_message=on_progress)

# Get checkpoint details
cp = sprite.get_checkpoint("checkpoint-id")
print(f"History: {cp.history}")
```

### Error Handling

```python
# Check return codes
result = sprite.exec("false").run()
if result.returncode != 0:
    print(f"Command failed with code: {result.returncode}")

# Handle timeouts
try:
    result = sprite.exec("sleep 30").run(timeout=5)
except TimeoutError:
    print("Command timed out!")

# Access stderr
result = sprite.exec("ls /nonexistent").run()
print(f"Error: {result.stderr.decode()}")

# Handle checkpoint errors
from sprites import CheckpointError, RestoreError

try:
    sprite.checkpoint()
except CheckpointError as e:
    print(f"Checkpoint failed: {e}")

try:
    sprite.restore("invalid-id")
except RestoreError as e:
    print(f"Restore failed: {e}")
```

## API Reference

### SpritesClient

The main client for interacting with the Sprites API.

```python
client = SpritesClient(endpoint=None, token=None)
```

**Parameters:**
- `endpoint` (str, optional): API endpoint URL. Defaults to `https://api.sprites.dev` or `SPRITES_ENDPOINT` env var.
- `token` (str, optional): Authentication token. Falls back to `SPRITES_TOKEN` env var.

**Methods:**
- `attach(sprite_id: str) -> Sprite`: Attach to an existing Sprite by ID.

### Sprite

Represents an attached Sprite environment.

**Methods:**
- `exec(cmd, **kwargs) -> SpriteExec`: Create a command execution.
- `checkpoint(on_message=None) -> Checkpoint`: Create a checkpoint of current state.
- `restore(checkpoint_id, on_message=None)`: Restore to a checkpoint.
- `list_checkpoints(history_filter=None) -> List[Checkpoint]`: List available checkpoints.
- `get_checkpoint(checkpoint_id) -> Checkpoint`: Get checkpoint details.

### SpriteExec

Handles command execution within a Sprite.

**Attributes:**
- `args` (list): Command arguments being executed.
- `tty` (bool): Whether this is a TTY session.
- `returncode` (int): Exit code (None until process exits).
- `stdout` (bytes): Accumulated stdout (non-TTY mode).
- `stderr` (bytes): Accumulated stderr (non-TTY mode).
- `output` (bytes): Accumulated output (TTY mode).

**Methods:**
- `start()`: Start execution (non-blocking).
- `run(stdin=None, timeout=None)`: Run to completion (blocking).
- `wait(timeout=None) -> bool`: Wait for completion.
- `send_stdin(data)`: Send input data.
- `send_stdin_eof()`: Send EOF (non-TTY mode only).
- `resize_terminal(cols, rows)`: Resize terminal (TTY mode only).
- `send_control_message(message)`: Send custom control message.
- `read_stdout(timeout=None) -> bytes`: Read stdout data.
- `read_stderr(timeout=None) -> bytes`: Read stderr data.
- `read_output(timeout=None) -> bytes`: Read output (TTY mode).
- `close()`: Close connection.

**Callbacks:**
- `on_stdout`: Called with stdout data (non-TTY mode).
- `on_stderr`: Called with stderr data (non-TTY mode).
- `on_output`: Called with output data (TTY mode).
- `on_exit`: Called with exit code when process exits.

### exec() Parameters

The `sprite.exec()` method accepts:

- `cmd` (str or list): Command to execute.
- `cwd` (str, optional): Working directory.
- `env` (dict, optional): Environment variables.
- `tty` (bool): Enable TTY mode. Default: False.
- `initial_window_size` (tuple, optional): Initial terminal size as (cols, rows).

### Checkpoint

Represents a checkpoint with attributes:
- `id` (str): Unique checkpoint identifier.
- `create_time` (datetime): When the checkpoint was created.
- `source_id` (str): ID of source checkpoint if this is a restore.
- `history` (list): List of checkpoint IDs in the history chain.

### StreamMessage

Progress message from checkpoint/restore operations:
- `type` (str): Message type (info, error, progress, complete).
- `message` (str): Human-readable message.
- `time` (datetime): When the message was generated.
- `error` (str): Error details if type is "error".
- `data` (dict): Additional data specific to the message type.

### Exceptions

The SDK provides specific exception types:
- `SpritesError`: Base exception for all SDK errors.
- `AuthenticationError`: Authentication failures.
- `ConnectionError`: Connection failures.
- `CheckpointError`: Checkpoint operation failures.
- `RestoreError`: Restore operation failures.
- `ExecutionError`: Command execution failures.

## TTY vs Non-TTY Mode

**Non-TTY Mode (default):**
- Separate stdout and stderr streams
- Line-buffered output
- Can send EOF signal
- Suitable for non-interactive commands

**TTY Mode:**
- Single output stream (raw PTY data)
- Character-by-character I/O
- No EOF signal (use Ctrl+D in input)
- Required for interactive programs (editors, shells)
- Supports terminal resize
- Output includes ANSI escape sequences (colors, cursor movement, etc.)
- Input is processed by the PTY (e.g., Ctrl+C generates SIGINT)

## WebSocket Protocol

The SDK handles the WebSocket protocol transparently:
- Binary frames for data transfer
- Text frames for control messages (JSON)
- Automatic ping/pong for keepalive
- Stream multiplexing in non-TTY mode

## Requirements

- Python 3.7+
- `websocket-client` library

## Testing

The SDK includes comprehensive unit and integration tests. To run tests:

```bash
# Install test dependencies
pip install -e ".[test]"

# Run all tests (requires server binary)
make test

# Run unit tests only  
make test-unit

# Run tests in Docker
make test-docker
```

See the [tests README](tests/README.md) for more details.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

MIT License - See LICENSE file for details.