# Supervisor Package

A simple, robust process supervisor for Go that provides graceful shutdown, signal forwarding, and process group management.

## Features

- **Simple API**: Start, stop, and manage processes with just a few method calls
- **Graceful Shutdown**: Sends SIGTERM first, then SIGKILL after a configurable grace period
- **Signal Forwarding**: Forward any signal to the supervised process
- **Process Group Management**: Automatically manages process groups to ensure child processes are cleaned up
- **Channel-based Communication**: No locks, all internal communication via channels
- **Comprehensive Error Handling**: Clear error messages for all edge cases

## Installation

```bash
go get github.com/sprite-env/server/packages/supervisor
```

## Usage

### Basic Example

```go
package main

import (
    "log"
    "time"
    "github.com/sprite-env/server/packages/supervisor"
)

func main() {
    // Create a supervisor
    s, err := supervisor.New(supervisor.Config{
        Command:     "myapp",
        Args:        []string{"--flag", "value"},
        GracePeriod: 10 * time.Second,
    })
    if err != nil {
        log.Fatal(err)
    }

    // Start the process
    if err := s.Start(); err != nil {
        log.Fatal(err)
    }

    // Get the process ID
    pid, _ := s.Pid()
    log.Printf("Started process with PID: %d", pid)

    // Do some work...
    time.Sleep(5 * time.Second)

    // Stop the process gracefully
    if err := s.Stop(); err != nil {
        log.Fatal(err)
    }
}
```

### Signal Forwarding

```go
// Forward a signal to the supervised process
if err := s.Signal(syscall.SIGUSR1); err != nil {
    log.Printf("Failed to send signal: %v", err)
}
```

### Waiting for Process Exit

```go
// Start a process that will exit on its own
s, _ := supervisor.New(supervisor.Config{
    Command: "sleep",
    Args:    []string{"5"},
})

s.Start()

// Wait for the process to exit
if err := s.Wait(); err != nil {
    log.Printf("Process exited with error: %v", err)
}
```

## Configuration Options

- `Command`: The command to execute (required)
- `Args`: Command line arguments
- `GracePeriod`: Time to wait for graceful shutdown before force killing (default: 10s)
- `Env`: Environment variables (if not set, inherits from parent)
- `Dir`: Working directory (if not set, uses current directory)

## Behavior

### Graceful Shutdown

When `Stop()` is called:
1. Sends SIGTERM to the process group
2. Waits for the process to exit gracefully
3. If the process doesn't exit within the grace period, sends SIGKILL
4. Ensures all child processes in the process group are also terminated

### Process Groups

The supervisor automatically creates a new process group for the supervised process. This ensures that:
- All child processes are terminated when the parent is stopped
- Signals are properly propagated to all processes in the group
- No orphaned processes are left behind

### Error Handling

The supervisor provides clear error messages for common scenarios:
- Process already started
- Process not started
- Process already stopped
- Signal forwarding failures
- Timeout during shutdown

## Thread Safety

The supervisor is safe for concurrent use. Multiple goroutines can safely:
- Send signals to the process
- Query the process state
- Call Stop() (only the first call will take effect)

## Testing

The package includes comprehensive tests covering:
- Basic start/stop operations
- Graceful shutdown scenarios
- Force kill after timeout
- Signal forwarding
- Process group management
- Concurrent operations
- Error conditions

Run tests with:
```bash
go test -v
```

## License

This package is part of the sprite-env project.