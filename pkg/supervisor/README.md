# Supervisor Package

A simple, robust process supervisor for Go that provides graceful shutdown, signal forwarding, process group management, and stdout/stderr subscription.

## Features

- **Simple API**: Start, stop, and manage processes with just a few method calls
- **Graceful Shutdown**: Sends SIGTERM first, then SIGKILL after a configurable grace period
- **Signal Forwarding**: Forward any signal to the supervised process
- **Process Group Management**: Automatically manages process groups to ensure child processes are cleaned up
- **Stdout/Stderr Subscription**: Multiple readers can subscribe to process output streams
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

    // Start the process - returns PID immediately
    pid, err := s.Start()
    if err != nil {
        log.Fatal(err)
    }
    log.Printf("Started process with PID: %d", pid)

    // Do some work...
    time.Sleep(5 * time.Second)

    // Stop the process gracefully
    if err := s.Stop(); err != nil {
        log.Fatal(err)
    }
}
```

### Output Stream Subscription

The supervisor supports multiple readers for both stdout and stderr streams:

```go
// Get stdout reader before starting the process
stdoutReader, err := s.StdoutPipe()
if err != nil {
    log.Fatal(err)
}
defer stdoutReader.Close()

// Get stderr reader
stderrReader, err := s.StderrPipe()
if err != nil {
    log.Fatal(err)
}
defer stderrReader.Close()

// Start the process
pid, err := s.Start()
if err != nil {
    log.Fatal(err)
}

// Read from stdout in a goroutine
go func() {
    scanner := bufio.NewScanner(stdoutReader)
    for scanner.Scan() {
        log.Printf("stdout: %s", scanner.Text())
    }
}()

// Read from stderr in a goroutine
go func() {
    scanner := bufio.NewScanner(stderrReader)
    for scanner.Scan() {
        log.Printf("stderr: %s", scanner.Text())
    }
}()
```

### Multiple Readers

Multiple readers can subscribe to the same stream independently:

```go
// Create multiple stdout readers
reader1, _ := s.StdoutPipe()
reader2, _ := s.StdoutPipe()
reader3, _ := s.StdoutPipe()

// Each reader receives a copy of all output
// Readers are independent - closing one doesn't affect others
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

pid, _ := s.Start()
log.Printf("Started process %d", pid)

// Wait for the process to exit
if err := s.Wait(); err != nil {
    log.Printf("Process exited with error: %v", err)
}

// Multiple calls to Wait() return the same result
err1 := s.Wait()
err2 := s.Wait()
// err1 == err2 (guaranteed)
```

## Configuration Options

- `Command`: The command to execute (required)
- `Args`: Command line arguments
- `GracePeriod`: Time to wait for graceful shutdown before force killing (default: 10s)
- `Env`: Environment variables (if not set, inherits from parent)
- `Dir`: Working directory (if not set, uses current directory)

## API Reference

### Methods

- `New(config Config) (*Supervisor, error)` - Create a new supervisor
- `Start() (int, error)` - Start the process and return its PID
- `Stop() error` - Gracefully stop the process
- `Signal(sig os.Signal) error` - Send a signal to the process
- `Wait() error` - Wait for the process to exit (can be called multiple times)
- `Pid() (int, error)` - Get the process ID
- `StdoutPipe() (io.ReadCloser, error)` - Get a reader for stdout
- `StderrPipe() (io.ReadCloser, error)` - Get a reader for stderr

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

### Output Streams

- Process stdout and stderr are always forwarded to the parent's stdout/stderr
- Additional readers can subscribe via `StdoutPipe()` and `StderrPipe()`
- Multiple readers are supported - each gets a copy of all output
- Readers use non-blocking writes with configurable buffer sizes (default: 4KB)
- If a reader's buffer is full, new data is dropped for that reader only
- All readers are automatically closed when the process exits

### Wait Behavior

- `Wait()` blocks until the process exits
- Multiple calls to `Wait()` are safe and return the same result
- The process exit status is captured only once
- Concurrent calls to `Wait()` from multiple goroutines are supported

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
- Create new output stream readers
- Call Wait() (all will receive the same result)

## Testing

The package includes comprehensive tests covering:
- Basic start/stop operations
- Graceful shutdown scenarios
- Force kill after timeout
- Signal forwarding
- Process group management
- Stdout/stderr subscription
- Multiple concurrent readers
- Concurrent operations
- Error conditions
- Various process failure modes

Run tests with:
```bash
go test -v
```

## License

This package is part of the sprite-env project.