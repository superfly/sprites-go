# Container Package

This package provides TTY (pseudo-terminal) management for container runtimes like crun, including system-level configuration for enabling container features across your application.

## System Configuration

Container features are configured system-wide rather than per-process. This ensures consistent behavior across all processes in your application.

```go
import "github.com/superfly/sprite-env/packages/container"

// Configure containers system-wide
container.Configure(container.Config{
    Enabled:   true,                    // Enable container features
    SocketDir: "/var/run/containers",   // Directory for TTY sockets
})

// Check if containers are enabled
if container.IsEnabled() {
    fmt.Println("Container features are enabled")
}
```

## Process Management

When containers are enabled system-wide, all processes automatically get TTY support:

```go
// Create a process - TTY is automatic when containers are enabled
config := container.ProcessConfig{
    Config: supervisor.Config{
        Command: "crun",
        Args:    []string{"run", "mycontainer"},
    },
    TTYTimeout: 10 * time.Second,  // Optional timeout for PTY acquisition
}

process, err := container.NewProcess(config)
if err != nil {
    log.Fatal(err)
}
defer process.Stop()

// Start the process
pid, err := process.Start()
if err != nil {
    log.Fatal(err)
}

// Get the PTY when the container runtime sends it
pty, err := process.GetTTY()
if err != nil {
    log.Fatal(err)
}
defer pty.Close()

// Use the PTY for I/O with the container...
```

## Low-Level TTY Management

For direct TTY socket management:

```go
// Create a TTY manager
tty, err := container.TTY()
if err != nil {
    log.Fatal(err)
}
defer tty.Close()

// Get the socket path to pass to crun via --console-socket
socketPath := tty.SocketPath()

// Start your container with:
// crun run --console-socket=<socketPath> mycontainer

// Wait for the PTY
pty, err := tty.GetWithTimeout(5 * time.Second)
if err != nil {
    log.Fatal(err)
}
defer pty.Close()
```

## Environment Variables

When containers are enabled, the following environment variables are automatically set:
- `CONSOLE_SOCKET`: Path to the Unix domain socket for PTY transfer
- `CONTAINER_WRAPPED`: Set to "true" to indicate container features are active

## Configuration Details

The `container.Config` struct has the following fields:
- `Enabled`: Whether container features are enabled system-wide
- `SocketDir`: Directory where TTY socket files will be created (defaults to `/tmp`)

The socket directory will be created automatically if it doesn't exist when containers are enabled.

## Overview

This package provides a clean interface for:
- Creating a Unix domain socket for receiving PTY file descriptors
- Blocking until a PTY is received from the container runtime
- Managing the lifecycle of the socket and PTY file descriptor
- Integration with the supervisor package for process management with TTY support

## Usage

### Basic Usage

```go
import "github.com/superfly/sprite-env/packages/container"

// Create a TTY manager
tty, err := container.TTY()
if err != nil {
    log.Fatal(err)
}
defer tty.Close()

// Get the socket path to pass to crun --console-socket
socketPath := tty.SocketPath()

// Start your container with crun, passing socketPath
// ...

// Block until PTY is received (with 5 second default timeout)
ptyFile, err := tty.Get()
if err != nil {
    log.Fatal(err)
}
```

### Convenience Functions

```go
// AcquirePty provides a one-liner for common use cases
socketPath, getPty, cleanup, err := container.AcquirePty()
if err != nil {
    log.Fatal(err)
}
defer cleanup()

// Start container with socketPath
// ...

// Get the PTY file when ready
ptyFile, err := getPty()
```

### Custom Timeout

```go
// Create TTY with custom timeout
tty, err := container.TTY()
if err != nil {
    log.Fatal(err)
}

// Get PTY with 10 second timeout
pty, err := tty.GetWithTimeout(10 * time.Second)
```

## Integration with crun

When starting a container with crun, pass the socket path:

```bash
crun run --console-socket=/path/to/socket container-id
```

The container runtime will connect to the socket and send the PTY file descriptor, which this package will receive and make available to your application.

## Process Management

The package also provides `NewProcess` which integrates with the supervisor package to manage processes with automatic TTY support:

```go
// Create a process with TTY support
config := container.ProcessConfig{
    Config: supervisor.Config{
        Command: "crun",
        Args:    []string{"run", "mycontainer"},
    },
    EnableTTY: true,
}

process, err := container.NewProcess(config)
if err != nil {
    log.Fatal(err)
}
defer process.Stop()

// Start the process - CONSOLE_SOCKET is automatically set
pid, err := process.Start()
if err != nil {
    log.Fatal(err)
}

// Get the PTY when ready
pty, err := process.GetTTY()
if err != nil {
    log.Fatal(err)
}
```

### Process Builder

A fluent builder interface is also available:

```go
process, err := container.NewProcessBuilder("crun", "run", "mycontainer").
    WithTTY().
    WithTTYTimeout(10 * time.Second).
    WithEnv([]string{"CUSTOM_VAR=value"}).
    Build()
```

## Testing

Run tests with:

```bash
go test ./...
```