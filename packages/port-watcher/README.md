# Port Watcher

A Go package that monitors when a process or its children start listening on ports bound to localhost or all interfaces. It uses an efficient global namespace monitor that runs one monitoring loop per network namespace.

## Features

- Monitors a specific process and all its child processes
- Detects new TCP ports bound to:
  - **IPv4**: `127.0.0.1` (localhost) and `0.0.0.0` (all interfaces)
  - **IPv6**: `::1` (localhost) and `::` (all interfaces)
- Uses `nsenter` to access network namespaces without requiring the monitor to run inside the namespace
- Polls network state every second (configurable)
- Provides callbacks when new ports are detected
- Logs port discoveries with PID information

## Installation

```bash
go get github.com/superfly/sprite-env/packages/port-watcher
```

## Usage

```go
package main

import (
    "fmt"
    "log"
    "os"
    "time"
    
    portwatcher "github.com/superfly/sprite-env/packages/port-watcher"
)

func main() {
    // Create a callback function
    callback := func(port portwatcher.Port) {
        fmt.Printf("New port detected: %s:%d (PID: %d)\n", 
            port.Address, port.Port, port.PID)
    }
    
    // Create a port watcher for the current process
    pw, err := portwatcher.New(os.Getpid(), callback)
    if err != nil {
        log.Fatal(err)
    }
    defer pw.Stop()
    
    // Start monitoring
    if err := pw.Start(); err != nil {
        log.Fatal(err)
    }
    
    // Keep running
    time.Sleep(60 * time.Second)
}
```

## How It Works

1. **Global Namespace Monitor**: A singleton monitor manages all network namespaces efficiently
   - One monitoring loop per network namespace (not per process)
   - Finds PID 1 in each namespace for `nsenter` access
   - Uses subscription model for multiple watchers per namespace

2. **Network Namespace Detection**: When monitoring a new PID:
   - Determines the process's network namespace via `/proc/[pid]/ns/net`
   - Finds the namespace's init process (PID 1 in that namespace)
   - Creates or reuses a namespace watcher for that namespace

3. **Port Detection**: The namespace monitor polls every second via:
   ```bash
   nsenter -t <namespace_pid_1> -n cat /proc/net/tcp
   ```
   - Parses TCP connection tables for listening sockets
   - Finds process ownership via `/proc/*/fd/*` socket inodes
   - Only reports ports from subscribed process trees

4. **Subscription System**: 
   - PortWatcher instances subscribe to their PID tree
   - Global monitor notifies relevant subscribers when ports are detected
   - Deduplication ensures each address:port combination is reported only once (regardless of PID)

5. **IPv6 Filtering**:
   - Only monitors localhost (::1) and all interfaces (::) addresses
   - Unrecognized IPv6 addresses are logged once for debugging
   - Other IPv6 addresses (like public IPs) are intentionally skipped

## API

### Types

```go
type Port struct {
    Port    int    // The port number
    PID     int    // The process ID that owns the socket
    Address string // The address (127.0.0.1 or ::1)
}

type PortCallback func(port Port)
```

### Functions

#### New
```go
func New(pid int, callback PortCallback) (*PortWatcher, error)
```
Creates a new PortWatcher for the given process ID.

#### Start
```go
func (pw *PortWatcher) Start() error
```
Begins monitoring for new ports. Performs an initial scan and then watches for changes.

#### Stop
```go
func (pw *PortWatcher) Stop()
```
Stops the port watcher and cleans up resources.

## Testing

Run the tests with:

```bash
make test
```

The package includes comprehensive tests including:
- Unit tests for parsing TCP data
- Integration tests for port detection
- Network namespace tests (Linux only) that verify namespace isolation and monitoring
- Tests are automatically skipped on non-Linux systems

## Limitations

- Only monitors TCP ports (not UDP)
- Only monitors specific addresses: localhost (127.0.0.1, ::1) and all interfaces (0.0.0.0, ::)
- Requires access to `/proc` filesystem (Linux only)
- Requires `nsenter` command (Linux only)
- May require appropriate permissions to read `/proc/*/fd/*` for other processes
- Requires CAP_SYS_ADMIN capability or root privileges to use `nsenter`

## License

See the parent project's LICENSE file.