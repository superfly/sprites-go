# Port Watcher

A Go package that monitors when a process or its children start listening on ports bound to localhost or all interfaces.

## Features

- Monitors a specific process and all its child processes
- Detects new TCP ports bound to:
  - **IPv4**: `127.0.0.1` (localhost) and `0.0.0.0` (all interfaces)
  - **IPv6**: `::1` (localhost) and `::` (all interfaces)
- Uses fsnotify to watch `/proc/net/tcp` and `/proc/net/tcp6` for changes
- Provides callbacks when new ports are detected

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

1. The package uses `fsnotify` to monitor changes to `/proc/net/tcp` and `/proc/net/tcp6`
2. When changes are detected, it parses the TCP connection table
3. For each listening socket on monitored addresses (127.0.0.1, 0.0.0.0, ::1, ::), it finds the owning process by checking `/proc/*/fd/*`
4. It verifies if the process is in the target process tree (the monitored PID or its children)
5. New ports trigger the callback function

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

## Limitations

- Only monitors TCP ports (not UDP)
- Only monitors specific addresses: localhost (127.0.0.1, ::1) and all interfaces (0.0.0.0, ::)
- Requires access to `/proc` filesystem (Linux only)
- May require appropriate permissions to read `/proc/*/fd/*` for other processes

## License

See the parent project's LICENSE file.