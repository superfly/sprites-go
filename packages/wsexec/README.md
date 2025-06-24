# wsexec

A Go package for executing commands remotely over WebSocket connections with a simplified, efficient binary protocol.

## Features

- **Client Interface**: Connect to remote WebSocket servers and execute commands
- **Server Interface**: Handle WebSocket requests and execute commands locally  
- **TTY Support**: Full pseudo-terminal support with transparent byte streaming
- **Terminal Resize**: PTY resize support via control messages
- **Streaming I/O**: Real-time stdin/stdout/stderr streaming
- **Simple Protocol**: Minimal overhead binary protocol (no JSON encoding)
- **Large Data Support**: Efficient handling of large data transfers

## Protocol Overview

### PTY Mode (TTY enabled)
When TTY is enabled, the WebSocket uses a mixed message type approach:

**Binary Messages** - Raw terminal data:
```
[Client Terminal] <--raw bytes--> [WebSocket] <--raw bytes--> [Server PTY]
```
All terminal data, control sequences (except resize) pass through unchanged.

**Text Messages** - Control messages (JSON):
```json
{"type":"resize","cols":80,"rows":24}
```
Control messages are sent as text frames to avoid interfering with the raw byte stream.

### Non-PTY Mode  
Uses simple binary messages with stream IDs:
- First byte: stream identifier
  - `0x00`: stdin
  - `0x01`: stdout  
  - `0x02`: stderr
  - `0x03`: exit code
  - `0x04`: stdin EOF
- Remaining bytes: raw data

Example messages:
```
[0x00][stdin data...]     // Client -> Server
[0x01][stdout data...]    // Server -> Client
[0x02][stderr data...]    // Server -> Client
[0x04]                    // Client -> Server (EOF)
[0x03][exit_code_byte]    // Server -> Client
```

## Basic Server Example

```go
package main

import (
    "net/http"
    "github.com/sprite-env/packages/wsexec"
)

func main() {
    http.HandleFunc("/exec", func(w http.ResponseWriter, r *http.Request) {
        // Only handle WebSocket upgrades
        if r.Header.Get("Upgrade") != "websocket" {
            http.Error(w, "WebSocket upgrade required", http.StatusUpgradeRequired)
            return
        }
        
        // Create and configure command
        cmd := wsexec.NewServerCommand("echo", "hello", "world")
        cmd.SetTTY(false)  // Set to true for interactive commands like bash
        
        // Handle the WebSocket connection
        if err := cmd.Handle(w, r); err != nil {
            // Error is logged internally
        }
    })
    
    http.ListenAndServe(":8080", nil)
}
```

## Basic Client Example

```go
package main

import (
    "net/http"
    "os"
    "github.com/sprite-env/packages/wsexec"
)

func main() {
    // Create WebSocket request
    req, _ := http.NewRequest("POST", "ws://localhost:8080/exec", nil)
    
    // Create command
    cmd := wsexec.Command(req, "echo", "hello", "world")
    cmd.Stdout = os.Stdout
    cmd.Stderr = os.Stderr
    
    // Execute
    if err := cmd.Run(); err != nil {
        panic(err)
    }
    
    // Get exit code
    exitCode := cmd.ExitCode()
}
```

## Server Command Configuration

Available methods:
- `SetTTY(bool)` - Enable/disable TTY mode
- `SetEnv([]string)` - Set environment variables  
- `SetWorkingDir(string)` - Set working directory
- `SetWrapperCommand([]string)` - Set wrapper command (e.g., timeout, sudo)
- `SetLogger(*slog.Logger)` - Set logger for debugging
- `SetContext(context.Context)` - Set context for cancellation
- `SetConsoleSocketPath(string)` - Use crun's console socket feature

Example:
```go
cmd := wsexec.NewServerCommand("bash")
cmd.SetTTY(true).
    SetEnv([]string{"TERM=xterm"}).
    SetWorkingDir("/tmp").
    SetWrapperCommand([]string{"timeout", "60"})
```

## Architecture Benefits

- **Simplicity**: No complex message encoding/decoding
- **Performance**: Direct byte streaming with minimal overhead
- **Compatibility**: Terminal features "just work" in PTY mode
- **Reliability**: Uses Go's standard `io.Copy` for data transfer
- **Scalability**: Efficient handling of large data transfers

## Running Tests

```bash
go test -v
``` 