# wsexec

A Go package for executing commands remotely over WebSocket connections.

## Features

- **Client Interface**: Connect to remote WebSocket servers and execute commands
- **Server Interface**: Handle WebSocket requests and execute commands locally  
- **TTY Support**: Pseudo-terminal support for interactive commands
- **Streaming I/O**: Real-time stdin/stdout/stderr streaming

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
}
```

## Server Command Configuration

Available methods:
- `SetTTY(bool)` - Enable/disable TTY mode
- `SetEnv([]string)` - Set environment variables  
- `SetWorkingDir(string)` - Set working directory
- `SetWrapperCommand([]string)` - Set wrapper command (e.g., timeout, sudo)
- `SetLogger(*slog.Logger)` - Set logger for debugging

Example:
```go
cmd := wsexec.NewServerCommand("bash")
cmd.SetTTY(true).
    SetEnv([]string{"TERM=xterm"}).
    SetWorkingDir("/tmp").
    SetWrapperCommand([]string{"timeout", "60"})
```

## Running Tests

```bash
go test -v
``` 