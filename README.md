# Sprite SDK for Go

The Sprite SDK provides an idiomatic Go API for working with sprites. It offers a familiar interface that mirrors the standard `exec.Cmd` API, making it easy to execute commands on remote sprites as if they were local processes.

## Features

- **Familiar API**: Works identically to `exec.Cmd` from the standard library
- **Full I/O Support**: Complete stdin/stdout/stderr functionality
- **Pipe Support**: StdinPipe, StdoutPipe, and StderrPipe for streaming I/O
- **TTY Support**: Full pseudo-terminal support with resize capabilities
- **WebSocket Transport**: Efficient bidirectional communication over WebSocket
- **Context Support**: Proper context cancellation and timeout handling

## Installation

```bash
go get github.com/superfly/sprites-go
```

Note: The import path is `github.com/superfly/sprites-go` but the package name is `sprites`. You'll need to import it with an alias or the package name will be `sprites`.

## Quick Start

```go
package main

import (
    "fmt"
    "log"
    
    sprites "github.com/superfly/sprites-go"
)

func main() {
    // Create a client with authentication
    client := sprites.New("your-auth-token")
    
    // Get a sprite handle
    sprite := client.Sprite("my-sprite")
    
    // Run a command - just like exec.Command!
    cmd := sprite.Command("echo", "hello", "world")
    output, err := cmd.Output()
    if err != nil {
        log.Fatal(err)
    }
    
    fmt.Printf("Output: %s", output)
}
```

## Usage

### Client Setup

```go
// Create a client with default settings
client := sprites.New("your-auth-token")

// Or with custom base URL
client := sprites.New("your-auth-token", 
    sprites.WithBaseURL("http://localhost:8080"))

// Get a sprite handle
sprite := client.Sprite("my-sprite")
```

### Basic Command Execution

The SDK provides a `sprite.Cmd` type that works exactly like `exec.Cmd`:

```go
// Create a command
cmd := sprite.Command("ls", "-la", "/tmp")

// Run and wait for completion
err := cmd.Run()

// Or get the output
output, err := cmd.Output()

// Or get combined stdout and stderr
combined, err := cmd.CombinedOutput()
```

### Setting Environment and Working Directory

```go
cmd := sprite.Command("env")
cmd.Env = []string{"FOO=bar", "BAZ=qux"}
cmd.Dir = "/tmp"

output, err := cmd.Output()
```

### Working with I/O

```go
cmd := sprite.Command("grep", "pattern")

// Set stdin from a reader
cmd.Stdin = strings.NewReader("line 1\nline 2 with pattern\nline 3")

// Capture stdout and stderr separately
var stdout, stderr bytes.Buffer
cmd.Stdout = &stdout
cmd.Stderr = &stderr

err := cmd.Run()
```

### Using Pipes

For streaming I/O, use pipes just like with `exec.Cmd`:

```go
cmd := sprite.Command("cat")

// Get stdin pipe
stdin, err := cmd.StdinPipe()
if err != nil {
    log.Fatal(err)
}

// Get stdout pipe  
stdout, err := cmd.StdoutPipe()
if err != nil {
    log.Fatal(err)
}

// Start the command
if err := cmd.Start(); err != nil {
    log.Fatal(err)
}

// Write to stdin in a goroutine
go func() {
    defer stdin.Close()
    for i := 0; i < 10; i++ {
        fmt.Fprintf(stdin, "Line %d\n", i)
        time.Sleep(100 * time.Millisecond)
    }
}()

// Read from stdout
scanner := bufio.NewScanner(stdout)
for scanner.Scan() {
    fmt.Println("Got:", scanner.Text())
}

// Wait for command to finish
err = cmd.Wait()
```

### Context Support

Use context for cancellation and timeouts:

```go
ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
defer cancel()

cmd := sprite.CommandContext(ctx, "long-running-command")
err := cmd.Run()
// Command will be killed if context times out
```

### TTY Support

Enable TTY mode for interactive commands:

```go
cmd := sprite.Command("bash")
cmd.SetTTY(true)

// Optionally set initial terminal size
err := cmd.SetTTYSize(24, 80)

// Start the command
if err := cmd.Start(); err != nil {
    log.Fatal(err)
}

// Resize the terminal while running
err = cmd.Resize(30, 100)

// Wait for completion
err = cmd.Wait()
```

### Error Handling

The SDK provides the same error types as `exec.Cmd`:

```go
cmd := sprite.Command("false")
err := cmd.Run()

if err != nil {
    // Check if it's an exit error
    if exitErr, ok := err.(*sprites.ExitError); ok {
        fmt.Printf("Command exited with code: %d\n", exitErr.ExitCode())
    } else {
        // Other error (connection, auth, etc.)
        log.Fatal(err)
    }
}
```

## Complete Example

Here's a complete example showing various features:

```go
package main

import (
    "context"
    "fmt"
    "log"
    "strings"
    "time"
    
    sprites "github.com/superfly/sprites-go"
)

func main() {
    // Create client with authentication
    client := sprites.New("your-auth-token", 
        sprites.WithBaseURL("https://api.sprite.example.com"))
    
    // Get a sprite handle
    sprite := client.Sprite("my-sprite")
    
    // Example 1: Simple command with output
    output, err := sprite.Command("date").Output()
    if err != nil {
        log.Fatal(err)
    }
    fmt.Printf("Current date: %s", output)
    
    // Example 2: Command with pipes and timeout
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    
    cmd := sprite.CommandContext(ctx, "grep", "-i", "error")
    cmd.Stdin = strings.NewReader("Line 1\nError on line 2\nLine 3\nAnother ERROR\n")
    
    output, err = cmd.Output()
    if err != nil {
        log.Fatal(err)
    }
    fmt.Printf("Grep results:\n%s", output)
    
    // Example 3: Interactive command with environment
    cmd = sprite.Command("bash", "-c", "echo Hello $USER from $HOSTNAME")
    cmd.Env = []string{"USER=sprite", "HOSTNAME=remote"}
    
    output, err = cmd.Output()
    if err != nil {
        log.Fatal(err)
    }
    fmt.Printf("Greeting: %s", output)
}
```

## API Reference

### Client Creation

```go
// Create a new sprites client
client := sprites.New(token string, opts ...Option)

// Available options:
sprites.WithBaseURL(url string)      // Set custom API endpoint
sprites.WithHTTPClient(client *http.Client)  // Use custom HTTP client
```

### Sprite Operations

```go
// Get a sprite handle (doesn't create it on the server)
sprite := client.Sprite(name string)

// Create a new sprite (future functionality)
sprite, err := client.Create(name string)

// List sprites (future functionality)
sprites, err := client.List()
```

### Command Execution

The `sprite.Cmd` type is designed to be a drop-in replacement for `exec.Cmd`. It implements the same methods with the same behavior:

- `Run()` - Start and wait for completion
- `Start()` - Start the command asynchronously  
- `Wait()` - Wait for a started command to complete
- `Output()` - Run and return stdout
- `CombinedOutput()` - Run and return combined stdout/stderr
- `StdinPipe()` - Create a pipe connected to stdin
- `StdoutPipe()` - Create a pipe connected to stdout
- `StderrPipe()` - Create a pipe connected to stderr

The following fields work identically to `exec.Cmd`:
- `Path` - The command to run
- `Args` - Command arguments (including Path as Args[0])
- `Env` - Environment variables
- `Dir` - Working directory
- `Stdin` - Standard input (nil, *os.File, or io.Reader)
- `Stdout` - Standard output (nil, *os.File, or io.Writer)
- `Stderr` - Standard error (nil, *os.File, or io.Writer)

## Testing

The SDK includes comprehensive tests that verify compatibility with `exec.Cmd` behavior. Run tests with:

```bash
# Tests run only on Linux
go test -v ./sdk/...
```

## License

See the main project LICENSE file.
