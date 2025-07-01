# Terminal Package

The `terminal` package provides a reusable library for interactive and non-interactive command execution with PTY support and transcript recording. It's designed to be decoupled from specific transport mechanisms (like WebSockets) while providing comprehensive terminal functionality.

## Features

- **PTY Support**: Automatic PTY allocation or console socket integration (for crun)
- **Transcript Recording**: Pluggable transcript collection for session recording
- **Stream Multiplexing**: Separate stdin/stdout/stderr streams for non-PTY mode
- **Terminal Resizing**: Built-in support for terminal resize events
- **Context Cancellation**: Proper cancellation support via `context.Context`
- **Flexible Configuration**: Builder pattern with functional options
- **Zero Dependencies**: Only depends on standard library and essential external packages

## Basic Usage

### Simple Command Execution

```go
package main

import (
    "context"
    "os"
    "strings"
    
    "github.com/superfly/sprite-env/pkg/terminal"
)

func main() {
    // Create a simple session
    session := terminal.NewSession(
        terminal.WithCommand("echo", "Hello, World!"),
        terminal.WithTTY(false),
    )
    
    // Run the command
    stdin := strings.NewReader("")
    exitCode, err := session.Run(context.Background(), stdin, os.Stdout, os.Stderr)
    if err != nil {
        panic(err)
    }
    
    println("Exit code:", exitCode)
}
```

### Interactive TTY Session

```go
session := terminal.NewSession(
    terminal.WithCommand("bash", "-l"),
    terminal.WithTTY(true),
    terminal.WithTerminalSize(80, 24),
    terminal.WithDir("/home/user"),
    terminal.WithEnv([]string{"EDITOR=vim"}),
)

exitCode, err := session.Run(ctx, os.Stdin, os.Stdout, os.Stderr)
```

### With Transcript Recording

```go
// Memory-based transcript
transcript := terminal.NewMemoryTranscript()
session := terminal.NewSession(
    terminal.WithCommand("make", "build"),
    terminal.WithTranscript(transcript),
)

exitCode, err := session.Run(ctx, stdin, stdout, stderr)

// Access recorded data
stdoutData := transcript.GetStreamData("stdout")
stderrData := transcript.GetStreamData("stderr")

// File-based transcript
fileTranscript, err := terminal.NewFileTranscript("/tmp/session.log")
if err != nil {
    panic(err)
}
defer fileTranscript.Close()

session = terminal.NewSession(
    terminal.WithCommand("npm", "test"),
    terminal.WithTranscript(fileTranscript),
)
```

### WebSocket Integration

```go
func handleWebSocketExec(w http.ResponseWriter, r *http.Request) {
    // Create terminal session
    session := terminal.NewSession(
        terminal.WithCommand("bash", "-l"),
        terminal.WithTTY(true),
        terminal.WithTerminalSize(80, 24),
    )
    
    // Create WebSocket handler
    wsHandler := terminal.NewWebSocketHandler(session)
    
    // Handle the WebSocket connection
    err := wsHandler.Handle(w, r)
    if err != nil {
        log.Printf("WebSocket error: %v", err)
    }
}
```

## Configuration Options

### Command Configuration

- `WithCommand(path string, args ...string)`: Sets the command to execute
- `WithEnv(env []string)`: Sets environment variables
- `WithDir(workingDir string)`: Sets the working directory
- `WithWrapper(wrapper []string)`: Sets a wrapper command (e.g., for exec.sh)

### Terminal Configuration

- `WithTTY(enabled bool)`: Enables or disables TTY mode
- `WithTerminalSize(cols, rows uint16)`: Sets initial terminal size for PTY mode
- `WithConsoleSocket(path string)`: Uses console socket for crun integration

### Logging and Recording

- `WithTranscript(collector TranscriptCollector)`: Sets transcript recorder
- `WithLogger(logger *slog.Logger)`: Sets structured logger

## Transcript Collection

The package provides a flexible transcript collection system with multiple backend options:

### Built-in Collectors

1. **SQLite Transcript** (Default): Stores transcripts in a structured SQLite database
```go
config := terminal.SQLiteTranscriptConfig{
    DBPath:  "/var/log/transcripts.db",
    WorkDir: &workDir,
    Env:     []string{"VAR=value"},
    TTY:     true,
    Logger:  logger,
}

transcript, err := terminal.NewSQLiteTranscript(config)
if err != nil {
    return err
}
defer transcript.Close()

// Use with terminal session
session := terminal.NewSession(
    terminal.WithCommand("echo", "hello"),
    terminal.WithTranscript(transcript),
)
```

2. **Memory Transcript**: Collects data in memory
```go
transcript := terminal.NewMemoryTranscript()
// ... use transcript ...
stdoutData := transcript.GetStreamData("stdout")
allStreams := transcript.GetAllStreams()
```

3. **File Transcript**: Logs to structured files
```go
transcript, err := terminal.NewFileTranscript("/path/to/transcript.log")
if err != nil {
    return err
}
defer transcript.Close()
```

4. **No-op Transcript**: Discards all data
```go
// Automatically used if no transcript is specified
session := terminal.NewSession(/* no transcript option */)
```

### SQLite Backend Features

The SQLite backend provides structured transcript storage:

- **Simple Schema**: Two-table design (sessions and log_lines)
- **Unique IDs**: All records have unique identifiers for API access
- **Essential Metadata**: Working directory, environment, timestamps
- **Concurrent Safe**: Proper transaction handling and locking
- **Efficient Queries**: Indexed for fast retrieval and filtering
- **Future-Ready**: Designed to support HTTP APIs for transcript access

#### Database Schema

```sql
-- Sessions table
CREATE TABLE sessions (
    session_id TEXT PRIMARY KEY,
    start_time INTEGER NOT NULL,
    end_time INTEGER DEFAULT NULL,
    working_dir TEXT DEFAULT NULL,
    environment TEXT DEFAULT NULL, -- JSON encoded
    tty BOOLEAN NOT NULL DEFAULT FALSE,
    exit_code INTEGER DEFAULT NULL,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
);

-- Log lines table
CREATE TABLE log_lines (
    line_id TEXT PRIMARY KEY,
    session_id TEXT NOT NULL,
    stream TEXT NOT NULL, -- 'stdin', 'stdout', 'stderr'
    sequence INTEGER NOT NULL, -- Global sequence within session
    timestamp INTEGER NOT NULL,
    message TEXT NOT NULL,
    created_at INTEGER NOT NULL,
    FOREIGN KEY (session_id) REFERENCES sessions(session_id)
);
```

#### Reading SQLite Transcripts

```go
// Create backend for reading
backend, err := terminal.NewSQLiteTranscriptBackend("/var/log/transcripts.db")
if err != nil {
    return err
}
defer backend.Close()

// Query log lines
query := terminal.LineQuery{
    SessionID:     "session-uuid",
    Stream:        "stdout", // or "stderr", "stdin", "all"
    Limit:         100,
    AfterSequence: 0, // Start from beginning
    Follow:        false, // For live streaming (not supported in SQLite backend)
}

lines, err := backend.GetLines(context.Background(), query)
if err != nil {
    return err
}

for _, line := range lines {
    fmt.Printf("[%s] %s: %s\n", line.Timestamp.Format(time.RFC3339), line.Stream, line.Text)
}

// Get session information
sqliteBackend := backend.(*terminal.SQLiteTranscriptBackend)
sessionInfo, err := sqliteBackend.GetSessionInfo(context.Background(), "session-uuid")
if err != nil {
    return err
}

fmt.Printf("Command: %s, Exit Code: %d\n", sessionInfo.Command, sessionInfo.ExitCode)

// List all sessions
sessions, err := sqliteBackend.ListSessions(context.Background(), 10, 0) // limit=10, offset=0
if err != nil {
    return err
}

for _, session := range sessions {
    fmt.Printf("Session %s: %s (exit: %d)\n", session.SessionID, session.Command, session.ExitCode)
}
```

### Backend Configuration

The SQLite backend is hardcoded as the only transcript backend. Configuration is simple:

#### Environment Variables

- `SPRITE_TRANSCRIPT_DB_PATH` - Path to SQLite database file (default: /var/log/transcripts.db)

#### JSON Configuration

```json
{
  "transcript_db_path": "/var/log/transcripts.db"
}
```

#### Requirements

The SQLite backend requires CGO to be enabled during compilation. If SQLite is unavailable, the system will fail to start rather than silently degrade.

### Custom Transcript Collectors

Implement the `TranscriptCollector` interface:

```go
type TranscriptCollector interface {
    StreamWriter(name string) io.Writer
    Close() error
}

type CustomTranscript struct {
    // your implementation
}

func (c *CustomTranscript) StreamWriter(name string) io.Writer {
    // return a writer for the named stream ("stdin", "stdout", "stderr")
}

func (c *CustomTranscript) Close() error {
    // cleanup resources
    return nil
}
```

## PTY Modes

The package supports three PTY modes:

1. **No PTY**: Separate stdin/stdout/stderr streams with multiplexing
2. **New PTY**: Creates a fresh PTY using `creack/pty`
3. **Console Socket**: Receives PTY from crun via Unix domain socket

### Console Socket Mode

Useful for container environments using crun:

```go
session := terminal.NewSession(
    terminal.WithCommand("bash"),
    terminal.WithTTY(true),
    terminal.WithConsoleSocket("/tmp/console.sock"),
    terminal.WithWrapper([]string{"/usr/bin/exec.sh"}),
)
```

## Terminal Resizing

For PTY sessions, you can resize the terminal:

```go
// During session execution, if you have access to the PTY file:
err := terminal.ResizeTerminal(ptyFile, newCols, newRows)

// Get current size:
cols, rows, err := terminal.GetTerminalSize(ptyFile)
```

## Error Handling

The `Run` method returns both an exit code and an error:

- **Exit code**: The command's exit status (0 for success, >0 for failure)
- **Error**: System-level errors (failed to start, I/O errors, etc.)

```go
exitCode, err := session.Run(ctx, stdin, stdout, stderr)
if err != nil {
    // System error (failed to start command, I/O error, etc.)
    return fmt.Errorf("session failed: %w", err)
}
if exitCode != 0 {
    // Command completed but returned non-zero exit code
    return fmt.Errorf("command failed with exit code %d", exitCode)
}
```

## Context Cancellation

Sessions respect context cancellation:

```go
ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
defer cancel()

exitCode, err := session.Run(ctx, stdin, stdout, stderr)
// Command will be terminated if context times out or is cancelled
```

## Architecture

The terminal package is designed with clear separation of concerns:

- **Session**: Core configuration and execution logic
- **TranscriptCollector**: Pluggable I/O recording
- **WebSocketHandler**: Transport-specific WebSocket integration
- **PTY Management**: Platform-specific terminal handling

This design allows the package to be used in various contexts:
- Direct command execution
- WebSocket-based terminal services
- Container-based execution environments
- Automated testing and CI/CD pipelines

## Testing

The package includes comprehensive tests:

```bash
cd pkg/terminal
go test -v
```

Tests cover:
- Basic command execution (TTY and non-TTY)
- Transcript collection
- Environment and working directory handling
- Wrapper command support
- Error conditions and cancellation

## Migration from wsexec

If you're migrating from the old `wsexec` package:

### Before (wsexec)
```go
cmd := wsexec.NewServerCommand("bash", "-l")
cmd.SetTTY(true)
cmd.SetWorkingDir("/tmp")
cmd.SetEnv([]string{"VAR=value"})
cmd.SetLogger(logger)
err := cmd.Handle(w, r) // WebSocket-specific
```

### After (terminal)
```go
session := terminal.NewSession(
    terminal.WithCommand("bash", "-l"),
    terminal.WithTTY(true),
    terminal.WithDir("/tmp"),
    terminal.WithEnv([]string{"VAR=value"}),
    terminal.WithLogger(logger),
)

// For WebSocket usage:
wsHandler := terminal.NewWebSocketHandler(session)
err := wsHandler.Handle(w, r)

// For direct usage:
exitCode, err := session.Run(ctx, stdin, stdout, stderr)
```

The main benefits of the new API:
- Transport-agnostic design
- Cleaner configuration with functional options
- Better testing support
- More flexible transcript recording
- Explicit separation of concerns
