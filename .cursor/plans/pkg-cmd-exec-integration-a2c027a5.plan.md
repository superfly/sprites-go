<!-- a2c027a5-6a92-46a3-8ec4-1556974a3743 2b675dd7-a344-487d-a93e-3b257e414ff2 -->
# Integrate pkg/runner into Server Exec Endpoint

## Overview

Replace `pkg/terminal` with `pkg/runner` for process execution. errgroup + shared context for coordination. Runner handles all I/O pumping internally. Create new exec.go handler to test alongside existing exec_terminal.go.

## Architecture

```
server/api/exec.go (new file)
  ↓ builds base exec.Cmd (path, args, env, dir)
  ↓ passes through tmux.WrapSession() (future)
  ↓ passes through system.WrapContainer() (always, no-op if not needed)
  ↓ creates runner with wsReader/wsWriter
  ↓ g, ctx := errgroup.WithContext(ctx)
  ↓ g.Go(func() error { return run.Run(ctx) })
  ↓ g.Go(func() error { return wsMonitor.Wait(ctx) })
  ↓ g.Wait() -- procedural wait, auto-cancels on first error
  ↓ get exit code, log, done
```

**Design constraints:**

- Exec handler should be as procedural as possible
- Prefer channels that can be closed over callbacks
- Exec handler builds command, passes through wrappers, hands to runner
- Runner.Run(ctx) blocks until process completes, returns error only (exitCode stored internally)
- errgroup coordinates runner + websocket monitor with shared context
- First error (process exit or websocket close) cancels the other
- Handler waits on errgroup.Wait() - completely procedural
- Runner handles all I/O pumping - wsReader/wsWriter are just adapters

## Current Binary Protocol

**Non-TTY mode** - multiplexed: `[StreamID byte][payload...]`

- `0x00` = stdin (client → server, not used server-side)
- `0x01` = stdout (server → client)  
- `0x02` = stderr (server → client)
- `0x03` = exit code
- `0x04` = stdin EOF

**TTY mode** - raw binary (no multiplexing)

## Implementation Steps

### 1. Modify pkg/runner Package

**Note:** pkg/runner already exists (renamed from pkg/cmd). Modify existing files.

**File: `pkg/runner/runner.go`** (modify existing)

Add exitCode field and update Run signature:

```go
// Runner executes a command with I/O streams
type Runner struct {
    cmd    *exec.Cmd
    config *runConfig
    
    // PTY state (for TTY mode resize)
    pty      *os.File      // set once, no mutex needed
    ptyReady chan struct{} // closed when PTY is set (only for WithWaitTTY)
    
    // Exit state
    exitCode int
}

// PID returns the process ID (available after cmd.Start() completes)
func (r *Runner) PID() int {
    if r.cmd.Process == nil {
        return -1
    }
    return r.cmd.Process.Pid
}

// Run starts and waits for the process to complete (blocking)
// Stores exit code internally, returns any error
// Context cancellation kills the process
func (r *Runner) Run(ctx context.Context) error {
    var err error
    if r.config.newTTY || r.config.waitTTYFunc != nil {
        r.exitCode, err = runWithTTY(ctx, r.cmd, r.config, r)
    } else {
        r.exitCode, err = runWithoutTTY(ctx, r.cmd, r.config)
    }
    return err
}

// ExitCode returns the exit code (call after Run completes)
func (r *Runner) ExitCode() int {
    return r.exitCode
}

// GetTTY returns the PTY file, waiting if not yet ready (for TTY mode only)
func (r *Runner) GetTTY() (*os.File, error) {
    // If ptyReady is nil, PTY was allocated synchronously (WithNewTTY)
    if r.ptyReady != nil {
        <-r.ptyReady // wait for PTY to be ready
    }
    
    if r.pty == nil {
        return nil, fmt.Errorf("no PTY allocated")
    }
    
    return r.pty, nil
}

// Resize resizes the PTY (only for TTY mode)
func (r *Runner) Resize(cols, rows uint16) error {
    pty, err := r.GetTTY()
    if err != nil {
        return err
    }
    
    ws := &unix.Winsize{Row: rows, Col: cols}
    return unix.IoctlSetWinsize(int(pty.Fd()), unix.TIOCSWINSZ, ws)
}
```

**File: `pkg/runner/run.go`** (new file - shared I/O logic)

```go
//go:build !windows

package runner

import (
    "context"
    "io"
    "os"
    "os/exec"
    "syscall"
)

// ioStreams represents the actual I/O sources/sinks for the process
type ioStreams struct {
    stdinSrc  io.Reader     // where stdin comes from (wsReader)
    stdoutDst io.Writer     // where stdout goes (wsWriter or mux.StdoutWriter)
    stderrDst io.Writer     // where stderr goes (mux.StderrWriter for non-TTY)
    
    stdinPipe  io.WriteCloser // stdin pipe to process (if needed)
    stdoutPipe io.Reader      // stdout pipe from process (if needed)
    stderrPipe io.Reader      // stderr pipe from process (if needed)
}

// setupIO prepares I/O streams based on TTY mode
func setupIO(cmd *exec.Cmd, cfg *runConfig, ptyMaster *os.File) (*ioStreams, error) {
    streams := &ioStreams{
        stdinSrc:  cfg.stdin,
        stdoutDst: cfg.stdout,
        stderrDst: cfg.stderr,
    }
    
    if ptyMaster != nil {
        // TTY mode: all I/O through PTY
        streams.stdoutPipe = ptyMaster
        streams.stdinPipe = ptyMaster
        
    } else {
        // Non-TTY: direct pipes
        cmd.Stdout = cfg.stdout
        cmd.Stderr = cfg.stderr
        
        if cfg.stdin != nil {
            p, err := cmd.StdinPipe()
            if err != nil {
                return nil, err
            }
            streams.stdinPipe = p
        }
    }
    
    return streams, nil
}

// pumpIO starts goroutines to pump data
func pumpIO(streams *ioStreams) (stdinDone, stdoutDone, stderrDone chan struct{}) {
    stdinDone = make(chan struct{})
    stdoutDone = make(chan struct{})
    stderrDone = make(chan struct{})
    
    // Pump stdin
    if streams.stdinPipe != nil && streams.stdinSrc != nil {
        go func() {
            defer close(stdinDone)
            io.Copy(streams.stdinPipe, streams.stdinSrc)
            streams.stdinPipe.Close()
        }()
    } else {
        close(stdinDone)
    }
    
    // Pump stdout
    if streams.stdoutPipe != nil {
        go func() {
            defer close(stdoutDone)
            io.Copy(streams.stdoutDst, streams.stdoutPipe)
        }()
    } else {
        close(stdoutDone)
    }
    
    close(stderrDone) // Not used
    
    return stdinDone, stdoutDone, stderrDone
}

// waitForProcess waits for cmd to complete or context cancellation
func waitForProcess(ctx context.Context, cmd *exec.Cmd, ioDone ...chan struct{}) error {
    waitCh := make(chan error, 1)
    go func() { waitCh <- cmd.Wait() }()
    
    var waitErr error
    select {
    case <-ctx.Done():
        killProcessGroup(cmd)
        waitErr = <-waitCh
    case waitErr = <-waitCh:
    }
    
    for _, ch := range ioDone {
        <-ch
    }
    
    return waitErr
}

// killProcessGroup kills process group
func killProcessGroup(cmd *exec.Cmd) {
    if cmd.Process == nil {
        return
    }
    
    if pgid, err := syscall.Getpgid(cmd.Process.Pid); err == nil {
        _ = syscall.Kill(-pgid, syscall.SIGKILL)
    } else {
        _ = cmd.Process.Kill()
    }
}

// exitCodeFromError extracts exit code
func exitCodeFromError(err error) (int, error) {
    if err == nil {
        return 0, nil
    }
    if ee, ok := err.(*exec.ExitError); ok {
        return ee.ExitCode(), nil
    }
    return -1, err
}
```

**File: `pkg/runner/run_tty_unix.go`** (modify existing)

```go
func runWithTTY(ctx context.Context, cmd *exec.Cmd, cfg *runConfig, r *Runner) (int, error) {
    var master *os.File
    
    if cmd.SysProcAttr == nil {
        cmd.SysProcAttr = &syscall.SysProcAttr{}
    }
    cmd.SysProcAttr.Setpgid = true
    
    switch {
    case cfg.newTTY:
        m, slave, err := creackpty.Open()
        if err != nil {
            return -1, fmt.Errorf("open pty: %w", err)
        }
        master = m
        defer master.Close()
        
        cmd.Stdin = slave
        cmd.Stdout = slave
        cmd.Stderr = slave
        cmd.SysProcAttr.Setsid = true
        cmd.SysProcAttr.Setctty = true
        
        if err := cmd.Start(); err != nil {
            slave.Close()
            return -1, err
        }
        slave.Close()
        
        r.pty = master
        
    case cfg.waitTTYFunc != nil:
        if err := cmd.Start(); err != nil {
            return -1, err
        }
        
        m, err := cfg.waitTTYFunc(ctx)
        if err != nil {
            killProcessGroup(cmd)
            cmd.Process.Wait()
            return -1, err
        }
        master = m
        defer master.Close()
        
        r.pty = master
        close(r.ptyReady)
    
    default:
        return -1, fmt.Errorf("tty mode not selected")
    }
    
    streams, err := setupIO(cmd, cfg, master)
    if err != nil {
        return -1, err
    }
    
    stdinDone, stdoutDone, stderrDone := pumpIO(streams)
    
    waitErr := waitForProcess(ctx, cmd, stdinDone, stdoutDone, stderrDone)
    return exitCodeFromError(waitErr)
}
```

**File: `pkg/runner/run_non_tty.go`** (modify existing)

```go
func runWithoutTTY(ctx context.Context, cmd *exec.Cmd, cfg *runConfig) (int, error) {
    if cmd.SysProcAttr == nil {
        cmd.SysProcAttr = &syscall.SysProcAttr{}
    }
    cmd.SysProcAttr.Setpgid = true
    
    streams, err := setupIO(cmd, cfg, nil)
    if err != nil {
        return -1, err
    }
    
    if err := cmd.Start(); err != nil {
        if streams.stdinPipe != nil {
            streams.stdinPipe.Close()
        }
        return -1, err
    }
    
    stdinDone, stdoutDone, stderrDone := pumpIO(streams)
    
    waitErr := waitForProcess(ctx, cmd, stdinDone, stdoutDone, stderrDone)
    return exitCodeFromError(waitErr)
}
```

### 2. Create Stream Multiplexer

**File: `pkg/runner/multiplexer.go`** (already exists, verify format matches)

### 3. System Wrapper Function

**File: `server/system/wrap.go`** (new file)

```go
package system

import (
    "os/exec"
    "github.com/superfly/sprite-env/pkg/container"
)

func (s *System) WrapContainer(cmd *exec.Cmd, tty bool) *exec.Cmd {
    if s.containerName == "" {
        return cmd
    }
    
    wrapped := container.WrapCommand(cmd, s.containerName,
        container.WithTTY(tty))
    return wrapped.Cmd
}
```

### 4. Container Package Helper

**File: `pkg/container/wrap.go`** (enhance existing)

```go
// GetPTYFunc returns function for runner.WithWaitTTY()
func GetPTYFunc(socketPath string) func(context.Context) (*os.File, error) {
    return func(ctx context.Context) (*os.File, error) {
        tty := NewWithPath(socketPath)
        defer tty.Close()
        return tty.Get()
    }
}
```

### 5. Create New Exec Handler

**File: `server/api/exec.go`** (new file)

```go
package api

import (
    "context"
    "encoding/json"
    "fmt"
    "net/http"
    "os/exec"
    "sync"
    "time"
    
    "github.com/gorilla/websocket"
    "github.com/superfly/sprite-env/pkg/container"
    "github.com/superfly/sprite-env/pkg/runner"
    "golang.org/x/sync/errgroup"
)

func (h *Handlers) HandleExecNew(w http.ResponseWriter, r *http.Request) {
    // [Parse query params]
    
    conn, err := h.upgrader.Upgrade(w, r, nil)
    if err != nil {
        return
    }
    defer conn.Close()
    
    // Build command
    baseCmd := exec.CommandContext(r.Context(), cmdPath, args...)
    baseCmd.Env = os.Environ()
    baseCmd.Env = append(baseCmd.Env, userEnv...)
    if workingDir != "" {
        baseCmd.Dir = workingDir
    }
    
    // Pass through wrappers
    finalCmd := h.system.WrapContainer(baseCmd, tty)
    
    // Create I/O adapters
    wsReader := &wsReader{conn: conn}
    wsWriter := &wsWriter{conn: conn}
    
    // Build runner options
    var opts []runner.Option
    var mux *runner.MultiplexedWriter
    
    opts = append(opts, runner.WithStdin(wsReader))
    
    if tty {
        opts = append(opts, runner.WithStdout(wsWriter))
        
        if h.system.ContainerName() != "" {
            socketPath := fmt.Sprintf("/tmp/console-%d.sock", time.Now().UnixNano())
            getPTY := container.GetPTYFunc(socketPath)
            opts = append(opts, runner.WithWaitTTY(getPTY))
        } else {
            opts = append(opts, runner.WithNewTTY())
        }
    } else {
        mux = runner.NewMultiplexedWriter(wsWriter)
        opts = append(opts, runner.WithStdout(mux.StdoutWriter()))
        opts = append(opts, runner.WithStderr(mux.StderrWriter()))
    }
    
    // Create runner
    run, err := runner.New(finalCmd, opts...)
    if err != nil {
        h.logger.Error("Failed to create runner", "error", err)
        return
    }
    
    wsReader.run = run
    
    // errgroup coordinates
    g, ctx := errgroup.WithContext(r.Context())
    
    g.Go(func() error {
        return run.Run(ctx)
    })
    
    wsMonitor := &wsMonitor{conn: conn, logger: h.logger}
    g.Go(func() error {
        return wsMonitor.Wait(ctx)
    })
    
    time.Sleep(10 * time.Millisecond)
    pid := run.PID()
    h.logger.Info("Process started", "pid", pid)
    
    if h.portWatcher != nil && pid > 0 {
        h.portWatcher.AddPID(pid)
    }
    
    if err := g.Wait(); err != nil {
        h.logger.Debug("Exec completed with error", "error", err)
    }
    
    exitCode := run.ExitCode()
    
    if !tty && mux != nil {
        mux.WriteExit(exitCode)
    }
    
    h.logger.Info("Exec completed", "pid", pid, "exitCode", exitCode)
}

type wsReader struct {
    conn *websocket.Conn
    buf  []byte
    run  *runner.Runner
}

func (r *wsReader) Read(p []byte) (int, error) {
    for {
        if len(r.buf) > 0 {
            n := copy(p, r.buf)
            r.buf = r.buf[n:]
            return n, nil
        }
        
        msgType, data, err := r.conn.ReadMessage()
        if err != nil {
            return 0, err
        }
        
        switch msgType {
        case websocket.BinaryMessage:
            r.buf = data
            n := copy(p, r.buf)
            r.buf = r.buf[n:]
            return n, nil
            
        case websocket.TextMessage:
            var msg struct {
                Type string  `json:"type"`
                Cols uint16  `json:"cols,omitempty"`
                Rows uint16  `json:"rows,omitempty"`
            }
            if err := json.Unmarshal(data, &msg); err != nil {
                continue
            }
            if msg.Type == "resize" && r.run != nil {
                r.run.Resize(msg.Cols, msg.Rows)
            }
        }
    }
}

type wsWriter struct {
    conn *websocket.Conn
    mu   sync.Mutex
}

func (w *wsWriter) Write(p []byte) (int, error) {
    w.mu.Lock()
    defer w.mu.Unlock()
    
    if err := w.conn.WriteMessage(websocket.BinaryMessage, p); err != nil {
        return 0, err
    }
    return len(p), nil
}

type wsMonitor struct {
    conn   *websocket.Conn
    logger *slog.Logger
}

func (m *wsMonitor) Wait(ctx context.Context) error {
    for {
        select {
        case <-ctx.Done():
            return ctx.Err()
        default:
            if _, _, err := m.conn.ReadMessage(); err != nil {
                m.logger.Debug("Websocket closed", "error", err)
                return err
            }
        }
    }
}
```

## Testing Strategy

1. **Keep exec_terminal.go working** - don't break existing tests
2. Add new route for HandleExecNew
3. Test new handler manually
4. Compare behavior between old and new
5. Once validated, replace exec_terminal.go with exec.go

## Files to Create/Modify

**New files:**

- `pkg/runner/run.go` - shared I/O logic
- `server/system/wrap.go` - container wrapper
- `server/api/exec.go` - new exec handler

**Modified files:**

- `pkg/runner/runner.go` - add exitCode field, update Run()
- `pkg/runner/run_tty_unix.go` - use shared I/O helpers
- `pkg/runner/run_non_tty.go` - use shared I/O helpers
- `pkg/container/wrap.go` - add GetPTYFunc
- `server/api/server.go` - add route for new handler

## Next Up: TMux Manager

After this work is complete and tests pass, integrate tmux manager which currently lives in pkg/terminal. This is a separate phase.

### To-dos

- [ ] 