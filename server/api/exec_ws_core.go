package api

import (
	"context"
	"encoding/json"
	"io"
	"net/url"
	"os"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/pkg/container"
	portwatcher "github.com/superfly/sprite-env/pkg/port-watcher"
	"github.com/superfly/sprite-env/pkg/runner"
)

// WSLike is a minimal interface implemented by *websocket.Conn and wss.OpConn
// that supports the exec streaming protocol.
type WSLike interface {
	ReadMessage() (int, []byte, error)
	WriteMessage(int, []byte) error
}

// ServeExecWS serves the exec flow over a WS-like connection using existing query params.
func (h *Handlers) ServeExecWS(ctx context.Context, ws WSLike, query url.Values) error {
	// Parse command
	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		cmdArgs = query["cmd[]"]
	}

	// tmux params
	sessionID := query.Get("id")
	detachable := (query.Get("detachable") == "true")
	controlMode := (query.Get("cc") == "true")

	path := query.Get("path")
	if path == "" && len(cmdArgs) > 0 {
		path = cmdArgs[0]
	}
	if path == "" {
		path = "bash"
	}
	var args []string
	if len(cmdArgs) > 1 {
		args = cmdArgs[1:]
	}
	tty := (query.Get("tty") == "true")
	// TTY: default to stdin enabled unless explicitly disabled with stdin=false
	// Non-TTY: default to no stdin unless explicitly enabled with stdin=true
	var stdinEnabled bool
	if tty {
		stdinEnabled = (query.Get("stdin") != "false")
	} else {
		stdinEnabled = (query.Get("stdin") == "true")
	}

	// Build base cmd with env and dir
	baseCmd := h.buildExecCommand(path, args, query)

	// Build final command considering tmux detachable/attach
	finalCmd := baseCmd
	var monitoredSessionID string
	if h.system != nil {
		if tm := h.system.GetTMUXManager(); tm != nil {
			if sessionID != "" {
				// Attach flow builds full command
				finalCmd = tm.AttachCmd(sessionID, controlMode)
				monitoredSessionID = sessionID
			} else if detachable {
				// New detachable session
				cmd, newID := tm.NewSessionCmd(baseCmd, controlMode)
				finalCmd = cmd
				monitoredSessionID = newID
			}
		}
	}

	// Wrap for container last, and avoid double-wrapping if tmux manager already wrapped
	var wrapped *container.WrappedCommand
	if h.containerEnabled && !isAlreadyContainerWrapped(finalCmd) {
		wrapped = container.Wrap(finalCmd, "app", container.WithTTY(tty))
		if wrapped != nil {
			finalCmd = wrapped.Cmd
		}
	}

	// I/O adapters using a WS-like wrapper
	type readWriter interface {
		ReadMessage() (int, []byte, error)
		WriteMessage(int, []byte) error
	}
	rw := ws.(readWriter)
	wsR := &wsLikeReader{readFn: rw.ReadMessage}
	wsW := &wsLikeWriter{writeFn: func(p []byte) error { return rw.WriteMessage(gorillaws.BinaryMessage, p) }}

	// For detachable sessions, we capture stdout into a limited-size buffer in addition to streaming.
	var stdoutWriter io.Writer = wsW
	var captureBuf *limitedBuffer
	if detachable {
		captureBuf = newLimitedBuffer(5 * 1024)
		stdoutWriter = io.MultiWriter(wsW, captureBuf)
	}

	// For TTY sessions, also capture process stderr (e.g., tmux emits to stderr) to server logs
	var stderrLogger io.Writer

	// Runner options
	var opts []runner.Option
	var mux *runner.MultiplexedWriter
	if stdinEnabled {
		opts = append(opts, runner.WithStdin(wsR))
	} else if tty {
		// TTY control-only stdin path
		opts = append(opts, runner.WithStdin(wsR), runner.WithConsumeOnlyStdin())
	}

	if tty {
		stderrLogger = &logWriter{logger: h.logger}
		opts = append(opts, runner.WithStdout(stdoutWriter))
		opts = append(opts, runner.WithStderr(stderrLogger))
		if wrapped != nil {
			// Use wrapped.GetPTY method to fetch PTY after Start
			opts = append(opts, runner.WithWaitTTY(func(ctx context.Context) (*os.File, error) { return wrapped.GetPTY() }))
		} else {
			opts = append(opts, runner.WithNewTTY())
		}
	} else {
		// Non-TTY: use a multiplexed writer to serialize stdout/stderr and allow exit signaling
		mux = runner.NewMultiplexedWriter(stdoutWriter)
		opts = append(opts, runner.WithStdout(mux.StdoutWriter()))
		opts = append(opts, runner.WithStderr(mux.StderrWriter()))
	}

	run, err := runner.NewWithContext(ctx, finalCmd, opts...)
	if err != nil {
		return err
	}
	wsR.run = run

	// Start process (async)
	if err := run.Start(); err != nil {
		return err
	}

	// PID (blocks until ready)
	pid := run.PID()

	// Create and start port watcher now that we have a PID
	var watcher *portwatcher.PortWatcher
	{
		callback := func(p portwatcher.Port) {
			msgType := ""
			if p.State == "open" {
				msgType = "port_opened"
			} else if p.State == "closed" {
				msgType = "port_closed"
			}
			if msgType == "" {
				return
			}
			addr := h.mapProxyAddress(p.Address)
			// Reuse old JSON format
			_ = h.sendPortNotificationRaw(ws, execPortNotificationMessage{
				Type:    msgType,
				Port:    p.Port,
				Address: addr,
				PID:     p.PID,
			})
		}
		if w, err := portwatcher.New(pid, "sprite", callback); err == nil {
			watcher = w
			_ = watcher.Start()
		}
	}

	// If tmux is engaged, wire pane PID lifecycle and seed existing panes
	if h.system != nil && monitoredSessionID != "" && h.system.GetTMUXManager() != nil && watcher != nil {
		tm := h.system.GetTMUXManager()
		tm.SetPaneCallback(monitoredSessionID, func(_ string, panePID int, added bool) {
			if added {
				_ = watcher.AddPID(panePID)
				return
			}
			watcher.RemovePID(panePID)
		})
		if panes, err := tm.GetSessionPanePIDs(monitoredSessionID); err == nil {
			for _, p := range panes {
				_ = watcher.AddPID(p)
			}
		}
	}

	// Cleanup
	defer func() {
		if h.system != nil && monitoredSessionID != "" && h.system.GetTMUXManager() != nil {
			h.system.GetTMUXManager().RemovePaneCallback(monitoredSessionID)
		}
		if watcher != nil {
			watcher.Stop()
		}
	}()

	startWall := time.Now()
	// Wait for completion
	_ = run.Wait()
	exitCode := run.ExitCode()
	// Quick-exit warning for very short-lived sessions
	if time.Since(startWall) < time.Second {
		h.logger.Warn("exec exited quickly (<1s)", "exitCode", exitCode)
	}

	// If detachable and we captured stdout, persist a truncated log file for later inspection
	if detachable && captureBuf != nil && monitoredSessionID != "" && sessionID == "" {
		// Ensure directory exists
		_ = os.MkdirAll("/.sprite/tmp", 0755)
		logPath := "" // set by monitoredSessionID
		logPath = "/.sprite/tmp/exec-" + monitoredSessionID + ".log"
		_ = os.WriteFile(logPath, captureBuf.Bytes(), 0644)
	}

	// For non-TTY, write exit via multiplexer before returning
	if !tty && mux != nil {
		_ = mux.WriteExit(exitCode)
	}
	return nil
}

// wsLikeReader and wsLikeWriter adapt WSLike via function pointers.
type wsLikeReader struct {
	buf    []byte
	run    *runner.Runner
	readFn func() (int, []byte, error)
}

func (r *wsLikeReader) Read(p []byte) (int, error) {
	for {
		if len(r.buf) > 0 {
			n := copy(p, r.buf)
			r.buf = r.buf[n:]
			return n, nil
		}
		mt, data, err := r.readFn()
		if err != nil {
			return 0, err
		}
		switch mt {
		case gorillaws.BinaryMessage:
			// Treat a single-byte 0x04 (StreamStdinEOF) as EOF for control paths
			if len(data) == 1 && data[0] == 4 {
				return 0, io.EOF
			}
			r.buf = data
		case gorillaws.TextMessage:
			var msg struct {
				Type string `json:"type"`
				Cols uint16 `json:"cols,omitempty"`
				Rows uint16 `json:"rows,omitempty"`
			}
			if json.Unmarshal(data, &msg) == nil && msg.Type == "resize" && r.run != nil {
				_ = r.run.Resize(msg.Cols, msg.Rows)
			}
		}
	}
}

type wsLikeWriter struct {
	writeFn func([]byte) error
}

func (w *wsLikeWriter) Write(p []byte) (int, error) {
	if err := w.writeFn(p); err != nil {
		return 0, err
	}
	return len(p), nil
}

// sendPortNotificationRaw writes a JSON text message over the websocket-like connection
func (h *Handlers) sendPortNotificationRaw(ws WSLike, msg execPortNotificationMessage) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}
	return ws.WriteMessage(gorillaws.TextMessage, data)
}
