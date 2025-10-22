package api

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/pkg/container"
	portwatcher "github.com/superfly/sprite-env/pkg/port-watcher"
	"github.com/superfly/sprite-env/pkg/runner"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// ExecHandler implements the new exec flow using pkg/runner and pkg/tmux.Manager
func (h *Handlers) ExecHandler(w http.ResponseWriter, r *http.Request) {
	// Only accept GET (WebSocket upgrade)
	if r.Method != http.MethodGet {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	query := r.URL.Query()

	// Parse command
	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		cmdArgs = query["cmd[]"]
	}

	// tmux params
	sessionID := query.Get("id")
	detachable := (query.Get("detachable") == "true")
	controlMode := (query.Get("cc") == "true")

	// If no command and no id, serve list route (match exec_terminal)
	if len(cmdArgs) == 0 && sessionID == "" {
		if r.Header.Get("Upgrade") == "websocket" {
			http.Error(w, "No command specified", http.StatusBadRequest)
			return
		}
		h.handleListExecSessionsNew(w, r)
		return
	}
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

	// Upgrade WebSocket
	upgrader := gorillaws.Upgrader{CheckOrigin: func(r *http.Request) bool { return true }}
	conn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		h.logger.Error("websocket upgrade failed", "error", err)
		return
	}
	defer conn.Close()

	// Build base cmd with env and dir
	baseCmd := h.buildExecCommand(path, args, query)

	// Build final command considering tmux detachable/attach
	finalCmd := baseCmd
	var monitoredSessionID string

	var wrapped *container.WrappedCommand
	if h.system != nil {
		if tm := h.system.GetTMUXManager(); tm != nil {
			if sessionID != "" {
				// Attach flow builds full command
				cmd, w := tm.Attach(sessionID, controlMode)
				finalCmd = cmd
				wrapped = w // capture for signaling (not for PTY)
				monitoredSessionID = sessionID
			} else if detachable {
				// New detachable session
				cmd, w, newID := tm.NewSession(baseCmd, controlMode)
				finalCmd = cmd
				wrapped = w // capture for signaling (not for PTY)
				monitoredSessionID = newID
			} else if h.containerEnabled {
				// Non-tmux path: always container wrap when enabled
				wrapped = container.Wrap(baseCmd, "app", container.WithTTY(tty))
				if wrapped != nil {
					finalCmd = wrapped.Cmd
					if h.logger != nil {
						h.logger.Info("using container wrapper for exec", "wrapper", "crun", "tty", tty)
					}
				}
			}
		}
	}

	// If not tmux and container wrapping wasn't decided above (e.g., no system manager), apply it now
	if wrapped == nil && monitoredSessionID == "" && h.containerEnabled {
		wrapped = container.Wrap(baseCmd, "app", container.WithTTY(tty))
		if wrapped != nil {
			// Log that we're using the container wrapper for this exec
			h.logger.Info("using container wrapper for exec", "wrapper", "crun", "tty", tty)
			finalCmd = wrapped.Cmd
			if h.logger != nil {
				h.logger.Info("using container wrapper for exec", "wrapper", "crun", "tty", tty)
			}
		}
	}
	// No tmux-provided wrapper fallback; rely on API layer wrapping only

	// I/O adapters
	wsR := &wsReader{conn: conn, wrapped: wrapped, logger: h.logger}
	wsW := &wsWriter{conn: conn}

	// For detachable sessions, we capture stdout into a limited-size buffer
	// in addition to streaming to the websocket.
	var stdoutWriter io.Writer = wsW
	var captureBuf *limitedBuffer
	if detachable {
		captureBuf = newLimitedBuffer(5 * 1024) // 5KB cap
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
		if monitoredSessionID != "" {
			// tmux path: allocate a new PTY in the runner; do not use container console
			opts = append(opts, runner.WithNewTTY())
		} else if wrapped != nil {
			// Non-tmux container path: use container console socket
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

	run, err := runner.NewWithContext(r.Context(), finalCmd, opts...)
	if err != nil {
		h.logger.Error("failed to create runner", "error", err)
		return
	}
	wsR.run = run

	// Start process (async)
	if err := run.Start(); err != nil {
		h.logger.Error("failed to start process", "error", err)
		return
	}

	// PID (blocks until ready)
	pid := run.PID()

	// Build log attributes with wrapper context tags
	logAttrs := []any{"pid", pid}
	if monitoredSessionID != "" {
		logAttrs = append(logAttrs, "sessionID", monitoredSessionID, "wrapper", "tmux")
	}
	if h.containerEnabled && wrapped != nil {
		logAttrs = append(logAttrs, "wrapper", "crun")
	}
	h.logger.Info("process started", logAttrs...)

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
			_ = h.sendPortNotification(conn, execPortNotificationMessage{
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
		logPath := fmt.Sprintf("/.sprite/tmp/exec-%s.log", monitoredSessionID)
		_ = os.WriteFile(logPath, captureBuf.Bytes(), 0644)
	}

	// For non-TTY, write exit via multiplexer before closing the socket
	if !tty && mux != nil {
		_ = mux.WriteExit(exitCode)
	}

	// Close socket
	_ = conn.WriteMessage(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, ""))
}

// limitedBuffer is a simple ring-like buffer that retains only the last N bytes written.
type limitedBuffer struct {
	cap int
	buf []byte
}

func newLimitedBuffer(max int) *limitedBuffer {
	return &limitedBuffer{cap: max}
}

func (b *limitedBuffer) Write(p []byte) (int, error) {
	if len(p) >= b.cap {
		// Take only the last cap bytes
		b.buf = make([]byte, b.cap)
		copy(b.buf, p[len(p)-b.cap:])
		return len(p), nil
	}
	// Append and trim from the front if needed
	b.buf = append(b.buf, p...)
	if len(b.buf) > b.cap {
		b.buf = b.buf[len(b.buf)-b.cap:]
	}
	return len(p), nil
}

func (b *limitedBuffer) Bytes() []byte {
	if b == nil {
		return nil
	}
	return append([]byte(nil), b.buf...)
}

// removed container wrapped heuristic; we deterministically wrap only non-tmux

// logWriter writes incoming bytes to the server logger at info level as stderr lines.
type logWriter struct {
	logger *slog.Logger
}

func (w *logWriter) Write(p []byte) (int, error) {
	if w == nil || w.logger == nil {
		return len(p), nil
	}
	w.logger.Info(string(p), "stdio", "stderr")
	return len(p), nil
}

// buildExecCommand builds a base exec.Cmd with environment and working directory set
func (h *Handlers) buildExecCommand(path string, args []string, query url.Values) *exec.Cmd {
	cmd := exec.Command(path, args...)
	if envVars := query["env"]; len(envVars) > 0 {
		cmd.Env = envVars
	} else {
		cmd.Env = []string{}
	}
	if dir := query.Get("dir"); dir != "" {
		cmd.Dir = dir
	} else {
		cmd.Dir = "/home/sprite"
	}
	return cmd
}

// execPortNotificationMessage represents a port event notification sent to the client
type execPortNotificationMessage struct {
	Type    string `json:"type"`
	Port    int    `json:"port"`
	Address string `json:"address"`
	PID     int    `json:"pid"`
}

// mapProxyAddress remaps localhost/wildcard addresses to proxyable bridge addrs when configured
func (h *Handlers) mapProxyAddress(addr string) string {
	switch addr {
	case "127.0.0.1":
		if h.proxyLocalhostIPv4 != "" {
			return h.proxyLocalhostIPv4
		}
	case "::1":
		if h.proxyLocalhostIPv6 != "" {
			return h.proxyLocalhostIPv6
		}
	case "0.0.0.0":
		if h.proxyLocalhostIPv4 != "" {
			return h.proxyLocalhostIPv4
		}
	case "::":
		if h.proxyLocalhostIPv6 != "" {
			return h.proxyLocalhostIPv6
		}
	}
	return addr
}

// sendPortNotification writes a JSON text message over the WebSocket
func (h *Handlers) sendPortNotification(conn *gorillaws.Conn, msg execPortNotificationMessage) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}
	return conn.WriteMessage(gorillaws.TextMessage, data)
}

// handleListExecSessionsNew mirrors exec_terminal list route but reads from the new tmux manager
func (h *Handlers) handleListExecSessionsNew(w http.ResponseWriter, r *http.Request) {
	tm := h.system.GetTMUXManager()
	if tm == nil {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"sessions": []any{},
			"count":    0,
			"error":    "TMUXManager not configured",
		})
		return
	}
	sessions, err := tm.ListSessionsWithInfo()
	if err != nil {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"sessions": []any{},
			"count":    0,
			"error":    fmt.Sprintf("Failed to list sessions: %v", err),
		})
		return
	}
	activityMap := tm.GetAllSessionActivityInfo()
	type SessionWithActivity struct {
		tmux.SessionInfo
		BytesPerSecond float64    `json:"bytes_per_second"`
		IsActive       bool       `json:"is_active"`
		LastActivity   *time.Time `json:"last_activity,omitempty"`
	}
	sessionsWithActivity := make([]SessionWithActivity, 0, len(sessions))
	for _, s := range sessions {
		item := SessionWithActivity{SessionInfo: s}
		if a, ok := activityMap[s.ID]; ok {
			item.BytesPerSecond = a.BytesPerSecond
			item.IsActive = a.IsActive
			t := a.LastActivity
			item.LastActivity = &t
		}
		sessionsWithActivity = append(sessionsWithActivity, item)
	}
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]any{
		"sessions": sessionsWithActivity,
		"count":    len(sessionsWithActivity),
	})
}

type wsReader struct {
	conn    *gorillaws.Conn
	buf     []byte
	run     *runner.Runner
	wrapped *container.WrappedCommand
	logger  *slog.Logger
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
		case gorillaws.BinaryMessage:
			r.buf = data
		case gorillaws.TextMessage:
			var msg struct {
				Type string `json:"type"`
				Cols uint16 `json:"cols,omitempty"`
				Rows uint16 `json:"rows,omitempty"`
			}
			if json.Unmarshal(data, &msg) == nil && msg.Type == "resize" && r.run != nil {
				_ = r.run.Resize(msg.Cols, msg.Rows)
				if r.wrapped != nil {
					// Log container and host PIDs when forwarding SIGWINCH
					containerPID, hostPID := -1, -1
					if pid, err := r.wrapped.GetPID(); err == nil && pid > 0 {
						containerPID = pid
						if hp, herr := container.ResolvePID(pid); herr == nil && hp > 0 {
							hostPID = hp
						}
					}
					lg := r.logger
					if lg == nil {
						lg = slog.Default()
					}
					lg.Info("forwarding SIGWINCH to container process",
						"container_pid", containerPID,
						"host_pid", hostPID,
						"cols", msg.Cols,
						"rows", msg.Rows,
					)
					_ = r.wrapped.Signal(syscall.SIGWINCH)
				} else {
					// No container wrapper (tmux path) - signal the runner PID directly and log
					lg := r.logger
					if lg == nil {
						lg = slog.Default()
					}
					lg.Debug("forwarding SIGWINCH to tmux process",
						"pid", r.run.PID(),
						"cols", msg.Cols,
						"rows", msg.Rows,
					)
					_ = syscall.Kill(r.run.PID(), syscall.SIGWINCH)
				}
			}
		}
	}
}

type wsWriter struct {
	conn *gorillaws.Conn
	mu   sync.Mutex
}

func (w *wsWriter) Write(p []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()
	if err := w.conn.WriteMessage(gorillaws.BinaryMessage, p); err != nil {
		return 0, err
	}
	return len(p), nil
}
