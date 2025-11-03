package tmux

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/superfly/sprite-env/pkg/container"
	"github.com/superfly/sprite-env/pkg/tap"
)

// SessionInfo mirrors api-facing session info from the legacy terminal manager
type SessionInfo struct {
	ID      string    `json:"id"`
	Name    string    `json:"name"`
	Created time.Time `json:"created"`
	Command string    `json:"command"`
}

// SessionActivityInfo mirrors activity info shape used by handlers
type SessionActivityInfo struct {
	SessionID      string
	Name           string
	LastActivity   time.Time
	BytesPerSecond float64
	IsActive       bool
}

// PaneLifecycleCallback is invoked when panes are added/removed
type PaneLifecycleCallback func(sessionID string, panePID int, added bool)

type Options struct {
	TmuxBinary    string
	SocketPath    string
	ConfigPath    string
	SessionPrefix string
	// WrapCmd is an optional function to wrap commands (e.g., container exec)
	WrapCmd func(*exec.Cmd) *exec.Cmd
	Logger  *slog.Logger
	// EventCallback, if set, will be invoked for each WindowMonitorEvent emitted
	// by the internal WindowMonitor. Only a single callback is supported.
	EventCallback func(WindowMonitorEvent)
}

// Manager provides a configurable tmux session manager
type Manager struct {
	logger         *slog.Logger
	nextID         int64
	socketPath     string
	configPath     string
	tmuxBinary     string
	sessionPrefix  string
	wrapCmd        func(*exec.Cmd) *exec.Cmd
	monitorStartCh chan struct{}

	windowMonitor *WindowMonitor

	paneCallbacks   map[string]PaneLifecycleCallback
	paneCallbacksMu sync.RWMutex

	// removed state for wrapped metadata; API layer handles wrappers

	// Optional single subscriber for window events
	eventCallback func(WindowMonitorEvent)
}

func NewManager(ctx context.Context, opts Options) *Manager {
	logger := opts.Logger
	if logger == nil {
		// Use the context logger if available; do not force debug level
		logger = tap.Logger(ctx)
	}
	if logger != nil {
		// Ensure component tag when a logger is present
		logger = logger.With("component", "tmx_manager")
	}

	m := &Manager{
		logger:         logger,
		nextID:         -1,
		socketPath:     coalesce(opts.SocketPath, "/.sprite/tmp/mux"),
		configPath:     coalesce(opts.ConfigPath, "/.sprite/etc/tmux.conf"),
		tmuxBinary:     coalesce(opts.TmuxBinary, "/.sprite/bin/tmux"),
		sessionPrefix:  coalesce(opts.SessionPrefix, "sprite"),
		wrapCmd:        opts.WrapCmd,
		monitorStartCh: make(chan struct{}, 1),
		paneCallbacks:  make(map[string]PaneLifecycleCallback),
		eventCallback:  opts.EventCallback,
	}

	m.initializeNextID()
	go m.monitorManager(ctx)
	go m.paneMonitor(ctx)
	// Start persistent window events pump to ensure callbacks are never lost
	if m.eventCallback != nil {
		go m.windowEventsPump(ctx)
	}

	return m
}

func coalesce(values ...string) string {
	for _, v := range values {
		if v != "" {
			return v
		}
	}
	return ""
}

func (m *Manager) monitorManager(ctx context.Context) {
	for {
		select {
		case <-ctx.Done():
			if m.logger != nil {
				m.logger.Debug("monitorManager: context done")
			}
			return
		case <-m.monitorStartCh:
			if m.windowMonitor == nil {
				// Start the window monitor lazily
				if m.logger != nil {
					m.logger.Debug("monitorManager: starting window monitor",
						"socketPath", m.socketPath,
						"configPath", m.configPath,
						"tmuxBinary", m.tmuxBinary)
				}
				baseCmd := exec.Command(m.tmuxBinary)
				mon := NewWindowMonitor(ctx, m.monitorSessionName()).
					WithSocketPath(m.socketPath).
					WithConfigPath(m.configPath).
					WithCommand(baseCmd).
					WithWrap(m.wrapCmd)
				m.windowMonitor = mon
				if err := m.windowMonitor.Start(ctx); err != nil {
					if m.logger != nil {
						m.logger.Error("monitorManager: window monitor failed to start", "error", err)
					}
				} else if m.logger != nil {
					m.logger.Debug("monitorManager: window monitor started")
				}

				// Event pump runs persistently via windowEventsPump()
			}
		}
	}
}

// windowEventsPump persistently attaches to the window monitor events channel
// and forwards events to the configured eventCallback, reattaching if the
// monitor restarts or its channel closes.
func (m *Manager) windowEventsPump(ctx context.Context) {
	for {
		if ctx.Err() != nil {
			return
		}
		if m.eventCallback == nil {
			time.Sleep(200 * time.Millisecond)
			continue
		}
		if m.windowMonitor == nil {
			time.Sleep(200 * time.Millisecond)
			continue
		}
		ch := m.windowMonitor.GetEventChannel()
		if ch == nil {
			time.Sleep(200 * time.Millisecond)
			continue
		}
		// Range until channel closes, then loop to reattach
		for ev := range ch {
			e := ev
			go func() {
				defer func() {
					if r := recover(); r != nil && m.logger != nil {
						m.logger.Warn("window event callback panicked", "panic", r)
					}
				}()
				m.eventCallback(e)
			}()
		}
		// Channel closed; reattach on next iteration
	}
}

func (m *Manager) monitorSessionName() string {
	return fmt.Sprintf("%s-monitor", m.sessionPrefix)
}

func (m *Manager) initializeNextID() {
	sessions, _ := m.ListSessions()
	maxID := int64(-1)
	for _, s := range sessions {
		if id, err := strconv.ParseInt(s, 10, 64); err == nil && id > maxID {
			maxID = id
		}
	}
	m.nextID = maxID
	if m.logger != nil {
		m.logger.Debug("initializeNextID", "nextID", m.nextID)
	}
}

func (m *Manager) GenerateSessionID() string {
	return fmt.Sprintf("%d", atomic.AddInt64(&m.nextID, 1))
}

// NewSessionCmd builds a tmux command that creates a new session and runs base.
// It generates a new session ID and returns the command and the ID.
func (m *Manager) NewSessionCmd(base *exec.Cmd, controlMode bool) (*exec.Cmd, string) {
	cmd, _, id := m.NewSession(base, controlMode)
	return cmd, id
}

// AttachCmd builds a tmux command that attaches to an existing session
func (m *Manager) AttachCmd(sessionID string, controlMode bool) *exec.Cmd {
	cmd, _ := m.Attach(sessionID, controlMode)
	return cmd
}

func (m *Manager) sessionName(id string) string {
	return fmt.Sprintf("%s-exec-%s", m.sessionPrefix, id)
}

// WrappedForSession returns the container WrappedCommand associated with a session, if any.
// WrappedForSession removed

func (m *Manager) buildTmuxCommand(tmuxArgs []string) *exec.Cmd {
	tmuxBinary := m.tmuxBinary
	if m.logger != nil {
		m.logger.Debug("buildTmuxCommand: constructing command", "tmuxBinary", tmuxBinary, "args", tmuxArgs)
	}
	cmd := exec.Command(tmuxBinary, tmuxArgs...)
	if strings.HasPrefix(tmuxBinary, "./") || strings.HasPrefix(tmuxBinary, "../") {
		cmd.Dir = "/.sprite/bin/"
	}
	// Ensure TERM only; avoid inheriting host environment
	cmd.Env = ensureDefaultEnv([]string{})
	// If a wrapper is configured (container exec), wrap the command now (for non-exec utility paths)
	if m.wrapCmd != nil {
		if wrapped := m.wrapCmd(cmd); wrapped != nil {
			if m.logger != nil {
				m.logger.Debug("buildTmuxCommand: wrapped tmux command for container",
					"fullCommand", wrapped.String(),
					"path", wrapped.Path,
					"args", wrapped.Args)
			}
			return wrapped
		}
		if m.logger != nil {
			m.logger.Error("buildTmuxCommand: wrapCmd returned nil; panicking")
		}
		panic("tmux manager: wrapCmd returned nil for tmux command")
	}
	return cmd
}

// NewSession builds a tmux command that creates a new session and runs base, returning
// the command to execute, a nil container wrapper (tmux is never wrapped here), and the new session ID.
func (m *Manager) NewSession(base *exec.Cmd, controlMode bool) (*exec.Cmd, *container.WrappedCommand, string) {
	// Request monitor startup after first session creation
	select {
	case m.monitorStartCh <- struct{}{}:
	default:
	}

	sessionID := m.GenerateSessionID()
	tmuxArgs := []string{"-f", m.configPath, "-S", m.socketPath}
	if controlMode {
		tmuxArgs = append(tmuxArgs, "-CC")
	}
	sessionName := m.sessionName(sessionID)
	// Create a wrapper script to set env/dir then exec the original command
	scriptPath := fmt.Sprintf("/.sprite/tmp/exec-%s", sessionID)
	if err := generateTmuxWrapperScript(scriptPath, base); err != nil {
		if m.logger != nil {
			m.logger.Warn("NewSession: wrapper script generation failed, falling back", "error", err)
		}
		// Fallback: direct command
		tmuxArgs = append(tmuxArgs, "new", "-s", sessionName, base.Path)
		if len(base.Args) > 1 {
			tmuxArgs = append(tmuxArgs, base.Args[1:]...)
		}
	} else {
		// Use script path directly
		tmuxArgs = append(tmuxArgs, "new", "-s", sessionName, scriptPath)
	}
	if m.logger != nil {
		m.logger.Debug("NewSession: building tmux new-session",
			"sessionID", sessionID,
			"sessionName", sessionName,
			"args", tmuxArgs,
			"dir", base.Dir)
	}
	// Build RAW tmux command (do not use buildTmuxCommand to avoid double-wrapping for exec flows)
	tmuxBinary := m.tmuxBinary
	cmd := exec.Command(tmuxBinary, tmuxArgs...)
	if strings.HasPrefix(tmuxBinary, "./") || strings.HasPrefix(tmuxBinary, "../") {
		cmd.Dir = "/.sprite/bin/"
	}
	// Minimal env for tmux process (avoid leaking host env)
	// User command env is exported by the wrapper script from base.Env
	cmd.Env = ensureDefaultEnv([]string{})
	cmd.Stdin = base.Stdin
	cmd.Stdout = base.Stdout
	cmd.Stderr = base.Stderr
	cmd.Dir = base.Dir
	if m.logger != nil {
		m.logger.Debug("NewSession: command built", "path", cmd.Path, "args", cmd.Args)
	}
	// For exec flows, if a wrapper is configured, wrap here and return the handle
	if m.wrapCmd != nil {
		wc := container.Wrap(cmd, "app", container.WithTTY(false))
		return wc.Cmd, wc, sessionID
	}
	return cmd, nil, sessionID
}

// Attach builds a tmux command that attaches to an existing session, returning
// the command to execute and a nil container wrapper (tmux is never wrapped here).
func (m *Manager) Attach(sessionID string, controlMode bool) (*exec.Cmd, *container.WrappedCommand) {
	// Request monitor startup (attach may be first interaction)
	select {
	case m.monitorStartCh <- struct{}{}:
	default:
	}

	tmuxArgs := []string{"-f", m.configPath, "-S", m.socketPath}
	if controlMode {
		tmuxArgs = append(tmuxArgs, "-CC")
	}
	sessionName := m.sessionName(sessionID)
	tmuxArgs = append(tmuxArgs, "attach", "-t", sessionName)
	if m.logger != nil {
		m.logger.Debug("Attach: building tmux attach",
			"sessionID", sessionID,
			"sessionName", sessionName,
			"args", tmuxArgs)
	}
	// Build RAW tmux command (avoid buildTmuxCommand here to prevent double wrap)
	tmuxBinary := m.tmuxBinary
	cmd := exec.Command(tmuxBinary, tmuxArgs...)
	if strings.HasPrefix(tmuxBinary, "./") || strings.HasPrefix(tmuxBinary, "../") {
		cmd.Dir = "/.sprite/bin/"
	}
	cmd.Env = ensureDefaultEnv([]string{})
	if m.logger != nil {
		m.logger.Debug("Attach: command built", "path", cmd.Path, "args", cmd.Args)
	}
	if m.wrapCmd != nil {
		wc := container.Wrap(cmd, "app", container.WithTTY(false))
		return wc.Cmd, wc
	}
	return cmd, nil
}

// ensureDefaultEnv adds sane defaults (TERM) if not present
func ensureDefaultEnv(env []string) []string {
	hasTERM := false
	for _, e := range env {
		if strings.HasPrefix(e, "TERM=") {
			hasTERM = true
			break
		}
	}
	if !hasTERM {
		env = append(env, "TERM=xterm-256color")
	}
	return env
}

// generateTmuxWrapperScript writes a script that prepares env and dir, then execs base
func generateTmuxWrapperScript(scriptPath string, base *exec.Cmd) error {
	dir := filepath.Dir(scriptPath)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return fmt.Errorf("failed to create directory %s: %w", dir, err)
	}

	var b strings.Builder
	b.WriteString("#!/usr/bin/env bash\n")
	b.WriteString("set -euo pipefail\n\n")
	b.WriteString("# Unset TMUX-related env vars\n")
	b.WriteString("for var in $(env | grep '^TMUX' | cut -d= -f1); do unset \"$var\"; done\n\n")

	env := ensureDefaultEnv(base.Env)
	if len(env) > 0 {
		b.WriteString("# Export environment\n")
		for _, e := range env {
			parts := strings.SplitN(e, "=", 2)
			if len(parts) == 2 {
				b.WriteString(fmt.Sprintf("export %s=%s\n", parts[0], shellQuote(parts[1])))
			}
		}
		b.WriteString("\n")
	}

	// Removed PATH modification step per new process.json flow

	if base.Dir != "" {
		b.WriteString("cd " + shellQuote(base.Dir) + "\n")
	} else {
		b.WriteString("cd /home/sprite\n")
	}

	b.WriteString("exec ")
	b.WriteString(shellQuote(base.Path))
	for _, a := range base.Args[1:] {
		b.WriteString(" ")
		b.WriteString(shellQuote(a))
	}
	b.WriteString("\n")

	if err := os.WriteFile(scriptPath, []byte(b.String()), 0755); err != nil {
		return fmt.Errorf("failed to write script %s: %w", scriptPath, err)
	}
	return nil
}

// shellQuote single-quote escapes shell strings
func shellQuote(s string) string {
	if s == "" {
		return "''"
	}
	if !strings.ContainsAny(s, "' \t\n$`\\\"!*?[](){};<>|&~") {
		return s
	}
	return "'" + strings.ReplaceAll(s, "'", "'\\''") + "'"
}

// SessionExists checks for a session
func (m *Manager) SessionExists(id string) bool {
	name := m.sessionName(id)
	args := []string{"-f", m.configPath, "-S", m.socketPath, "has-session", "-t", name}
	return m.buildTmuxCommand(args).Run() == nil
}

// KillSession kills a tmux session
func (m *Manager) KillSession(id string) error {
	name := m.sessionName(id)
	args := []string{"-f", m.configPath, "-S", m.socketPath, "kill-session", "-t", name}
	return m.buildTmuxCommand(args).Run()
}

// ListSessions returns session IDs (strings)
func (m *Manager) ListSessions() ([]string, error) {
	args := []string{"-f", m.configPath, "-S", m.socketPath, "list-sessions", "-F", "#{session_name}"}
	out, err := m.buildTmuxCommand(args).Output()
	if err != nil {
		return []string{}, nil
	}
	var result []string
	for _, line := range strings.Split(strings.TrimSpace(string(out)), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		prefix := m.sessionPrefix + "-exec-"
		if strings.HasPrefix(line, prefix) {
			result = append(result, strings.TrimPrefix(line, prefix))
		}
	}
	return result, nil
}

// ListSessionsWithInfo returns detailed info
func (m *Manager) ListSessionsWithInfo() ([]SessionInfo, error) {
	args := []string{"-f", m.configPath, "-S", m.socketPath,
		"list-sessions", "-F", "#{session_name}|#{session_created}|#{session_windows}|#{pane_current_command}"}
	out, err := m.buildTmuxCommand(args).Output()
	if err != nil {
		return []SessionInfo{}, nil
	}
	sessPrefix := m.sessionPrefix + "-exec-"
	var sessions []SessionInfo
	lines := strings.Split(string(out), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" || !strings.HasPrefix(line, sessPrefix) {
			continue
		}
		parts := strings.Split(line, "|")
		if len(parts) < 2 {
			continue
		}
		sessionName := parts[0]
		id := strings.TrimPrefix(sessionName, sessPrefix)
		var created time.Time
		if ts, err := strconv.ParseInt(parts[1], 10, 64); err == nil {
			created = time.Unix(ts, 0)
		}
		cmd := m.getSessionCommand(sessionName)
		sessions = append(sessions, SessionInfo{ID: id, Name: sessionName, Created: created, Command: cmd})
	}
	return sessions, nil
}

func (m *Manager) getSessionCommand(sessionName string) string {
	args := []string{"-f", m.configPath, "-S", m.socketPath, "list-panes", "-t", sessionName, "-F", "#{pane_current_command}"}
	out, err := m.buildTmuxCommand(args).Output()
	if err != nil {
		return "unknown"
	}
	lines := strings.Split(string(out), "\n")
	if len(lines) > 0 {
		s := strings.TrimSpace(lines[0])
		if s != "" {
			return s
		}
	}
	return "unknown"
}

// GetSessionPanePIDs returns host PIDs for panes in a session
func (m *Manager) GetSessionPanePIDs(id string) ([]int, error) {
	if strings.TrimSpace(id) == "" {
		return nil, fmt.Errorf("empty session id")
	}
	name := m.sessionName(id)
	args := []string{"-f", m.configPath, "-S", m.socketPath, "list-panes", "-t", name, "-F", "#{pane_pid}"}
	out, err := m.buildTmuxCommand(args).Output()
	if err != nil {
		return nil, fmt.Errorf("failed to get pane PIDs: %w", err)
	}
	var pids []int
	for _, line := range strings.Split(string(out), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if cpid, err := strconv.Atoi(line); err == nil && cpid > 0 {
			// Best-effort: resolve to host PID; if it fails, skip
			if host, err := container.ResolvePID(cpid); err == nil && host > 0 {
				pids = append(pids, host)
			}
		}
	}
	return pids, nil
}

// Activity aggregation
func (m *Manager) GetAllSessionActivityInfo() map[string]*SessionActivityInfo {
	stats := make(map[string]*ActivityStats)
	if m.windowMonitor != nil {
		stats = m.windowMonitor.GetActivityStats()
	}
	mapping := m.getSessionIDMapping()
	// reverse mapping
	reverse := make(map[string]string)
	for tmuxID, userID := range mapping {
		reverse[userID] = tmuxID
	}
	result := make(map[string]*SessionActivityInfo)
	for userID, tmuxID := range reverse {
		if s, ok := stats[tmuxID]; ok {
			result[userID] = &SessionActivityInfo{
				SessionID:      userID,
				Name:           m.sessionName(userID),
				LastActivity:   s.LastActivity,
				BytesPerSecond: s.RecentDataRate,
				IsActive:       s.IsActive,
			}
		}
	}
	return result
}

func (m *Manager) getSessionIDMapping() map[string]string {
	args := []string{"-f", m.configPath, "-S", m.socketPath, "list-sessions", "-F", "#{session_id}:#{session_name}"}
	out, err := m.buildTmuxCommand(args).Output()
	if err != nil {
		return map[string]string{}
	}
	mapping := make(map[string]string)
	sessPrefix := m.sessionPrefix + "-exec-"
	lines := strings.Split(string(out), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		parts := strings.Split(line, ":")
		if len(parts) < 2 {
			continue
		}
		tmuxID := strings.TrimPrefix(parts[0], "$")
		name := parts[1]
		if strings.HasPrefix(name, sessPrefix) {
			userID := strings.TrimPrefix(name, sessPrefix)
			mapping[tmuxID] = userID
		}
	}
	return mapping
}

// SetPaneCallback registers a callback for pane lifecycle events for a session
func (m *Manager) SetPaneCallback(sessionID string, cb PaneLifecycleCallback) {
	m.paneCallbacksMu.Lock()
	m.paneCallbacks[sessionID] = cb
	m.paneCallbacksMu.Unlock()
}

// RemovePaneCallback removes the callback for a session
func (m *Manager) RemovePaneCallback(sessionID string) {
	m.paneCallbacksMu.Lock()
	delete(m.paneCallbacks, sessionID)
	m.paneCallbacksMu.Unlock()
}

// paneMonitor is a lightweight polling loop wiring pane callbacks via GetSessionPanePIDs
func (m *Manager) paneMonitor(ctx context.Context) {
	known := make(map[string]map[int]bool)
	ticker := time.NewTicker(2 * time.Second)
	defer ticker.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			m.paneCallbacksMu.RLock()
			cbs := make(map[string]PaneLifecycleCallback)
			for id, cb := range m.paneCallbacks {
				cbs[id] = cb
			}
			m.paneCallbacksMu.RUnlock()
			for id, cb := range cbs {
				pids, err := m.GetSessionPanePIDs(id)
				if err != nil {
					if prev, ok := known[id]; ok {
						for pid := range prev {
							cb(id, pid, false)
						}
						delete(known, id)
					}
					continue
				}
				cur := make(map[int]bool)
				for _, pid := range pids {
					cur[pid] = true
				}
				prev := known[id]
				if prev == nil {
					prev = make(map[int]bool)
					known[id] = prev
				}
				for pid := range cur {
					if !prev[pid] {
						cb(id, pid, true)
						prev[pid] = true
					}
				}
				for pid := range prev {
					if !cur[pid] {
						cb(id, pid, false)
						delete(prev, pid)
					}
				}
			}
		}
	}
}

// GetWindowMonitorEvents returns the event channel from the window monitor
// Returns nil if the window monitor is not started
func (m *Manager) GetWindowMonitorEvents() <-chan WindowMonitorEvent {
	if m.windowMonitor == nil {
		return nil
	}
	return m.windowMonitor.GetEventChannel()
}

// SetWrapCmd sets the command wrapper function
func (m *Manager) SetWrapCmd(wrap func(*exec.Cmd) *exec.Cmd) { m.wrapCmd = wrap }
