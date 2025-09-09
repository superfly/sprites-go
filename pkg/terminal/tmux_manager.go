package terminal

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync/atomic"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// SessionInfo contains information about a tmux session
type SessionInfo struct {
	ID      string    `json:"id"`
	Name    string    `json:"name"`
	Created time.Time `json:"created"`
	Command string    `json:"command"`
}

// SessionActivity represents activity in tmux sessions
type SessionActivity struct {
	SessionID string
	Active    bool
	Type      string // "output", "window_activity", etc.
}

// SessionActivityInfo contains information about a session's activity
type SessionActivityInfo struct {
	SessionID      string
	Name           string
	LastActivity   time.Time
	BytesPerSecond float64
	IsActive       bool
}

// TMUXManager manages detachable tmux sessions for exec commands
type TMUXManager struct {
	logger         *slog.Logger
	nextID         int64
	activityChan   chan SessionActivity
	windowMonitor  *tmux.WindowMonitor
	prepareCommand func()
	cmdPrefix      []string // Prefix for server-side tmux commands (e.g., ["crun", "exec", "app"])

	// Channel-based synchronization for monitor startup
	monitorStartCh chan struct{}
}

// NewTMUXManager creates a new TMUXManager
func NewTMUXManager(ctx context.Context) *TMUXManager {
	tm := &TMUXManager{
		logger:         tap.Logger(ctx),
		nextID:         -1,
		activityChan:   make(chan SessionActivity, 100),
		monitorStartCh: make(chan struct{}, 1),
	}
	// Initialize nextID based on existing sessions
	tm.initializeNextID()

	// Start the monitor manager goroutine
	go tm.monitorManager(ctx)

	return tm
}

// monitorManager handles monitor startup requests serially
func (tm *TMUXManager) monitorManager(ctx context.Context) {
	for {
		select {
		case <-ctx.Done():
			return
		case <-tm.monitorStartCh:
			// Check if we need to start the monitor
			if tm.windowMonitor == nil && tm.prepareCommand != nil {
				if tm.logger != nil {
					tm.logger.Info("Starting tmux activity monitor")
				}
				tm.prepareCommand()
			}
		}
	}
}

// initializeNextID sets nextID based on existing tmux sessions
func (tm *TMUXManager) initializeNextID() {
	sessions, _ := tm.ListSessions()
	maxID := int64(-1)
	for _, session := range sessions {
		// Try to parse numeric session IDs
		if id, err := strconv.ParseInt(session, 10, 64); err == nil {
			if id > maxID {
				maxID = id
			}
		}
	}
	tm.nextID = maxID
	if tm.logger != nil {
		tm.logger.Debug("Initialized TMUXManager", "nextID", tm.nextID)
	}
}

// CreateSession creates a new tmux session with an auto-incrementing ID
func (tm *TMUXManager) CreateSession(cmd string, args []string, controlMode bool) (string, string, []string) {
	// Get current ID and increment for next time
	// We add 1 first, so if nextID is -1, we get 0 for the first session
	sessionID := fmt.Sprintf("%d", atomic.AddInt64(&tm.nextID, 1))

	if tm.logger != nil {
		tm.logger.Info("Creating new tmux session", "sessionID", sessionID, "cmd", cmd, "args", args)
	}

	// Return tmux new-session command with sprite-exec-<id> naming
	// Start attached so the user can interact immediately
	sessionName := fmt.Sprintf("sprite-exec-%s", sessionID)

	// Request activity monitor startup after first session creation
	select {
	case tm.monitorStartCh <- struct{}{}:
		// Request sent
	default:
		// Channel full, request already pending
	}

	// Build tmux args: tmux -f config -S socket new-session -s sessionName cmd args...
	tmuxArgs := []string{
		"-f", "/.sprite/bin/tmux.conf",
		"-S", "/.sprite/tmp/exec-tmux",
	}

	// Add control mode if requested
	if controlMode {
		tmuxArgs = append(tmuxArgs, "-CC")
	}

	tmuxArgs = append(tmuxArgs,
		"new-session",
		"-s", sessionName,
		cmd,
	)
	tmuxArgs = append(tmuxArgs, args...)

	return sessionID, "/.sprite/bin/tmux", tmuxArgs
}

// AttachSession attaches to an existing tmux session
func (tm *TMUXManager) AttachSession(id string, controlMode bool) (string, []string) {
	sessionName := fmt.Sprintf("sprite-exec-%s", id)

	if tm.logger != nil {
		tm.logger.Info("Attaching to existing tmux session",
			"sessionID", id,
			"sessionName", sessionName,
			"socket", "/.sprite/tmp/exec-tmux")
	}

	// Request activity monitor startup (in case first interaction is attach)
	select {
	case tm.monitorStartCh <- struct{}{}:
		// Request sent
	default:
		// Channel full, request already pending
	}

	// Return tmux attach command - using sprite-exec-<id> naming
	tmuxArgs := []string{
		"-f", "/.sprite/bin/tmux.conf",
		"-S", "/.sprite/tmp/exec-tmux",
	}

	// Add control mode if requested
	if controlMode {
		tmuxArgs = append(tmuxArgs, "-CC")
	}

	tmuxArgs = append(tmuxArgs,
		"attach-session",
		"-t", sessionName,
	)

	return "/.sprite/bin/tmux", tmuxArgs
}

// SessionExists checks if a tmux session with the given ID exists
func (tm *TMUXManager) SessionExists(id string) bool {
	// Check if tmux session exists by running tmux has-session with sprite-exec-<id> naming
	sessionName := fmt.Sprintf("sprite-exec-%s", id)
	tmuxArgs := []string{"-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux", "has-session", "-t", sessionName}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command("/.sprite/bin/tmux", tmuxArgs...)
	}
	err := cmd.Run()

	return err == nil
}

// KillSession forcefully kills a tmux session
func (tm *TMUXManager) KillSession(id string) error {
	if tm.logger != nil {
		tm.logger.Info("Killing tmux session", "sessionID", id)
	}

	// Send kill-session command to tmux with sprite-exec-<id> naming
	sessionName := fmt.Sprintf("sprite-exec-%s", id)
	tmuxArgs := []string{"-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux", "kill-session", "-t", sessionName}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command("/.sprite/bin/tmux", tmuxArgs...)
	}
	return cmd.Run()
}

// ListSessions returns a list of all tmux sessions (sprite-exec-<id> names only)
func (tm *TMUXManager) ListSessions() ([]string, error) {
	// List all tmux sessions
	tmuxArgs := []string{"-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux", "list-sessions", "-F", "#{session_name}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command("/.sprite/bin/tmux", tmuxArgs...)
	}

	output, err := cmd.Output()
	if err != nil {
		// If tmux server is not running, there are no sessions
		return []string{}, nil
	}

	var sessions []string
	lines := strings.Split(string(output), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line != "" {
			// Only include sprite-exec-<id> sessions
			// This filters out any other tmux sessions
			if strings.HasPrefix(line, "sprite-exec-") {
				// Extract just the ID part for backward compatibility
				id := strings.TrimPrefix(line, "sprite-exec-")
				sessions = append(sessions, id)
			}
		}
	}

	return sessions, nil
}

// ListSessionsWithInfo returns detailed information about all tmux sessions
func (tm *TMUXManager) ListSessionsWithInfo() ([]SessionInfo, error) {
	// List all tmux sessions with detailed format
	// Format: session_name:created_time:session_windows
	tmuxArgs := []string{"-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux",
		"list-sessions", "-F",
		"#{session_name}|#{session_created}|#{session_windows}|#{pane_current_command}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command("/.sprite/bin/tmux", tmuxArgs...)
	}

	output, err := cmd.Output()
	if err != nil {
		// If tmux server is not running, there are no sessions
		return []SessionInfo{}, nil
	}

	var sessions []SessionInfo
	lines := strings.Split(string(output), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line != "" && strings.HasPrefix(line, "sprite-exec-") {
			parts := strings.Split(line, "|")
			if len(parts) >= 2 {
				sessionName := parts[0]
				id := strings.TrimPrefix(sessionName, "sprite-exec-")

				// Parse creation time (Unix timestamp)
				var created time.Time
				if createdUnix, err := strconv.ParseInt(parts[1], 10, 64); err == nil {
					created = time.Unix(createdUnix, 0)
				}

				// Get the command - we'll need to query each session individually for this
				command := tm.getSessionCommand(sessionName)

				sessions = append(sessions, SessionInfo{
					ID:      id,
					Name:    sessionName,
					Created: created,
					Command: command,
				})
			}
		}
	}

	return sessions, nil
}

// getSessionCommand gets the command running in a tmux session
func (tm *TMUXManager) getSessionCommand(sessionName string) string {
	// Get the command from the first pane of the session
	tmuxArgs := []string{"-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux",
		"list-panes", "-t", sessionName, "-F", "#{pane_current_command}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command("/.sprite/bin/tmux", tmuxArgs...)
	}

	output, err := cmd.Output()
	if err != nil {
		return "unknown"
	}

	lines := strings.Split(string(output), "\n")
	if len(lines) > 0 {
		command := strings.TrimSpace(lines[0])
		if command != "" {
			return command
		}
	}
	return "unknown"
}

// SetPrepareCommand sets the callback function to run when the manager is initialized
// The callback will be executed when StartActivityMonitor is called
func (tm *TMUXManager) SetPrepareCommand(fn func()) {
	tm.prepareCommand = fn
	if tm.logger != nil {
		tm.logger.Info("TMUXManager prepare command has been set")
	}
	// Note: We no longer run it immediately - it will be called when needed
}

// SetCmdPrefix sets the command prefix for server-side tmux commands
func (tm *TMUXManager) SetCmdPrefix(prefix []string) {
	tm.cmdPrefix = prefix
	if tm.logger != nil {
		tm.logger.Info("TMUXManager command prefix has been set", "prefix", prefix)
	}
}

// GetActivityChannel returns the activity channel for monitoring
func (tm *TMUXManager) GetActivityChannel() <-chan SessionActivity {
	return tm.activityChan
}

// HasActiveSessions checks if there are any tmux sessions with recent activity
func (tm *TMUXManager) HasActiveSessions() bool {
	return len(tm.GetActiveSessionsInfo()) > 0
}

// GetActiveSessionsInfo returns information about sessions that have recent activity
func (tm *TMUXManager) GetActiveSessionsInfo() []SessionActivityInfo {
	sessions, err := tm.ListSessionsWithInfo()
	if err != nil {
		return []SessionActivityInfo{}
	}

	// Get activity stats from window monitor if available
	var activityStats map[string]*tmux.ActivityStats
	if tm.windowMonitor != nil {
		activityStats = tm.windowMonitor.GetActivityStats()
	} else {
		activityStats = make(map[string]*tmux.ActivityStats)
	}

	var result []SessionActivityInfo
	now := time.Now()

	for _, session := range sessions {
		// Check if we have activity stats for this session
		stats, hasActivity := activityStats[session.ID]
		if !hasActivity {
			continue
		}

		// Check if activity is recent (within last 5 minutes)
		activityAge := now.Sub(stats.LastActivity)
		if activityAge > 5*time.Minute {
			continue
		}

		info := SessionActivityInfo{
			SessionID:    session.ID,
			Name:         session.Name,
			IsActive:     true,
			LastActivity: stats.LastActivity,
		}

		// Calculate bytes per second
		duration := now.Sub(stats.StartTime).Seconds()
		if duration > 0 {
			info.BytesPerSecond = float64(stats.ByteCount) / duration
		}

		result = append(result, info)
	}

	return result
}

// StartActivityMonitor starts monitoring tmux sessions for activity
func (tm *TMUXManager) StartActivityMonitor(ctx context.Context) error {
	// First check if receiver is nil
	if tm == nil {
		return fmt.Errorf("TMUXManager is nil")
	}

	// Ensure we have a logger - try from context first
	if tm.logger == nil {
		tm.logger = tap.Logger(ctx)
		if tm.logger == nil {
			tm.logger = slog.Default()
			tm.logger.Warn("TMUXManager logger was nil, using default logger")
		}
	}

	tm.logger.Info("StartActivityMonitor called")

	// Check if monitor is already running
	if tm.windowMonitor != nil {
		tm.logger.Debug("Window monitor already running, returning early")
		return nil
	}

	// Check if socket directory exists - might not exist in test environments
	socketDir := "/.sprite/tmp"
	if _, err := os.Stat(socketDir); os.IsNotExist(err) {
		tm.logger.Warn("Socket directory does not exist, skipping tmux activity monitor",
			"socketDir", socketDir,
			"info", "This is expected in test environments")
		return nil
	}

	// Create window monitor
	tm.logger.Debug("Creating new window monitor",
		"monitorSession", "sprite-monitor",
		"socketPath", "/.sprite/tmp/exec-tmux",
		"configPath", "/.sprite/bin/tmux.conf",
		"cmdPrefix", tm.cmdPrefix)
	tm.windowMonitor = tmux.NewWindowMonitor(ctx, "sprite-monitor").
		WithSocketPath("/.sprite/tmp/exec-tmux").
		WithConfigPath("/.sprite/bin/tmux.conf").
		WithCmdPrefix(tm.cmdPrefix)

	// Start the window monitor
	tm.logger.Debug("About to call windowMonitor.Start()")
	if err := tm.windowMonitor.Start(ctx); err != nil {
		tm.logger.Error("Failed to start tmux window monitor",
			"error", err,
			"session", "sprite-monitor")
		tm.windowMonitor = nil // Reset on failure
		return fmt.Errorf("failed to start window monitor: %w", err)
	}

	// Start processing window monitor events
	go tm.processWindowMonitorEvents(ctx)

	tm.logger.Info("Started tmux activity monitor")
	return nil
}

// processWindowMonitorEvents forwards activity state changes from window monitor
func (tm *TMUXManager) processWindowMonitorEvents(ctx context.Context) {
	tm.logger.Debug("Starting window monitor event processor")

	if tm.windowMonitor == nil {
		tm.logger.Error("Window monitor is nil")
		return
	}

	eventChan := tm.windowMonitor.GetEventChannel()

	for {
		select {
		case <-ctx.Done():
			tm.logger.Debug("Window monitor event processor stopped due to context cancellation")
			return
		case event, ok := <-eventChan:
			if !ok {
				tm.logger.Error("Window monitor event channel closed")
				return
			}

			// Extract session ID from original session format (e.g., "$1" -> "1")
			sessionID := strings.TrimPrefix(event.OriginalSession, "$")
			if sessionID == "" || !strings.HasPrefix(event.OriginalSession, "$") {
				continue
			}

			switch event.EventType {
			case "active":
				// Session became active
				tm.logger.Debug("Session became active", "sessionID", sessionID)
				select {
				case tm.activityChan <- SessionActivity{
					SessionID: sessionID,
					Active:    true,
					Type:      "window_activity",
				}:
				default:
					tm.logger.Debug("Activity channel full, dropping event")
				}

			case "inactive":
				// Session became inactive
				tm.logger.Debug("Session became inactive", "sessionID", sessionID)
				select {
				case tm.activityChan <- SessionActivity{
					SessionID: sessionID,
					Active:    false,
					Type:      "window_idle",
				}:
				default:
					tm.logger.Debug("Activity channel full, dropping event")
				}

			case "closed":
				// Session/window closed
				tm.logger.Debug("Session ended", "sessionID", sessionID)
				select {
				case tm.activityChan <- SessionActivity{
					SessionID: sessionID,
					Active:    false,
					Type:      "session_end",
				}:
				default:
					tm.logger.Debug("Activity channel full, dropping event")
				}
			}
		}
	}
}
