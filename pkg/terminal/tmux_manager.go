//go:build !clientonly
// +build !clientonly

package terminal

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/superfly/sprite-env/pkg/container"
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

// PaneLifecycleCallback is called when panes are added or removed
type PaneLifecycleCallback func(sessionID string, panePID int, added bool)

// TMUXManager manages detachable tmux sessions for exec commands
type TMUXManager struct {
	logger         *slog.Logger
	nextID         int64
	activityChan   chan SessionActivity
	windowMonitor  *tmux.WindowMonitor
	prepareCommand func()
	cmdPrefix      []string // Prefix for server-side tmux commands (e.g., ["crun", "exec", "app"])
	socketPath     string   // Path to tmux socket
	configPath     string   // Path to tmux config

	// Channel-based synchronization for monitor startup
	monitorStartCh chan struct{}

	// Pane lifecycle callbacks - map of sessionID to callback
	paneCallbacks   map[string]PaneLifecycleCallback
	paneCallbacksMu sync.RWMutex // Protects paneCallbacks
}

// NewTMUXManager creates a new TMUXManager
func NewTMUXManager(ctx context.Context) *TMUXManager {
	logger := tap.Logger(ctx)
	if logger == nil {
		logger = slog.Default()
	}
	// Force debug logging for tmux manager
	logger = logger.With("component", "tmux_manager")

	tm := &TMUXManager{
		logger:         logger,
		nextID:         -1,
		socketPath:     "/.sprite/tmp/exec-tmux",
		configPath:     "/.sprite/etc/tmux.conf",
		activityChan:   make(chan SessionActivity, 100),
		monitorStartCh: make(chan struct{}, 1),
		paneCallbacks:  make(map[string]PaneLifecycleCallback),
	}

	tm.logger.Debug("TMUXManager created")

	// Initialize nextID based on existing sessions
	tm.initializeNextID()

	// Start the monitor manager goroutine
	go tm.monitorManager(ctx)

	// Start the pane monitor goroutine
	go tm.paneMonitor(ctx)

	return tm
}

// WithSocketPath sets the tmux socket path
func (tm *TMUXManager) WithSocketPath(path string) *TMUXManager {
	tm.socketPath = path
	return tm
}

// WithConfigPath sets the tmux config path
func (tm *TMUXManager) WithConfigPath(path string) *TMUXManager {
	tm.configPath = path
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
		"-f", tm.configPath,
		"-S", tm.socketPath,
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
			"socket", tm.socketPath)
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
		"-f", tm.configPath,
		"-S", tm.socketPath,
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
	tmuxArgs := []string{"-f", tm.configPath, "-S", tm.socketPath, "has-session", "-t", sessionName}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
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
	tmuxArgs := []string{"-f", tm.configPath, "-S", tm.socketPath, "kill-session", "-t", sessionName}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
	}
	return cmd.Run()
}

// ListSessions returns a list of all tmux sessions (sprite-exec-<id> names only)
func (tm *TMUXManager) ListSessions() ([]string, error) {
	// List all tmux sessions
	tmuxArgs := []string{"-f", tm.configPath, "-S", tm.socketPath, "list-sessions", "-F", "#{session_name}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
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
	tmuxArgs := []string{"-f", tm.configPath, "-S", tm.socketPath,
		"list-sessions", "-F",
		"#{session_name}|#{session_created}|#{session_windows}|#{pane_current_command}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
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

// GetSessionPanePIDs returns all pane PIDs for a given session ID
func (tm *TMUXManager) GetSessionPanePIDs(id string) ([]int, error) {
	sessionName := fmt.Sprintf("sprite-exec-%s", id)

	// List all panes in the session with their PIDs
	// Format: #{pane_pid}
	tmuxArgs := []string{
		"-f", tm.configPath,
		"-S", tm.socketPath,
		"list-panes",
		"-t", sessionName,
		"-F", "#{pane_pid}",
	}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
	}

	output, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("failed to get pane PIDs: %w", err)
	}

	var pids []int
	lines := strings.Split(string(output), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line != "" {
			if containerPID, err := strconv.Atoi(line); err == nil && containerPID > 0 {
				// Convert container namespace PID to host PID
				hostPID, err := container.ResolvePID(containerPID)
				if err != nil {
					if tm.logger != nil {
						tm.logger.Warn("Failed to resolve container PID to host PID",
							"containerPID", containerPID, "error", err)
					}
					// Skip PIDs we can't resolve
					continue
				}
				pids = append(pids, hostPID)
			}
		}
	}

	return pids, nil
}

// getSessionCommand gets the command running in a tmux session
func (tm *TMUXManager) getSessionCommand(sessionName string) string {
	// Get the command from the first pane of the session
	tmuxArgs := []string{"-f", tm.configPath, "-S", tm.socketPath,
		"list-panes", "-t", sessionName, "-F", "#{pane_current_command}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
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

	// Get the mapping between tmux session IDs and user session IDs
	mapping := tm.getSessionIDMapping()

	// Reverse the mapping to go from user ID to tmux ID
	reverseMapping := make(map[string]string)
	for tmuxID, userID := range mapping {
		reverseMapping[userID] = tmuxID
	}

	var result []SessionActivityInfo
	now := time.Now()

	for _, session := range sessions {
		// Look up the tmux session ID for this user session ID
		tmuxSessionID, ok := reverseMapping[session.ID]
		if !ok {
			// Can't map to tmux ID, skip
			continue
		}

		// Check if we have activity stats for this session
		stats, hasActivity := activityStats[tmuxSessionID]
		if !hasActivity {
			continue
		}

		// Check if activity is recent (within last 5 minutes)
		activityAge := now.Sub(stats.LastActivity)
		if activityAge > 5*time.Minute {
			continue
		}

		info := SessionActivityInfo{
			SessionID:      session.ID,
			Name:           session.Name,
			IsActive:       stats.IsActive,
			LastActivity:   stats.LastActivity,
			BytesPerSecond: stats.RecentDataRate, // Use rolling rate over last 10 seconds
		}

		result = append(result, info)
	}

	return result
}

// GetAllSessionActivityInfo returns activity information for all sessions, including inactive ones
func (tm *TMUXManager) GetAllSessionActivityInfo() map[string]*SessionActivityInfo {
	// Get activity stats from window monitor if available
	var activityStats map[string]*tmux.ActivityStats
	if tm.windowMonitor != nil {
		activityStats = tm.windowMonitor.GetActivityStats()
	} else {
		activityStats = make(map[string]*tmux.ActivityStats)
	}

	tm.logger.Debug("GetAllSessionActivityInfo called",
		"activityStatsCount", len(activityStats),
		"activityStatsKeys", func() []string {
			keys := make([]string, 0, len(activityStats))
			for k := range activityStats {
				keys = append(keys, k)
			}
			return keys
		}())

	// Get the mapping between tmux session IDs and user session IDs
	mapping := tm.getSessionIDMapping()

	tm.logger.Debug("Session ID mapping",
		"mapping", mapping,
		"mappingCount", len(mapping))

	result := make(map[string]*SessionActivityInfo)

	for tmuxSessionID, stats := range activityStats {
		// Map from tmux session ID (e.g., "1") to user session ID (e.g., "0")
		userSessionID, ok := mapping[tmuxSessionID]
		if !ok {
			// If we can't map it, skip this session
			tm.logger.Warn("No mapping found for tmux session ID",
				"tmuxSessionID", tmuxSessionID,
				"availableMappings", mapping)
			continue
		}

		tm.logger.Debug("Mapped session activity",
			"tmuxSessionID", tmuxSessionID,
			"userSessionID", userSessionID,
			"isActive", stats.IsActive,
			"bytesPerSecond", stats.RecentDataRate)

		info := &SessionActivityInfo{
			SessionID:      userSessionID,
			Name:           fmt.Sprintf("sprite-exec-%s", userSessionID),
			IsActive:       stats.IsActive,
			LastActivity:   stats.LastActivity,
			BytesPerSecond: stats.RecentDataRate, // Use rolling rate over last 10 seconds
		}

		result[userSessionID] = info
	}

	tm.logger.Debug("GetAllSessionActivityInfo returning",
		"resultCount", len(result),
		"resultKeys", func() []string {
			keys := make([]string, 0, len(result))
			for k := range result {
				keys = append(keys, k)
			}
			return keys
		}())

	return result
}

// getSessionIDMapping returns a mapping from tmux session IDs to user session IDs
// e.g., {"1": "0", "2": "1"} where "1" is the tmux session ID and "0" is the user session ID
func (tm *TMUXManager) getSessionIDMapping() map[string]string {
	// List all tmux sessions with their IDs
	// Format: tmux_session_id:session_name
	tmuxArgs := []string{"-f", tm.configPath, "-S", tm.socketPath,
		"list-sessions", "-F", "#{session_id}:#{session_name}"}

	var cmd *exec.Cmd
	if len(tm.cmdPrefix) > 0 {
		// Use prefix for server-side command
		allArgs := append([]string{"/.sprite/bin/tmux"}, tmuxArgs...)
		cmd = exec.Command(tm.cmdPrefix[0], append(tm.cmdPrefix[1:], allArgs...)...)
	} else {
		// Use system tmux if /.sprite/bin/tmux doesn't exist (e.g., in tests)
		tmuxBinary := "/.sprite/bin/tmux"
		if _, err := os.Stat(tmuxBinary); os.IsNotExist(err) {
			tmuxBinary = "tmux"
		}
		cmd = exec.Command(tmuxBinary, tmuxArgs...)
	}

	output, err := cmd.Output()
	if err != nil {
		// Log the error for debugging
		if tm.logger != nil {
			tm.logger.Warn("Failed to get session ID mapping",
				"error", err,
				"cmd", cmd.String())
		}
		// If tmux server is not running, return empty mapping
		return make(map[string]string)
	}

	tm.logger.Debug("Got tmux list-sessions output",
		"output", string(output),
		"cmd", cmd.String())

	mapping := make(map[string]string)
	lines := strings.Split(string(output), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		tm.logger.Debug("Parsing session line", "line", line)

		parts := strings.Split(line, ":")
		if len(parts) >= 2 {
			tmuxSessionID := strings.TrimPrefix(parts[0], "$") // Remove $ prefix
			sessionName := parts[1]

			tm.logger.Debug("Parsed session parts",
				"rawTmuxID", parts[0],
				"cleanTmuxID", tmuxSessionID,
				"sessionName", sessionName)

			// Extract user session ID from sprite-exec-X name
			if strings.HasPrefix(sessionName, "sprite-exec-") {
				userSessionID := strings.TrimPrefix(sessionName, "sprite-exec-")
				mapping[tmuxSessionID] = userSessionID
				tm.logger.Debug("Added to mapping",
					"tmuxSessionID", tmuxSessionID,
					"userSessionID", userSessionID)
			} else {
				tm.logger.Debug("Skipping non-sprite-exec session",
					"sessionName", sessionName)
			}
		} else {
			tm.logger.Warn("Unexpected line format",
				"line", line,
				"parts", parts)
		}
	}

	tm.logger.Debug("Final mapping created",
		"mapping", mapping,
		"size", len(mapping))

	return mapping
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

	// Create window monitor with the same context so it gets the logger
	tm.logger.Debug("Creating new window monitor",
		"monitorSession", "sprite-monitor",
		"socketPath", tm.socketPath,
		"configPath", tm.configPath,
		"cmdPrefix", tm.cmdPrefix)
	tm.windowMonitor = tmux.NewWindowMonitor(ctx, "sprite-monitor").
		WithSocketPath(tm.socketPath).
		WithConfigPath(tm.configPath).
		WithCmdPrefix(tm.cmdPrefix)

	// Start the window monitor
	tm.logger.Debug("Starting window monitor")
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
			tm.logger.Info("Window monitor event processor stopped due to context cancellation")
			return
		case event, ok := <-eventChan:
			if !ok {
				tm.logger.Error("Window monitor event channel closed")
				return
			}

			// Only log state change events at INFO level, activity events at DEBUG
			if event.EventType == "activity" {
				tm.logger.Debug("Received activity event",
					"originalSession", event.OriginalSession,
					"windowID", event.WindowID,
					"paneID", event.PaneID)
			} else {
				tm.logger.Info("Received window monitor event",
					"eventType", event.EventType,
					"originalSession", event.OriginalSession,
					"windowID", event.WindowID,
					"paneID", event.PaneID)
			}

			// Extract session ID from original session format (e.g., "$1" -> "1")
			sessionID := strings.TrimPrefix(event.OriginalSession, "$")
			if sessionID == "" || !strings.HasPrefix(event.OriginalSession, "$") {
				tm.logger.Debug("Skipping event with invalid session format",
					"originalSession", event.OriginalSession)
				continue
			}

			switch event.EventType {
			case "active":
				// Session became active
				tm.logger.Info("Session became active", "sessionID", sessionID)
				select {
				case tm.activityChan <- SessionActivity{
					SessionID: sessionID,
					Active:    true,
					Type:      "window_activity",
				}:
					tm.logger.Debug("Sent active event to activity channel", "sessionID", sessionID)
				default:
					tm.logger.Warn("Activity channel full, dropping active event", "sessionID", sessionID)
				}

			case "inactive":
				// Session became inactive
				tm.logger.Info("Session became inactive", "sessionID", sessionID)
				select {
				case tm.activityChan <- SessionActivity{
					SessionID: sessionID,
					Active:    false,
					Type:      "window_idle",
				}:
					tm.logger.Debug("Sent inactive event to activity channel", "sessionID", sessionID)
				default:
					tm.logger.Warn("Activity channel full, dropping inactive event", "sessionID", sessionID)
				}

			case "closed":
				// Session/window closed
				tm.logger.Info("Session ended", "sessionID", sessionID)
				select {
				case tm.activityChan <- SessionActivity{
					SessionID: sessionID,
					Active:    false,
					Type:      "session_end",
				}:
					tm.logger.Debug("Sent closed event to activity channel", "sessionID", sessionID)
				default:
					tm.logger.Warn("Activity channel full, dropping closed event", "sessionID", sessionID)
				}
			}
		}
	}
}

// SetPaneCallback registers a callback for pane lifecycle events for a session
func (tm *TMUXManager) SetPaneCallback(sessionID string, callback PaneLifecycleCallback) {
	tm.paneCallbacksMu.Lock()
	tm.paneCallbacks[sessionID] = callback
	tm.paneCallbacksMu.Unlock()

	if tm.logger != nil {
		tm.logger.Debug("Registered pane callback", "sessionID", sessionID)
	}
}

// RemovePaneCallback removes the callback for a session
func (tm *TMUXManager) RemovePaneCallback(sessionID string) {
	tm.paneCallbacksMu.Lock()
	delete(tm.paneCallbacks, sessionID)
	tm.paneCallbacksMu.Unlock()

	if tm.logger != nil {
		tm.logger.Debug("Removed pane callback", "sessionID", sessionID)
	}
}

// paneMonitor monitors pane changes for sessions with registered callbacks
func (tm *TMUXManager) paneMonitor(ctx context.Context) {
	// Track known panes for each session
	sessionPanes := make(map[string]map[int]bool) // sessionID -> set of pane PIDs

	ticker := time.NewTicker(2 * time.Second) // Poll every 2 seconds
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			// Get a snapshot of callbacks to check
			tm.paneCallbacksMu.RLock()
			callbacksCopy := make(map[string]PaneLifecycleCallback)
			for sid, cb := range tm.paneCallbacks {
				callbacksCopy[sid] = cb
			}
			tm.paneCallbacksMu.RUnlock()

			// Check each session with a callback
			for sessionID, callback := range callbacksCopy {
				// Get current panes for this session
				currentPanes, err := tm.GetSessionPanePIDs(sessionID)
				if err != nil {
					// Session might have ended
					if tm.logger != nil {
						tm.logger.Debug("Failed to get panes for session", "sessionID", sessionID, "error", err)
					}
					// Clean up if we had tracked panes
					if knownPanes, exists := sessionPanes[sessionID]; exists {
						// Notify about all removed panes
						for pid := range knownPanes {
							callback(sessionID, pid, false)
						}
						delete(sessionPanes, sessionID)
					}
					continue
				}

				// Convert to map for easy comparison
				currentPaneMap := make(map[int]bool)
				for _, pid := range currentPanes {
					currentPaneMap[pid] = true
				}

				// Get previously known panes
				knownPanes, exists := sessionPanes[sessionID]
				if !exists {
					knownPanes = make(map[int]bool)
					sessionPanes[sessionID] = knownPanes
				}

				// Check for new panes
				for pid := range currentPaneMap {
					if !knownPanes[pid] {
						// New pane detected
						if tm.logger != nil {
							tm.logger.Info("New pane detected", "sessionID", sessionID, "pid", pid)
						}
						callback(sessionID, pid, true)
						knownPanes[pid] = true
					}
				}

				// Check for removed panes
				for pid := range knownPanes {
					if !currentPaneMap[pid] {
						// Pane was removed
						if tm.logger != nil {
							tm.logger.Info("Pane removed", "sessionID", sessionID, "pid", pid)
						}
						callback(sessionID, pid, false)
						delete(knownPanes, pid)
					}
				}
			}
		}
	}
}
