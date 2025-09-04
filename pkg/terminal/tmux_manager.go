package terminal

import (
	"fmt"
	"log/slog"
	"os/exec"
	"strconv"
	"strings"
	"sync/atomic"
	"time"
)

// SessionInfo contains information about a tmux session
type SessionInfo struct {
	ID      string    `json:"id"`
	Name    string    `json:"name"`
	Created time.Time `json:"created"`
	Command string    `json:"command"`
}

// TMUXManager manages detachable tmux sessions for exec commands
type TMUXManager struct {
	logger *slog.Logger
	nextID int64
}

// NewTMUXManager creates a new TMUXManager
func NewTMUXManager(logger *slog.Logger) *TMUXManager {
	tm := &TMUXManager{
		logger: logger,
		nextID: 1,
	}
	// Initialize nextID based on existing sessions
	tm.initializeNextID()
	return tm
}

// initializeNextID sets nextID based on existing tmux sessions
func (tm *TMUXManager) initializeNextID() {
	sessions, _ := tm.ListSessions()
	maxID := int64(0)
	for _, session := range sessions {
		// Try to parse numeric session IDs
		if id, err := strconv.ParseInt(session, 10, 64); err == nil {
			if id > maxID {
				maxID = id
			}
		}
	}
	tm.nextID = maxID + 1
	if tm.logger != nil {
		tm.logger.Debug("Initialized TMUXManager", "nextID", tm.nextID)
	}
}

// CreateSession creates a new tmux session with an auto-incrementing ID
func (tm *TMUXManager) CreateSession(cmd string, args []string, controlMode bool) (string, string, []string) {
	// Get current ID and increment for next time
	// We add 1 first, so if nextID is 0, we get 1 for the first session
	sessionID := fmt.Sprintf("%d", atomic.AddInt64(&tm.nextID, 1))

	if tm.logger != nil {
		tm.logger.Info("Creating new tmux session", "sessionID", sessionID, "cmd", cmd, "args", args)
	}

	// Return tmux new-session command with sprite-exec-<id> naming
	// Start attached so the user can interact immediately
	sessionName := fmt.Sprintf("sprite-exec-%s", sessionID)

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
	cmd := exec.Command("/.sprite/bin/tmux", "-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux", "has-session", "-t", sessionName)
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
	cmd := exec.Command("/.sprite/bin/tmux", "-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux", "kill-session", "-t", sessionName)
	return cmd.Run()
}

// ListSessions returns a list of all tmux sessions (sprite-exec-<id> names only)
func (tm *TMUXManager) ListSessions() ([]string, error) {
	// List all tmux sessions
	cmd := exec.Command("/.sprite/bin/tmux", "-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux", "list-sessions", "-F", "#{session_name}")
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
	cmd := exec.Command("/.sprite/bin/tmux", "-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux",
		"list-sessions", "-F",
		"#{session_name}|#{session_created}|#{session_windows}|#{pane_current_command}")
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
	cmd := exec.Command("/.sprite/bin/tmux", "-f", "/.sprite/bin/tmux.conf", "-S", "/.sprite/tmp/exec-tmux",
		"list-panes", "-t", sessionName, "-F", "#{pane_current_command}")
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
