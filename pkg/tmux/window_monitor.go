package tmux

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// WindowMonitor monitors all tmux windows across all sessions
type WindowMonitor struct {
	logger         *slog.Logger
	parser         *TmuxControlModeParser
	monitorSession string
	linkedWindows  map[string]string         // windowID -> original sessionID
	activityStats  map[string]*ActivityStats // sessionID -> stats
	mu             sync.RWMutex
	eventChan      chan WindowMonitorEvent
	socketPath     string        // tmux socket path
	configPath     string        // tmux config path
	cmdPrefix      []string      // Command prefix for container execution
	tmuxBinary     string        // Path to tmux binary
	closed         chan struct{} // Signal that monitor has closed
	closeOnce      sync.Once
}

// ActivityStats tracks activity statistics for a session
type ActivityStats struct {
	SessionID    string
	ByteCount    int64
	LastActivity time.Time
	StartTime    time.Time
	IsActive     bool // Track whether session is currently considered active
}

// WindowMonitorEvent represents activity events from the window monitor
type WindowMonitorEvent struct {
	WindowID        string
	OriginalSession string
	EventType       string // "activity", "silence", "new", "closed", "active", "inactive"
	PaneID          string
	Data            []byte
}

// NewWindowMonitor creates a new window monitor
func NewWindowMonitor(ctx context.Context, monitorSession string) *WindowMonitor {
	logger := tap.Logger(ctx)
	return &WindowMonitor{
		logger:         logger,
		monitorSession: monitorSession,
		linkedWindows:  make(map[string]string),
		activityStats:  make(map[string]*ActivityStats),
		eventChan:      make(chan WindowMonitorEvent, 1000),
		socketPath:     "/.sprite/tmp/exec-tmux",
		configPath:     "/.sprite/bin/tmux.conf",
		tmuxBinary:     "tmux", // Default to tmux in PATH
		closed:         make(chan struct{}),
	}
}

// WithSocketPath sets a custom socket path (mainly for testing)
func (wm *WindowMonitor) WithSocketPath(path string) *WindowMonitor {
	wm.socketPath = path
	return wm
}

// WithConfigPath sets a custom config path (mainly for testing)
func (wm *WindowMonitor) WithConfigPath(path string) *WindowMonitor {
	wm.configPath = path
	return wm
}

// WithCmdPrefix sets a command prefix for container execution
func (wm *WindowMonitor) WithCmdPrefix(prefix []string) *WindowMonitor {
	wm.cmdPrefix = prefix
	return wm
}

// Start begins monitoring all windows
func (wm *WindowMonitor) Start(ctx context.Context) error {
	// Ensure we have a logger
	if wm.logger == nil {
		// Fallback to getting logger from context
		wm.logger = tap.Logger(ctx)
		if wm.logger == nil {
			// Last resort - use default logger
			wm.logger = slog.Default()
		}
	}

	// Log the start attempt with socket and config paths
	wm.logger.Info("WindowMonitor.Start called",
		"session", wm.monitorSession,
		"socketPath", wm.socketPath,
		"configPath", wm.configPath)

	// First, try to create the monitor session using regular tmux command (not control mode)
	createArgs := []string{}
	if wm.configPath != "" {
		createArgs = append(createArgs, "-f", wm.configPath)
	}
	createArgs = append(createArgs, "-S", wm.socketPath, "new-session", "-d", "-s", wm.monitorSession)

	// Determine tmux binary path
	tmuxBinary := "/.sprite/bin/tmux"

	// Check if tmux binary exists, fall back to system tmux if not found
	if _, err := os.Stat(tmuxBinary); err != nil {
		// Try system tmux at common locations
		systemPaths := []string{"/usr/bin/tmux", "/usr/local/bin/tmux", "/opt/homebrew/bin/tmux", "tmux"}
		found := false
		for _, path := range systemPaths {
			if path == "tmux" {
				// For bare "tmux", let exec.LookPath find it
				if _, err := exec.LookPath(path); err == nil {
					tmuxBinary = path
					found = true
					break
				}
			} else if _, err := os.Stat(path); err == nil {
				tmuxBinary = path
				found = true
				break
			}
		}

		if !found {
			wm.logger.Error("Tmux binary not found in any standard location",
				"triedPaths", systemPaths)
			return fmt.Errorf("tmux binary not found")
		}

		wm.logger.Info("Using system tmux binary",
			"path", tmuxBinary)
	}

	// Store the tmux binary path for later use
	wm.tmuxBinary = tmuxBinary

	// Check if socket directory exists
	// Extract directory from socket path - handle both /path/to/dir/exec-tmux and /path/to/socket formats
	var socketDir string
	if strings.HasSuffix(wm.socketPath, "/exec-tmux") {
		socketDir = strings.TrimSuffix(wm.socketPath, "/exec-tmux")
	} else {
		socketDir = filepath.Dir(wm.socketPath)
	}

	if info, err := os.Stat(socketDir); err != nil {
		wm.logger.Error("Socket directory not found",
			"dir", socketDir,
			"error", err)
		return fmt.Errorf("socket directory not found at %s: %w", socketDir, err)
	} else if !info.IsDir() {
		wm.logger.Error("Socket path is not a directory",
			"dir", socketDir)
		return fmt.Errorf("socket path %s is not a directory", socketDir)
	}

	var createCmd *exec.Cmd
	if len(wm.cmdPrefix) > 0 {
		// Use prefix for container execution
		allArgs := append([]string{wm.tmuxBinary}, createArgs...)
		createCmd = exec.Command(wm.cmdPrefix[0], append(wm.cmdPrefix[1:], allArgs...)...)
	} else {
		createCmd = exec.Command(wm.tmuxBinary, createArgs...)
	}

	wm.logger.Info("Creating tmux monitor session",
		"fullCommand", createCmd.String(),
		"args", createArgs)

	if output, err := createCmd.CombinedOutput(); err != nil {
		// Session might already exist, which is fine
		wm.logger.Debug("Session creation returned error (might already exist)",
			"session", wm.monitorSession,
			"error", err,
			"output", string(output),
			"cmd", createCmd.String())
	} else {
		wm.logger.Info("Created new monitor session",
			"session", wm.monitorSession,
			"output", string(output))
	}

	// Now attach to the session in control mode
	attachArgs := []string{}
	if wm.configPath != "" {
		attachArgs = append(attachArgs, "-f", wm.configPath)
	}
	attachArgs = append(attachArgs, "-S", wm.socketPath, "-C", "attach-session", "-t", wm.monitorSession)

	var attachCmd *exec.Cmd
	if len(wm.cmdPrefix) > 0 {
		// Use prefix for container execution
		allArgs := append([]string{wm.tmuxBinary}, attachArgs...)
		attachCmd = exec.Command(wm.cmdPrefix[0], append(wm.cmdPrefix[1:], allArgs...)...)
	} else {
		attachCmd = exec.Command(wm.tmuxBinary, attachArgs...)
	}

	wm.logger.Info("Attaching to tmux control mode",
		"fullCommand", attachCmd.String(),
		"args", attachArgs)

	parser, err := NewTmuxControlModeParser(attachCmd, wm.logger)
	if err != nil {
		wm.logger.Error("Failed to create tmux control mode parser",
			"error", err,
			"cmd", attachCmd.String())
		return fmt.Errorf("failed to attach to tmux control mode: %w", err)
	}

	wm.logger.Info("Successfully created tmux control mode parser")

	wm.parser = parser

	// Start the monitoring goroutine
	go wm.monitorLoop(ctx)

	// Start the activity timeout checker
	go wm.activityTimeoutChecker(ctx)

	// Do initial discovery after starting the monitor
	go func() {
		// Small delay to ensure control mode is fully connected
		time.Sleep(100 * time.Millisecond)
		wm.logger.Debug("Starting initial window discovery")
		wm.discoverAndLinkWindows()
	}()

	wm.logger.Info("Window monitor started", "session", wm.monitorSession)
	return nil
}

// monitorLoop processes events from the control mode parser
func (wm *WindowMonitor) monitorLoop(ctx context.Context) {
	defer func() {
		// Signal that monitor is closed
		wm.closeOnce.Do(func() {
			close(wm.closed)
		})

		if wm.parser != nil {
			wm.parser.Close()
			wm.parser = nil // Clear the parser reference
		}
		close(wm.eventChan)
	}()

	for {
		select {
		case <-ctx.Done():
			wm.logger.Debug("Window monitor loop stopped due to context cancellation")
			return
		case event, ok := <-wm.parser.Events():
			if !ok {
				// Parser events channel closed - process has exited
				// Check if there was an error from the parser
				if wm.parser != nil {
					if err := wm.parser.Wait(); err != nil {
						wm.logger.Error("Window monitor tmux process exited with error",
							"error", err,
							"session", wm.monitorSession)
					} else {
						wm.logger.Warn("Window monitor tmux process exited normally",
							"session", wm.monitorSession)
					}
				}
				return
			}

			// Only log non-output events at debug level
			if _, isPaneOutput := event.(PaneOutputEvent); !isPaneOutput {
				wm.logger.Debug("Received tmux event",
					"eventType", fmt.Sprintf("%T", event),
					"event", fmt.Sprintf("%+v", event))
			}

			wm.handleEvent(event)
		}
	}
}

// handleEvent processes tmux events
func (wm *WindowMonitor) handleEvent(event TmuxEvent) {
	switch e := event.(type) {
	case SessionsChangedEvent:
		// Sessions have changed (added/removed), discover new windows
		wm.logger.Debug("Sessions changed, discovering windows")
		go wm.discoverAndLinkWindows()

	case WindowAddEvent:
		// A new window was added to some session, check if we need to link it
		wm.logger.Debug("Window added", "windowID", e.WindowID)
		go wm.discoverAndLinkWindows()

	case PaneOutputEvent:
		// Look up which original session this window belongs to
		wm.mu.RLock()
		windowID := wm.getWindowIDFromPane(e.PaneID)
		originalSession, exists := wm.linkedWindows[windowID]
		wm.mu.RUnlock()

		if exists {
			// Update activity stats
			wm.updateActivityStats(originalSession, len(e.Data))

			// Send event
			select {
			case wm.eventChan <- WindowMonitorEvent{
				WindowID:        windowID,
				OriginalSession: originalSession,
				EventType:       "activity",
				PaneID:          e.PaneID,
				Data:            []byte(e.Data),
			}:
			default:
				wm.logger.Debug("Event channel full, dropping activity event")
			}
		} else {
			// Only log unlinked window output at trace level to reduce noise
			if wm.logger.Enabled(context.TODO(), slog.LevelDebug-4) {
				wm.logger.Debug("Pane output for unlinked window",
					"paneID", e.PaneID,
					"windowID", windowID)
			}
		}

	case WindowUnlinkEvent:
		// A window was unlinked - might need to re-link it
		wm.mu.Lock()
		delete(wm.linkedWindows, e.WindowID)
		wm.mu.Unlock()

		wm.logger.Debug("Window unlinked from monitor",
			"windowID", e.WindowID,
			"session", e.SessionID)

	case UnlinkedWindowCloseEvent:
		// Window closed
		wm.mu.Lock()
		originalSession := wm.linkedWindows[e.WindowID]
		delete(wm.linkedWindows, e.WindowID)

		// Clean up activity stats
		if originalSession != "" {
			cleanSessionID := strings.TrimPrefix(originalSession, "$")
			delete(wm.activityStats, cleanSessionID)
		}
		wm.mu.Unlock()

		if originalSession != "" {
			select {
			case wm.eventChan <- WindowMonitorEvent{
				WindowID:        e.WindowID,
				OriginalSession: originalSession,
				EventType:       "closed",
			}:
			default:
			}
		}

	case WindowCloseEvent:
		// Window closed (regular close event)
		wm.mu.Lock()
		originalSession := wm.linkedWindows[e.WindowID]
		delete(wm.linkedWindows, e.WindowID)

		// Clean up activity stats
		if originalSession != "" {
			cleanSessionID := strings.TrimPrefix(originalSession, "$")
			delete(wm.activityStats, cleanSessionID)
		}
		wm.mu.Unlock()

		if originalSession != "" {
			select {
			case wm.eventChan <- WindowMonitorEvent{
				WindowID:        e.WindowID,
				OriginalSession: originalSession,
				EventType:       "closed",
			}:
			default:
			}
		}
	}
}

// getWindowIDFromPane queries tmux to find the window ID for a pane
func (wm *WindowMonitor) getWindowIDFromPane(paneID string) string {
	// Use display-message to get window ID
	args := []string{}
	if wm.configPath != "" {
		args = append(args, "-f", wm.configPath)
	}
	args = append(args, "-S", wm.socketPath, "display-message", "-p", "-t", paneID, "#{window_id}")

	var cmd *exec.Cmd
	if len(wm.cmdPrefix) > 0 {
		// Use prefix for container execution
		allArgs := append([]string{wm.tmuxBinary}, args...)
		cmd = exec.Command(wm.cmdPrefix[0], append(wm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command(wm.tmuxBinary, args...)
	}

	output, err := cmd.Output()
	if err != nil {
		wm.logger.Debug("Failed to get window ID for pane", "paneID", paneID, "error", err)
		return ""
	}

	return strings.TrimSpace(string(output))
}

// discoverAndLinkWindows finds all windows and links them to the monitor session
func (wm *WindowMonitor) discoverAndLinkWindows() {
	// Check if monitor is still running
	select {
	case <-wm.closed:
		wm.logger.Debug("Window discovery aborted - monitor closed")
		return
	default:
	}

	// Check if parser is valid
	if wm.parser == nil {
		wm.logger.Debug("Window discovery aborted - parser is nil")
		return
	}
	// List all windows in all sessions
	args := []string{}
	if wm.configPath != "" {
		args = append(args, "-f", wm.configPath)
	}
	args = append(args, "-S", wm.socketPath, "list-windows", "-a", "-F",
		"#{window_id}:#{session_id}:#{session_name}:#{window_name}")

	var cmd *exec.Cmd
	if len(wm.cmdPrefix) > 0 {
		// Use prefix for container execution
		allArgs := append([]string{wm.tmuxBinary}, args...)
		cmd = exec.Command(wm.cmdPrefix[0], append(wm.cmdPrefix[1:], allArgs...)...)
	} else {
		cmd = exec.Command(wm.tmuxBinary, args...)
	}

	output, err := cmd.CombinedOutput()
	if err != nil {
		wm.logger.Debug("Failed to list windows",
			"error", err,
			"output", string(output),
			"socketPath", wm.socketPath)
		return
	}

	lines := strings.Split(string(output), "\n")
	newWindows := 0
	totalWindows := 0

	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		parts := strings.Split(line, ":")
		if len(parts) < 4 {
			continue
		}

		windowID := parts[0]
		sessionID := parts[1]
		sessionName := parts[2]

		totalWindows++

		// Skip windows already in the monitor session
		// The monitor session won't have a name starting with "sprite-exec-"
		// Also skip if the session name matches our monitor session name
		if sessionName == wm.monitorSession || !strings.HasPrefix(sessionName, "sprite-exec-") {
			continue
		}

		// Check if this window is already linked
		wm.mu.RLock()
		_, isLinked := wm.linkedWindows[windowID]
		wm.mu.RUnlock()

		if !isLinked {
			wm.logger.Debug("Found sprite-exec window to link",
				"windowID", windowID,
				"sessionID", sessionID,
				"sessionName", sessionName)
			// Link this window to our monitor session
			if err := wm.linkWindow(windowID, sessionID); err != nil {
				wm.logger.Debug("Failed to link window",
					"windowID", windowID,
					"sessionID", sessionID,
					"error", err)
			} else {
				newWindows++
				wm.logger.Debug("Successfully linked window to monitor",
					"windowID", windowID,
					"originalSession", sessionID,
					"sessionName", sessionName)
			}
		}
		// Silently skip already linked windows
	}

	if newWindows > 0 {
		wm.logger.Info("Discovered and linked new windows", "count", newWindows, "totalWindows", totalWindows)
		// Refresh panes after linking new windows
		if wm.parser != nil {
			wm.parser.ListPanes()
		}
	}
}

// linkWindow links a window to the monitor session
func (wm *WindowMonitor) linkWindow(windowID, originalSessionID string) error {
	// Check if parser is still valid
	if wm.parser == nil {
		return fmt.Errorf("parser is closed")
	}

	// Link the window to our monitor session
	err := wm.parser.SendCommand(fmt.Sprintf("link-window -s %s -t %s", windowID, wm.monitorSession))
	if err != nil {
		return err
	}

	// Store the mapping
	wm.mu.Lock()
	wm.linkedWindows[windowID] = originalSessionID
	wm.mu.Unlock()

	// Send new window event
	select {
	case wm.eventChan <- WindowMonitorEvent{
		WindowID:        windowID,
		OriginalSession: originalSessionID,
		EventType:       "new",
	}:
	default:
	}

	return nil
}

// GetEventChannel returns the event channel
func (wm *WindowMonitor) GetEventChannel() <-chan WindowMonitorEvent {
	return wm.eventChan
}

// GetLinkedWindows returns a copy of the linked windows map
func (wm *WindowMonitor) GetLinkedWindows() map[string]string {
	wm.mu.RLock()
	defer wm.mu.RUnlock()

	result := make(map[string]string, len(wm.linkedWindows))
	for k, v := range wm.linkedWindows {
		result[k] = v
	}
	return result
}

// Close stops the window monitor
func (wm *WindowMonitor) Close() error {
	var err error
	wm.closeOnce.Do(func() {
		close(wm.closed)
		if wm.parser != nil {
			err = wm.parser.Close()
			wm.parser = nil
		}
	})
	return err
}

// updateActivityStats updates activity statistics for a session
func (wm *WindowMonitor) updateActivityStats(sessionID string, byteCount int) {
	wm.mu.Lock()
	defer wm.mu.Unlock()

	// Extract session ID from format like "$1" -> "1"
	cleanSessionID := strings.TrimPrefix(sessionID, "$")

	stats, exists := wm.activityStats[cleanSessionID]
	if !exists {
		stats = &ActivityStats{
			SessionID: cleanSessionID,
			StartTime: time.Now(),
			IsActive:  true, // New sessions start as active
		}
		wm.activityStats[cleanSessionID] = stats

		// Send active event for new session
		select {
		case wm.eventChan <- WindowMonitorEvent{
			OriginalSession: sessionID,
			EventType:       "active",
		}:
		default:
			wm.logger.Debug("Event channel full, dropping active event")
		}
	} else if !stats.IsActive {
		// Session was inactive and is now active again
		stats.IsActive = true

		// Send active event
		select {
		case wm.eventChan <- WindowMonitorEvent{
			OriginalSession: sessionID,
			EventType:       "active",
		}:
		default:
			wm.logger.Debug("Event channel full, dropping active event")
		}
	}

	stats.ByteCount += int64(byteCount)
	stats.LastActivity = time.Now()
}

// GetActivityStats returns activity statistics for all sessions
func (wm *WindowMonitor) GetActivityStats() map[string]*ActivityStats {
	wm.mu.RLock()
	defer wm.mu.RUnlock()

	// Create a copy to avoid race conditions
	result := make(map[string]*ActivityStats)
	for id, stats := range wm.activityStats {
		result[id] = &ActivityStats{
			SessionID:    stats.SessionID,
			ByteCount:    stats.ByteCount,
			LastActivity: stats.LastActivity,
			StartTime:    stats.StartTime,
			IsActive:     stats.IsActive,
		}
	}

	return result
}

// activityTimeoutChecker periodically checks for sessions that have become inactive
func (wm *WindowMonitor) activityTimeoutChecker(ctx context.Context) {
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-wm.closed:
			wm.logger.Debug("Activity timeout checker stopped - monitor closed")
			return
		case <-ticker.C:
			wm.mu.Lock()
			now := time.Now()

			for sessionID, stats := range wm.activityStats {
				// Check if session has been inactive for more than 5 seconds
				if stats.IsActive && now.Sub(stats.LastActivity) > 5*time.Second {
					stats.IsActive = false

					// Send inactive event
					select {
					case wm.eventChan <- WindowMonitorEvent{
						OriginalSession: "$" + sessionID, // Add back the $ prefix
						EventType:       "inactive",
					}:
					default:
						wm.logger.Debug("Event channel full, dropping inactive event")
					}
				}
			}

			wm.mu.Unlock()
		}
	}
}
