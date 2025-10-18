package tmux

import (
	"context"
	"fmt"
	"log/slog"
	"os/exec"
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
	socketPath     string                    // tmux socket path
	configPath     string                    // tmux config path
	cmdPath        string                    // Path to tmux binary (unwrapped)
	wrapCmd        func(*exec.Cmd) *exec.Cmd // Optional wrapper (e.g., container.Wrap)
	closed         chan struct{}             // Signal that monitor has closed
	closeOnce      sync.Once
}

// ActivityStats tracks activity statistics for a session
type ActivityStats struct {
	SessionID      string
	ByteCount      int64
	LastActivity   time.Time
	StartTime      time.Time
	IsActive       bool    // Track whether session is currently considered active
	RecentDataRate float64 // bytes per second over recent window
	dataPoints     []activityDataPoint
}

type activityDataPoint struct {
	timestamp time.Time
	bytes     int64
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
	if logger == nil {
		logger = slog.Default()
	}
	logger = logger.With("component", "window_monitor", "monitorSession", monitorSession)

	logger.Debug("Creating new WindowMonitor")

	return &WindowMonitor{
		logger:         logger,
		monitorSession: monitorSession,
		linkedWindows:  make(map[string]string),
		activityStats:  make(map[string]*ActivityStats),
		eventChan:      make(chan WindowMonitorEvent, 1000),
		socketPath:     "", // Must be set explicitly
		configPath:     "", // Must be set explicitly
		cmdPath:        "", // Must be set explicitly via WithCommand
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

// WithCommand sets the base command to use for tmux execution
// Extracts the Path and binary name for creating fresh commands
func (wm *WindowMonitor) WithCommand(cmd *exec.Cmd) *WindowMonitor {
	// Capture only the base executable path; wrapping is handled via wrapCmd
	wm.cmdPath = cmd.Path
	return wm
}

// WithWrap sets a wrapper function to run tmux commands inside a container
func (wm *WindowMonitor) WithWrap(wrap func(*exec.Cmd) *exec.Cmd) *WindowMonitor {
	wm.wrapCmd = wrap
	return wm
}

// buildTmuxCommand constructs an exec.Cmd for running tmux with the provided args
func (wm *WindowMonitor) buildTmuxCommand(tmuxArgs []string) *exec.Cmd {
	// Build raw tmux command first
	cmd := exec.Command(wm.cmdPath, tmuxArgs...)
	if wm.wrapCmd != nil {
		if wrapped := wm.wrapCmd(cmd); wrapped != nil {
			if wm.logger != nil {
				wm.logger.Debug("WindowMonitor: wrapped tmux command",
					"fullCommand", wrapped.String(),
					"path", wrapped.Path,
					"args", wrapped.Args)
			}
			return wrapped
		}
		if wm.logger != nil {
			wm.logger.Error("WindowMonitor: wrapCmd returned nil; panicking")
		}
		panic("window monitor: wrapCmd returned nil for tmux command")
	}
	return cmd
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
	wm.logger.Debug("WindowMonitor.Start called",
		"session", wm.monitorSession,
		"socketPath", wm.socketPath,
		"configPath", wm.configPath)

	// Step 1: Create the session detached
	createArgs := []string{}
	if wm.configPath != "" {
		createArgs = append(createArgs, "-f", wm.configPath)
	}
	createArgs = append(createArgs, "-S", wm.socketPath, "new-session", "-d", "-s", wm.monitorSession)

	createCmd := wm.buildTmuxCommand(createArgs)

	wm.logger.Debug("WindowMonitor: exec",
		"fullCommand", createCmd.String(),
		"path", createCmd.Path,
		"args", createCmd.Args)

	if output, err := createCmd.CombinedOutput(); err != nil {
		// Session might already exist, which is fine
		wm.logger.Debug("Session creation returned error (might already exist)",
			"session", wm.monitorSession,
			"error", err,
			"output", string(output))
	}

	// Step 2: Attach to the session in control mode
	attachArgs := []string{}
	if wm.configPath != "" {
		attachArgs = append(attachArgs, "-f", wm.configPath)
	}
	attachArgs = append(attachArgs, "-S", wm.socketPath, "-C", "attach-session", "-t", wm.monitorSession)

	attachCmd := wm.buildTmuxCommand(attachArgs)

	wm.logger.Debug("WindowMonitor: exec",
		"fullCommand", attachCmd.String(),
		"path", attachCmd.Path,
		"args", attachCmd.Args)

	parser, err := NewTmuxControlModeParser(attachCmd, wm.logger)
	if err != nil {
		wm.logger.Error("Failed to create tmux control mode parser",
			"error", err,
			"cmd", attachCmd.String())
		return fmt.Errorf("failed to attach to tmux control mode: %w", err)
	}

	wm.logger.Debug("Successfully created tmux control mode parser")

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

	// Cache the events channel to avoid race with Close() setting parser to nil
	events := wm.parser.Events()

	for {
		select {
		case <-ctx.Done():
			wm.logger.Debug("Window monitor loop stopped due to context cancellation")
			return
		case <-wm.closed:
			wm.logger.Debug("Window monitor loop stopped due to close signal")
			return
		case event, ok := <-events:
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
		wm.logger.Debug("Sessions changed event received, discovering windows")
		go wm.discoverAndLinkWindows()

	case WindowAddEvent:
		// A new window was added to some session, check if we need to link it
		wm.logger.Debug("Window added event received", "windowID", e.WindowID)
		go wm.discoverAndLinkWindows()

	case PaneOutputEvent:
		// Look up which original session this window belongs to
		wm.mu.RLock()
		windowID := wm.getWindowIDFromPane(e.PaneID)
		originalSession, exists := wm.linkedWindows[windowID]
		linkedWindowsCount := len(wm.linkedWindows)
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
				wm.logger.Debug("Sent activity event", "originalSession", originalSession)
			default:
				wm.logger.Warn("Event channel full, dropping activity event",
					"originalSession", originalSession)
			}
		} else {
			wm.logger.Warn("Pane output for unlinked window",
				"paneID", e.PaneID,
				"windowID", windowID,
				"linkedWindows", linkedWindowsCount)
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

		// Clean up activity stats (originalSession is already the user session ID)
		if originalSession != "" {
			delete(wm.activityStats, originalSession)
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

		// Clean up activity stats (originalSession is already the user session ID)
		if originalSession != "" {
			delete(wm.activityStats, originalSession)
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

	cmd := wm.buildTmuxCommand(args)
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

	cmd := wm.buildTmuxCommand(args)
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
				wm.logger.Debug("Linked window to monitor",
					"windowID", windowID,
					"originalSession", sessionID,
					"sessionName", sessionName)
			}
		}
		// Silently skip already linked windows
	}

	if newWindows > 0 {
		wm.logger.Debug("Discovered and linked new windows", "count", newWindows, "totalWindows", totalWindows)
		// Refresh panes after linking new windows
		if wm.parser != nil {
			wm.parser.ListPanes()
		}
	} else {
		wm.logger.Debug("Window discovery completed",
			"newWindows", newWindows,
			"totalWindows", totalWindows,
			"linkedWindows", len(wm.linkedWindows))
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
	// Store cleaned session ID (without $ prefix) for consistency
	cleanSessionID := strings.TrimPrefix(originalSessionID, "$")
	wm.linkedWindows[windowID] = cleanSessionID

	// Initialize activity stats for the newly linked session
	if _, exists := wm.activityStats[cleanSessionID]; !exists {
		now := time.Now()
		wm.activityStats[cleanSessionID] = &ActivityStats{
			SessionID:    cleanSessionID,
			StartTime:    now,
			LastActivity: now,
			IsActive:     true, // New sessions start as active
			dataPoints:   make([]activityDataPoint, 0, 100),
		}
		wm.logger.Debug("Initialized activity stats for newly linked session",
			"sessionID", cleanSessionID,
			"originalSessionID", originalSessionID,
			"windowID", windowID)
	}
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
	// Defensive: handle both formats for robustness
	cleanSessionID := strings.TrimPrefix(sessionID, "$")

	now := time.Now()
	stats, exists := wm.activityStats[cleanSessionID]
	if !exists {
		wm.logger.Debug("Creating new activity stats for session",
			"sessionID", cleanSessionID,
			"originalFormat", sessionID)
		stats = &ActivityStats{
			SessionID:    cleanSessionID,
			StartTime:    now,
			LastActivity: now,  // Initialize to current time to prevent immediate timeout
			IsActive:     true, // New sessions start as active
			dataPoints:   make([]activityDataPoint, 0, 100),
		}
		wm.activityStats[cleanSessionID] = stats

		// Send active event for new session
		select {
		case wm.eventChan <- WindowMonitorEvent{
			OriginalSession: cleanSessionID,
			EventType:       "active",
		}:
			wm.logger.Debug("Sent active event for new session", "sessionID", cleanSessionID)
		default:
			wm.logger.Warn("Event channel full, dropping active event for new session", "sessionID", cleanSessionID)
		}
	} else if !stats.IsActive {
		// Session was inactive and is now active again
		wm.logger.Debug("Session became active again",
			"sessionID", cleanSessionID,
			"wasInactive", true)
		stats.IsActive = true

		// Send active event
		select {
		case wm.eventChan <- WindowMonitorEvent{
			OriginalSession: cleanSessionID,
			EventType:       "active",
		}:
			wm.logger.Debug("Sent active event for reactivated session", "sessionID", cleanSessionID)
		default:
			wm.logger.Warn("Event channel full, dropping active event for reactivated session", "sessionID", cleanSessionID)
		}
	}

	stats.ByteCount += int64(byteCount)
	stats.LastActivity = now

	wm.logger.Debug("Updated activity stats",
		"sessionID", cleanSessionID,
		"byteCount", byteCount,
		"totalBytes", stats.ByteCount,
		"isActive", stats.IsActive)

	// Add data point for rate calculation
	stats.dataPoints = append(stats.dataPoints, activityDataPoint{
		timestamp: now,
		bytes:     int64(byteCount),
	})

	// Calculate rolling rate over last 10 seconds
	wm.updateDataRate(stats, now)
}

// updateDataRate calculates the rolling data rate for a session
func (wm *WindowMonitor) updateDataRate(stats *ActivityStats, now time.Time) {
	// Remove data points older than 10 seconds
	cutoff := now.Add(-10 * time.Second)
	i := 0
	for i < len(stats.dataPoints) && stats.dataPoints[i].timestamp.Before(cutoff) {
		i++
	}
	if i > 0 {
		stats.dataPoints = stats.dataPoints[i:]
	}

	// Calculate rate over the data points in the window
	if len(stats.dataPoints) > 0 {
		firstTime := stats.dataPoints[0].timestamp
		duration := now.Sub(firstTime).Seconds()
		if duration > 0 {
			totalBytes := int64(0)
			for _, dp := range stats.dataPoints {
				totalBytes += dp.bytes
			}
			stats.RecentDataRate = float64(totalBytes) / duration
		}
	} else {
		stats.RecentDataRate = 0
	}
}

// GetActivityStats returns activity statistics for all sessions
func (wm *WindowMonitor) GetActivityStats() map[string]*ActivityStats {
	wm.mu.RLock()
	defer wm.mu.RUnlock()

	wm.logger.Debug("GetActivityStats called",
		"activityStatsCount", len(wm.activityStats),
		"activityStatsKeys", func() []string {
			keys := make([]string, 0, len(wm.activityStats))
			for k := range wm.activityStats {
				keys = append(keys, k)
			}
			return keys
		}())

	// Create a copy to avoid race conditions
	result := make(map[string]*ActivityStats)
	for id, stats := range wm.activityStats {
		wm.logger.Debug("Copying activity stats",
			"sessionID", id,
			"isActive", stats.IsActive,
			"byteCount", stats.ByteCount,
			"recentDataRate", stats.RecentDataRate)

		result[id] = &ActivityStats{
			SessionID:      stats.SessionID,
			ByteCount:      stats.ByteCount,
			LastActivity:   stats.LastActivity,
			StartTime:      stats.StartTime,
			IsActive:       stats.IsActive,
			RecentDataRate: stats.RecentDataRate,
			// Note: we don't copy dataPoints to avoid exposing internal state
		}
	}

	wm.logger.Debug("GetActivityStats returning", "resultCount", len(result))

	return result
}

// activityTimeoutChecker periodically checks for sessions that have become inactive
func (wm *WindowMonitor) activityTimeoutChecker(ctx context.Context) {
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	wm.logger.Debug("Activity timeout checker started")

	for {
		select {
		case <-ctx.Done():
			wm.logger.Info("Activity timeout checker stopped - context done")
			return
		case <-wm.closed:
			wm.logger.Info("Activity timeout checker stopped - monitor closed")
			return
		case <-ticker.C:
			wm.mu.Lock()
			now := time.Now()

			for sessionID, stats := range wm.activityStats {
				inactiveDuration := now.Sub(stats.LastActivity)
				// Check if session has been inactive for more than 5 seconds
				if stats.IsActive && inactiveDuration > 5*time.Second {
					wm.logger.Debug("Session became inactive due to timeout",
						"sessionID", sessionID,
						"inactiveDuration", inactiveDuration,
						"lastActivity", stats.LastActivity)
					stats.IsActive = false

					// Send inactive event
					select {
					case wm.eventChan <- WindowMonitorEvent{
						OriginalSession: "$" + sessionID, // Add back the $ prefix
						EventType:       "inactive",
					}:
						wm.logger.Debug("Sent inactive event", "sessionID", sessionID)
					default:
						wm.logger.Warn("Event channel full, dropping inactive event", "sessionID", sessionID)
					}
				}
			}

			wm.mu.Unlock()
		}
	}
}
