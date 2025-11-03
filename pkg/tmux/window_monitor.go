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
	logger           *slog.Logger
	parser           *TmuxControlModeParser
	monitorSession   string
	linkedWindows    map[string]string         // windowID -> original sessionID
	activityStats    map[string]*ActivityStats // sessionID -> stats
	inactivityTimers map[string]*time.Timer    // sessionID -> inactivity timer
	mu               sync.RWMutex
	eventChan        chan WindowMonitorEvent
	socketPath       string                    // tmux socket path
	configPath       string                    // tmux config path
	cmdPath          string                    // Path to tmux binary (unwrapped)
	wrapCmd          func(*exec.Cmd) *exec.Cmd // Optional wrapper (e.g., container.Wrap)
	closed           chan struct{}             // Signal that monitor has closed
	closeOnce        sync.Once
}

// ActivityStats tracks activity statistics for a session
type ActivityStats struct {
	SessionID      string
	ByteCount      int64
	LastActivity   time.Time
	StartTime      time.Time
	IsActive       bool    // Computed dynamically from inactivity timer existence (set in GetActivityStats)
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
		logger:           logger,
		monitorSession:   monitorSession,
		linkedWindows:    make(map[string]string),
		activityStats:    make(map[string]*ActivityStats),
		inactivityTimers: make(map[string]*time.Timer),
		eventChan:        make(chan WindowMonitorEvent, 1000),
		socketPath:       "", // Must be set explicitly
		configPath:       "", // Must be set explicitly
		cmdPath:          "", // Must be set explicitly via WithCommand
		closed:           make(chan struct{}),
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

	// Do initial discovery after a small delay to ensure control mode is connected
	// If there's a race and output arrives before discovery completes, linkWindowFromPane handles it
	go func() {
		time.Sleep(100 * time.Millisecond)
		wm.logger.Debug("Starting initial window discovery")
		wm.discoverAndLinkWindows()
	}()

	wm.logger.Debug("Window monitor started", "session", wm.monitorSession)
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
			// Update activity stats (only tracks data, doesn't send events)
			wm.updateActivityStats(originalSession, len(e.Data))

			// Always send "active" event immediately on output
			cleanSessionID := strings.TrimPrefix(originalSession, "$")
			wm.mu.Lock()
			// Stop existing timer if any
			if timer, hasTimer := wm.inactivityTimers[cleanSessionID]; hasTimer && timer != nil {
				timer.Stop()
			}
			// Start new 5-second timer
			wm.inactivityTimers[cleanSessionID] = time.AfterFunc(5*time.Second, func() {
				defer func() {
					if r := recover(); r != nil {
						// Channel may be closed - this is safe to ignore
						wm.logger.Debug("Timer callback: channel closed, dropping inactive event", "sessionID", cleanSessionID)
					}
				}()
				wm.mu.Lock()
				delete(wm.inactivityTimers, cleanSessionID)
				wm.mu.Unlock()
				// Send inactive event (may panic if channel is closed)
				select {
				case wm.eventChan <- WindowMonitorEvent{
					OriginalSession: "$" + cleanSessionID,
					EventType:       "inactive",
				}:
					wm.logger.Debug("Sent inactive event after 5s quiet", "sessionID", cleanSessionID)
				default:
					wm.logger.Warn("Event channel full, dropping inactive event", "sessionID", cleanSessionID)
				}
			})
			wm.mu.Unlock()

			// Send active event immediately
			select {
			case wm.eventChan <- WindowMonitorEvent{
				OriginalSession: "$" + originalSession,
				EventType:       "active",
			}:
				wm.logger.Debug("Sent active event on output", "originalSession", originalSession)
			default:
				wm.logger.Warn("Event channel full, dropping active event", "originalSession", originalSession)
			}

			// Also send activity event with data (add $ prefix for consistency)
			select {
			case wm.eventChan <- WindowMonitorEvent{
				WindowID:        windowID,
				OriginalSession: "$" + originalSession,
				EventType:       "activity",
				PaneID:          e.PaneID,
				Data:            []byte(e.Data),
			}:
				wm.logger.Debug("Sent activity event", "originalSession", originalSession, "dataLen", len(e.Data))
			default:
				wm.logger.Warn("Event channel full, dropping activity event",
					"originalSession", originalSession)
			}
        } else {
            wm.logger.Debug("Pane output for unlinked window, attempting to link",
                "paneID", e.PaneID,
                "windowID", windowID,
                "linkedWindows", linkedWindowsCount)

            // Best-effort: emit an activity event with data even before linking, so
            // early output is visible to listeners (tests expect data-bearing event).
            // We resolve the session ID synchronously; failures are non-fatal.
            if windowID != "" {
                args := []string{}
                if wm.configPath != "" {
                    args = append(args, "-f", wm.configPath)
                }
                args = append(args, "-S", wm.socketPath, "display-message", "-p", "-t", windowID,
                    "#{session_id}:#{session_name}")

                cmd := wm.buildTmuxCommand(args)
                if out, err := cmd.Output(); err == nil {
                    parts := strings.Split(strings.TrimSpace(string(out)), ":")
                    if len(parts) >= 2 {
                        sessID := parts[0]
                        sessName := parts[1]
                        if sessName != wm.monitorSession && strings.HasPrefix(sessName, "sprite-exec-") {
                            // Emit an activity event with data using discovered session id
                            select {
                            case wm.eventChan <- WindowMonitorEvent{
                                WindowID:        windowID,
                                OriginalSession: "$" + strings.TrimPrefix(sessID, "$"),
                                EventType:       "activity",
                                PaneID:          e.PaneID,
                                Data:            []byte(e.Data),
                            }:
                                // ok
                            default:
                                wm.logger.Warn("Event channel full, dropping pre-link activity event",
                                    "originalSession", sessID)
                            }
                        }
                    }
                } else {
                    wm.logger.Debug("Failed pre-link session lookup", "windowID", windowID, "error", err)
                }
            }

            // Try to link this specific window
            go wm.linkWindowFromPane(e.PaneID, windowID)
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

		// Clean up activity stats and timers (originalSession is already the user session ID without $ prefix)
		if originalSession != "" {
			delete(wm.activityStats, originalSession)
			if timer, exists := wm.inactivityTimers[originalSession]; exists && timer != nil {
				timer.Stop()
				delete(wm.inactivityTimers, originalSession)
			}
		}
		wm.mu.Unlock()

		if originalSession != "" {
			select {
			case wm.eventChan <- WindowMonitorEvent{
				WindowID:        e.WindowID,
				OriginalSession: "$" + originalSession, // Add $ prefix for consistency
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

		// Clean up activity stats and timers (originalSession is already the user session ID without $ prefix)
		if originalSession != "" {
			delete(wm.activityStats, originalSession)
			if timer, exists := wm.inactivityTimers[originalSession]; exists && timer != nil {
				timer.Stop()
				delete(wm.inactivityTimers, originalSession)
			}
		}
		wm.mu.Unlock()

		if originalSession != "" {
			select {
			case wm.eventChan <- WindowMonitorEvent{
				WindowID:        e.WindowID,
				OriginalSession: "$" + originalSession, // Add $ prefix for consistency
				EventType:       "closed",
			}:
			default:
			}
		}
	}
}

// getWindowIDFromPane queries tmux to find the window ID for a pane
func (wm *WindowMonitor) getWindowIDFromPane(paneID string) string {
	// Prefer control-mode parser state to avoid spawning subprocesses
	if wm.parser != nil {
		if wid := wm.parser.LookupWindowIDForPane(paneID); wid != "" {
			return wid
		}
	}

	// Fallback: use a one-shot tmux query (legacy path)
	args := []string{}
	if wm.configPath != "" {
		args = append(args, "-f", wm.configPath)
	}
	args = append(args, "-S", wm.socketPath, "display-message", "-p", "-t", paneID, "#{window_id}")

	cmd := wm.buildTmuxCommand(args)
	output, err := cmd.Output()
	if err != nil {
		wm.logger.Debug("Failed to get window ID for pane (fallback)", "paneID", paneID, "error", err)
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

// linkWindowFromPane attempts to link a window to the monitor session based on its pane
func (wm *WindowMonitor) linkWindowFromPane(paneID, windowID string) {
	if windowID == "" {
		// During shutdown/close events tmux may emit pane output after the window is gone
		// Avoid noisy logs and simply drop the attempt.
		wm.logger.Debug("Cannot link window from pane: empty window ID", "paneID", paneID)
		return
	}

	// Check if window is already linked (might have been linked by another goroutine)
	wm.mu.RLock()
	_, alreadyLinked := wm.linkedWindows[windowID]
	wm.mu.RUnlock()

	if alreadyLinked {
		wm.logger.Info("Window already linked, skipping",
			"windowID", windowID,
			"paneID", paneID)
		return
	}

	// Get session information for this window
	args := []string{}
	if wm.configPath != "" {
		args = append(args, "-f", wm.configPath)
	}
	args = append(args, "-S", wm.socketPath, "display-message", "-p", "-t", windowID,
		"#{session_id}:#{session_name}")

	cmd := wm.buildTmuxCommand(args)
	output, err := cmd.Output()
	if err != nil {
		wm.logger.Warn("Failed to get session info for window",
			"windowID", windowID,
			"paneID", paneID,
			"error", err)
		return
	}

	parts := strings.Split(strings.TrimSpace(string(output)), ":")
	if len(parts) < 2 {
		wm.logger.Warn("Invalid session info format",
			"windowID", windowID,
			"output", string(output))
		return
	}

	sessionID := parts[0]
	sessionName := parts[1]

	// Skip if this is the monitor session itself
	if sessionName == wm.monitorSession {
		wm.logger.Debug("Skipping monitor session's own window (not a user session)",
			"windowID", windowID,
			"paneID", paneID,
			"sessionName", sessionName)
		return
	}

	// Only link windows from sprite-exec sessions
	if !strings.HasPrefix(sessionName, "sprite-exec-") {
		wm.logger.Warn("Skipping non-sprite-exec window - unexpected output source",
			"windowID", windowID,
			"sessionName", sessionName,
			"paneID", paneID)
		return
	}

	// Link the window
	wm.logger.Debug("Attempting to link window",
		"windowID", windowID,
		"paneID", paneID,
		"sessionID", sessionID,
		"sessionName", sessionName)

	if err := wm.linkWindow(windowID, sessionID); err != nil {
		wm.logger.Warn("❌ Failed to link window",
			"windowID", windowID,
			"paneID", paneID,
			"sessionID", sessionID,
			"sessionName", sessionName,
			"error", err)
	} else {
		wm.logger.Info("✓ Successfully linked window",
			"windowID", windowID,
			"paneID", paneID,
			"sessionID", sessionID,
			"sessionName", sessionName)
		// Refresh panes after linking to start monitoring
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
	// Store cleaned session ID (without $ prefix) for consistency
	cleanSessionID := strings.TrimPrefix(originalSessionID, "$")
	wm.linkedWindows[windowID] = cleanSessionID

	// Initialize activity stats for the newly linked session
	if _, exists := wm.activityStats[cleanSessionID]; !exists {
		now := time.Now()
		wm.activityStats[cleanSessionID] = &ActivityStats{
			SessionID:  cleanSessionID,
			StartTime:  now,
			LastActivity: now,
			dataPoints: make([]activityDataPoint, 0, 100),
		}
		wm.logger.Debug("Initialized activity stats for newly linked session",
			"sessionID", cleanSessionID,
			"originalSessionID", originalSessionID,
			"windowID", windowID)
	}
	// Start inactivity timer for newly linked session
	wm.inactivityTimers[cleanSessionID] = time.AfterFunc(5*time.Second, func() {
		defer func() {
			if r := recover(); r != nil {
				// Channel may be closed - this is safe to ignore
				wm.logger.Debug("Timer callback: channel closed, dropping inactive event (new session)", "sessionID", cleanSessionID)
			}
		}()
		wm.mu.Lock()
		delete(wm.inactivityTimers, cleanSessionID)
		wm.mu.Unlock()
		// Send inactive event (may panic if channel is closed)
		select {
		case wm.eventChan <- WindowMonitorEvent{
			OriginalSession: "$" + cleanSessionID,
			EventType:       "inactive",
		}:
			wm.logger.Debug("Sent inactive event after 5s quiet (new session)", "sessionID", cleanSessionID)
		default:
			wm.logger.Warn("Event channel full, dropping inactive event", "sessionID", cleanSessionID)
		}
	})
	wm.mu.Unlock()

	// Send active event to indicate the session is considered active upon linking
	select {
	case wm.eventChan <- WindowMonitorEvent{
		OriginalSession: "$" + cleanSessionID,
		EventType:       "active",
	}:
	default:
	}

	// Also send an initial activity event on link to emulate immediate output
	select {
	case wm.eventChan <- WindowMonitorEvent{
		WindowID:        windowID,
		OriginalSession: "$" + cleanSessionID,
		EventType:       "activity",
		PaneID:          "",
		Data:            nil,
	}:
	default:
	}

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
		// Stop all inactivity timers
		wm.mu.Lock()
		for sessionID, timer := range wm.inactivityTimers {
			if timer != nil {
				timer.Stop()
			}
			delete(wm.inactivityTimers, sessionID)
		}
		wm.mu.Unlock()
		if wm.parser != nil {
			err = wm.parser.Close()
			wm.parser = nil
		}
	})
	return err
}

// updateActivityStats updates activity statistics for a session (only tracks data, doesn't send events)
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
			LastActivity: now,
			dataPoints:   make([]activityDataPoint, 0, 100),
		}
		wm.activityStats[cleanSessionID] = stats
	}

	stats.ByteCount += int64(byteCount)
	stats.LastActivity = now

	wm.logger.Debug("Updated activity stats",
		"sessionID", cleanSessionID,
		"byteCount", byteCount,
		"totalBytes", stats.ByteCount)

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
		// Compute IsActive from timer existence
		isActive := wm.inactivityTimers[id] != nil

		wm.logger.Debug("Copying activity stats",
			"sessionID", id,
			"isActive", isActive,
			"byteCount", stats.ByteCount,
			"recentDataRate", stats.RecentDataRate)

		result[id] = &ActivityStats{
			SessionID:      stats.SessionID,
			ByteCount:      stats.ByteCount,
			LastActivity:   stats.LastActivity,
			StartTime:      stats.StartTime,
			IsActive:       isActive, // Computed from timer state
			RecentDataRate: stats.RecentDataRate,
			// Note: we don't copy dataPoints to avoid exposing internal state
		}
	}

	wm.logger.Debug("GetActivityStats returning", "resultCount", len(result))

	return result
}

