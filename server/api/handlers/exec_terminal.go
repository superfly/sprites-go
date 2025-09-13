package handlers

import (
	"encoding/json"
	"fmt"
	"net/http"
	"strconv"
	"time"

	portwatcher "github.com/superfly/sprite-env/pkg/port-watcher"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// PortNotificationMessage represents a port event notification sent to the client
type PortNotificationMessage struct {
	Type    string `json:"type"`    // "port_opened" or "port_closed"
	Port    int    `json:"port"`    // Port number
	Address string `json:"address"` // Address (e.g., "127.0.0.1", "0.0.0.0")
	PID     int    `json:"pid"`     // Process ID
}

func (h *Handlers) HandleExec(w http.ResponseWriter, r *http.Request) {
	h.logger.Debug("HandleExec called",
		"method", r.Method,
		"url", r.URL.String(),
		"headers", r.Header)

	// Only accept GET requests (for WebSocket upgrade or session listing)
	if r.Method != http.MethodGet {
		h.logger.Warn("HandleExec: Method not allowed", "method", r.Method)
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	query := r.URL.Query()
	h.logger.Debug("HandleExec: Parsed query parameters", "query", query)

	// Support both standard Go format (cmd=echo&cmd=test123) and PHP/Rails format (cmd[]=echo&cmd[]=test123)
	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		// Try PHP/Rails style array syntax
		cmdArgs = query["cmd[]"]
	}

	// Get session parameters early to check if we're attaching to an existing session
	sessionID := query.Get("id")
	detachable := (query.Get("detachable") == "true")
	controlMode := (query.Get("cc") == "true")

	h.logger.Debug("HandleExec: Session parameters",
		"sessionID", sessionID,
		"detachable", detachable,
		"controlMode", controlMode,
		"hasTmuxManager", h.tmuxManager != nil)

	// If no command specified and not attaching to a session, list available sessions
	if len(cmdArgs) == 0 && sessionID == "" {
		// Check if this is a WebSocket upgrade request
		if r.Header.Get("Upgrade") == "websocket" {
			h.logger.Error("HandleExec: No command specified for WebSocket")
			http.Error(w, "No command specified", http.StatusBadRequest)
			return
		}

		// For regular GET requests without commands, list available sessions
		if r.Method == http.MethodGet {
			h.handleListExecSessions(w, r)
			return
		}

		h.logger.Error("HandleExec: No command specified")
		http.Error(w, "No command specified", http.StatusBadRequest)
		return
	}
	h.logger.Debug("HandleExec: Command arguments from query", "cmd", cmdArgs)

	path := query.Get("path")
	if path == "" && len(cmdArgs) > 0 {
		path = cmdArgs[0]
	}
	if path == "" {
		path = "bash"
	}
	h.logger.Debug("HandleExec: Command path", "path", path)

	var (
		args  []string
		tty   = (query.Get("tty") == "true")
		stdin = (query.Get("stdin") != "false") // Default to true for backward compatibility
	)
	if len(cmdArgs) > 1 {
		args = cmdArgs[1:]
	}

	// Handle tmux sessions
	var returnedSessionID string
	if sessionID != "" && h.tmuxManager != nil {
		// Attach to existing session using TMUXManager
		var tmuxCmd string
		var tmuxArgs []string
		tmuxCmd, tmuxArgs = h.tmuxManager.AttachSession(sessionID, controlMode)
		path = tmuxCmd
		args = tmuxArgs
		h.logger.Info("Attempting to attach to tmux session",
			"sessionID", sessionID,
			"controlMode", controlMode,
			"path", path,
			"args", args)
	} else if detachable && h.tmuxManager != nil {
		// Create a new detachable session with auto-incrementing ID
		var tmuxCmd string
		var tmuxArgs []string
		returnedSessionID, tmuxCmd, tmuxArgs = h.tmuxManager.CreateSession(path, args, controlMode)
		path = tmuxCmd
		args = tmuxArgs
		h.logger.Info("Created new detachable tmux session",
			"sessionID", returnedSessionID,
			"controlMode", controlMode)
	}

	options := []terminal.Option{
		terminal.WithCommand(path, args...),
		terminal.WithTTY(tty),
		terminal.WithStdin(stdin),
	}

	// Set console socket for TTY + wrapper combination
	if tty && len(h.execWrapperCommand) > 0 {
		socketPath := fmt.Sprintf("/tmp/wsexec-console-%d.sock", time.Now().UnixNano())
		options = append(options, terminal.WithConsoleSocket(socketPath))
		h.logger.Debug("HandleExec: Using console socket for TTY", "socketPath", socketPath)
	}

	if dir := query.Get("dir"); dir != "" {
		options = append(options, terminal.WithDir(dir))
	}

	if envVars := query["env"]; len(envVars) > 0 {
		options = append(options, terminal.WithEnv(envVars))
	}

	// Set initial terminal size if specified (for TTY mode)
	if tty {
		if colsStr := query.Get("cols"); colsStr != "" {
			if cols, err := strconv.ParseUint(colsStr, 10, 16); err == nil {
				if rowsStr := query.Get("rows"); rowsStr != "" {
					if rows, err := strconv.ParseUint(rowsStr, 10, 16); err == nil {
						h.logger.Info("Received initial terminal size from client",
							"cols", cols,
							"rows", rows,
							"source", "query_params")
						options = append(options, terminal.WithTerminalSize(uint16(cols), uint16(rows)))
						h.logger.Debug("HandleExec: Initial terminal size set", "cols", cols, "rows", rows)
					}
				}
			}
		}
	}

	if len(h.execWrapperCommand) > 0 {
		options = append(options, terminal.WithWrapper(h.execWrapperCommand))
	}

	options = append(options, terminal.WithLogger(h.logger))

	// Create unique exec ID for tracking
	execID := fmt.Sprintf("terminal-%d-%s", time.Now().UnixNano(), path)
	if sessionID != "" {
		// Use the session ID for tmux sessions
		execID = fmt.Sprintf("terminal-tmux-%s", sessionID)
	} else if returnedSessionID != "" {
		// Use the generated session ID for new detachable sessions
		execID = fmt.Sprintf("terminal-tmux-%s", returnedSessionID)
	}

	// Create a variable to hold the message sender once websocket connects
	var messageSender terminal.TextMessageSender

	// Create a single port watcher that will be shared
	var portWatcher *portwatcher.PortWatcher

	// Track existing panes that need to be added after process starts
	var pendingPanePIDs []int

	// Track session ID for tmux pane monitoring
	var monitoredSessionID string
	if sessionID != "" {
		monitoredSessionID = sessionID
	} else if returnedSessionID != "" {
		monitoredSessionID = returnedSessionID
	}

	// Port notification callback
	portCallback := func(port portwatcher.Port) {
		var msgType string
		if port.State == "open" {
			msgType = "port_opened"
		} else {
			msgType = "port_closed"
		}

		notification := PortNotificationMessage{
			Type:    msgType,
			Port:    port.Port,
			Address: port.Address,
			PID:     port.PID,
		}

		if messageSender != nil {
			if data, err := json.Marshal(notification); err == nil {
				if err := messageSender.SendTextMessage(data); err != nil {
					h.logger.Error("Failed to send port notification", "execID", execID, "notification", notification, "error", err)
				} else {
					h.logger.Debug("Sent port notification", "execID", execID, "notification", notification)
				}
			} else {
				h.logger.Error("Failed to marshal port notification", "execID", execID, "notification", notification, "error", err)
			}
		}
	}

	// For tmux sessions, create port watcher early and set up pane monitoring
	if h.tmuxManager != nil && monitoredSessionID != "" {
		// Create a dummy PID for the port watcher - will add real PIDs later
		// Using PID 1 as a placeholder since we need a PID to create the watcher
		watcher, err := portwatcher.New(1, portCallback)
		if err != nil {
			h.logger.Error("Failed to create port watcher for tmux session", "execID", execID, "sessionID", monitoredSessionID, "error", err)
		} else {
			if err := watcher.Start(); err != nil {
				h.logger.Error("Failed to start port watcher for tmux session", "execID", execID, "sessionID", monitoredSessionID, "error", err)
			} else {
				portWatcher = watcher
				// Immediately remove the dummy PID
				portWatcher.RemovePID(1)
				h.logger.Debug("Created port watcher for tmux session", "execID", execID, "sessionID", monitoredSessionID)

				// Set up pane lifecycle callback
				h.tmuxManager.SetPaneCallback(monitoredSessionID, func(sid string, panePID int, added bool) {
					// Convert container PID to host PID using system's ResolvePID
					hostPID, err := h.system.ResolvePID(panePID)
					if err != nil {
						h.logger.Warn("Failed to resolve container PID to host PID", "containerPID", panePID, "error", err)
						hostPID = panePID // Fall back to using the PID as-is
					} else if hostPID != panePID {
						h.logger.Debug("Converted container PID to host PID", "containerPID", panePID, "hostPID", hostPID)
					}

					if added {
						h.logger.Info("Adding tmux pane PID to port monitoring", "sessionID", sid, "containerPID", panePID, "hostPID", hostPID)
						if err := portWatcher.AddPID(hostPID); err != nil {
							h.logger.Error("Failed to add pane PID to port watcher", "sessionID", sid, "hostPID", hostPID, "error", err)
						}
					} else {
						h.logger.Info("Removing tmux pane PID from port monitoring", "sessionID", sid, "containerPID", panePID, "hostPID", hostPID)
						portWatcher.RemovePID(hostPID)
					}
				})

				// Get existing pane PIDs and add them to port monitoring
				existingPanes, err := h.tmuxManager.GetSessionPanePIDs(monitoredSessionID)
				if err != nil {
					h.logger.Error("Failed to get existing pane PIDs", "sessionID", monitoredSessionID, "error", err)
				} else {
					h.logger.Info("Found existing panes in tmux session", "sessionID", monitoredSessionID, "count", len(existingPanes), "containerPIDs", existingPanes)
					// Store existing panes to be processed after we get container init PID
					pendingPanePIDs = existingPanes
				}
			}
		}
	}

	// Set up process start callback to create port watcher and monitor ports
	options = append(options, terminal.WithOnProcessStart(func(pid int) {
		h.logger.Debug("Process started via terminal", "execID", execID, "pid", pid)

		// Create port watcher if not already created (for non-tmux sessions)
		if portWatcher == nil {
			watcher, err := portwatcher.New(pid, portCallback)
			if err != nil {
				h.logger.Error("Failed to create port watcher", "execID", execID, "pid", pid, "error", err)
				return
			}

			if err := watcher.Start(); err != nil {
				h.logger.Error("Failed to start port watcher", "execID", execID, "pid", pid, "error", err)
				return
			}

			portWatcher = watcher
			h.logger.Debug("Port watcher created and started", "execID", execID, "pid", pid)
		} else {
			// For tmux sessions, add the main process PID to existing watcher
			h.logger.Debug("Adding main process PID to existing port watcher", "execID", execID, "pid", pid)
			if err := portWatcher.AddPID(pid); err != nil {
				h.logger.Error("Failed to add main PID to port watcher", "execID", execID, "pid", pid, "error", err)
			}

			// Process any pending pane PIDs
			if len(pendingPanePIDs) > 0 {
				h.logger.Info("Processing pending pane PIDs", "count", len(pendingPanePIDs))
				for _, panePID := range pendingPanePIDs {
					// Convert container PID to host PID using system's ResolvePID
					hostPID, err := h.system.ResolvePID(panePID)
					if err != nil {
						h.logger.Error("Failed to resolve pending pane PID", "containerPID", panePID, "error", err)
						continue
					}
					h.logger.Info("Adding resolved pane PID to port monitoring", "containerPID", panePID, "hostPID", hostPID)
					if err := portWatcher.AddPID(hostPID); err != nil {
						h.logger.Error("Failed to add pane PID to port watcher", "hostPID", hostPID, "error", err)
					}
				}
				// Clear the pending list
				pendingPanePIDs = nil
			}
		}
	}))

	var (
		session   = terminal.NewSession(options...)
		wsHandler = terminal.NewWebSocketHandler(session).WithOnConnected(func(sender terminal.TextMessageSender) {
			messageSender = sender
			h.logger.Debug("WebSocket connected for exec terminal", "execID", execID)

			// Send session ID for new detachable sessions
			if returnedSessionID != "" {
				sessionMsg := fmt.Sprintf("\r\n📌 Detachable session created with ID: %s\r\n", returnedSessionID)
				sessionMsg += fmt.Sprintf("   To reconnect later, use: sprite exec -id %s\r\n\r\n", returnedSessionID)
				if err := sender.SendTextMessage([]byte(sessionMsg)); err != nil {
					h.logger.Error("Failed to send session ID message", "error", err)
				}
			}
		})
	)

	// Note: tmux handles detachment automatically when the WebSocket disconnects.
	// When running `tmux new-session`, the session will keep running after disconnect.
	// When running `tmux attach`, the session continues after detachment.
	h.logger.Info("HandleExec: Starting WebSocket command execution",
		"path", path,
		"args", args,
		"tty", tty,
		"stdin", stdin,
		"sessionID", sessionID,
		"wrapperCommand", h.execWrapperCommand)

	startTime := time.Now()

	// Execute the command directly
	err := wsHandler.Handle(w, r)

	// Clean up port monitoring
	if portWatcher != nil {
		portWatcher.Stop()
	}

	// Clean up tmux pane callback
	if monitoredSessionID != "" && h.tmuxManager != nil {
		h.tmuxManager.RemovePaneCallback(monitoredSessionID)
	}

	endTime := time.Now()
	duration := time.Since(startTime)
	h.logger.Info("Exec completed",
		"path", path,
		"args", args,
		"error", err,
		"requestDuration", duration.Milliseconds(),
	)

	// Send notification to admin channel if available
	if enricher := h.getContextEnricher(r.Context()); enricher != nil {
		statusCode := 200
		if err != nil {
			statusCode = 500
		}
		extraData := map[string]interface{}{
			"command":    path,
			"args":       args,
			"tty":        tty,
			"exec_id":    execID,
			"session_id": sessionID,
		}
		enricher.RequestEnd(r.Context(), &RequestInfo{
			RequestID:   execID,
			Method:      r.Method,
			Path:        r.URL.Path,
			StartTime:   startTime,
			EndTime:     endTime,
			DurationMS:  duration.Milliseconds(),
			StatusCode:  statusCode,
			Error:       err,
			RequestType: "exec",
			ExtraData:   extraData,
		})
	}
}

// handleListExecSessions lists available tmux sessions
func (h *Handlers) handleListExecSessions(w http.ResponseWriter, r *http.Request) {
	// Check if tmux manager is available
	if h.tmuxManager == nil {
		h.logger.Warn("TMUXManager not configured")
		w.Header().Set("Content-Type", "application/json")
		response := map[string]interface{}{
			"sessions": []interface{}{},
			"count":    0,
			"error":    "TMUXManager not configured",
		}
		json.NewEncoder(w).Encode(response)
		return
	}

	// Get list of sessions with detailed info from tmux manager
	sessions, err := h.tmuxManager.ListSessionsWithInfo()
	if err != nil {
		h.logger.Error("Failed to list tmux sessions", "error", err)
		w.Header().Set("Content-Type", "application/json")
		response := map[string]interface{}{
			"sessions": []interface{}{},
			"count":    0,
			"error":    fmt.Sprintf("Failed to list sessions: %v", err),
		}
		json.NewEncoder(w).Encode(response)
		return
	}

	// Get activity info for all sessions
	activityMap := h.tmuxManager.GetAllSessionActivityInfo()

	// Merge session info with activity data
	type SessionWithActivity struct {
		terminal.SessionInfo
		BytesPerSecond float64    `json:"bytes_per_second"`
		IsActive       bool       `json:"is_active"`
		LastActivity   *time.Time `json:"last_activity,omitempty"`
	}

	sessionsWithActivity := make([]SessionWithActivity, 0, len(sessions))
	for _, session := range sessions {
		s := SessionWithActivity{
			SessionInfo:    session,
			BytesPerSecond: 0,
			IsActive:       false,
		}

		if activity, ok := activityMap[session.ID]; ok {
			s.BytesPerSecond = activity.BytesPerSecond
			s.IsActive = activity.IsActive
			s.LastActivity = &activity.LastActivity
		}

		sessionsWithActivity = append(sessionsWithActivity, s)
	}

	// Return JSON response
	w.Header().Set("Content-Type", "application/json")
	response := map[string]interface{}{
		"sessions": sessionsWithActivity,
		"count":    len(sessionsWithActivity),
	}

	if err := json.NewEncoder(w).Encode(response); err != nil {
		h.logger.Error("Failed to encode response", "error", err)
	}
}
