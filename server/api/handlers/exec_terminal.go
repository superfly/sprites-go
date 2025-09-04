package handlers

import (
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"strconv"
	"syscall"
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

	// Set up process start callback to monitor ports with websocket notifications
	options = append(options, terminal.WithOnProcessStart(func(pid int) {
		h.logger.Debug("Process started via terminal", "execID", execID, "pid", pid)

		// Start port monitoring directly here
		go h.startPortMonitoring(execID, pid, func(port portwatcher.Port, opened bool) {
			var msgType string
			if opened {
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
		})
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

// startPortMonitoring starts monitoring ports for a specific process
func (h *Handlers) startPortMonitoring(execID string, pid int, callback func(port portwatcher.Port, opened bool)) {
	h.logger.Debug("Starting port monitoring", "execID", execID, "pid", pid)

	// Track active ports to detect when they close
	activePorts := make(map[string]portwatcher.Port) // key: "address:port:pid"

	portCallback := func(port portwatcher.Port) {
		key := fmt.Sprintf("%s:%d:%d", port.Address, port.Port, port.PID)
		if _, exists := activePorts[key]; !exists {
			activePorts[key] = port
			h.logger.Info("Process started listening on port",
				"execID", execID,
				"port", port.Port,
				"address", port.Address,
				"pid", port.PID)
			callback(port, true) // port opened
		}
	}

	// Create and start port watcher
	watcher, err := portwatcher.New(pid, portCallback)
	if err != nil {
		h.logger.Error("Failed to create port watcher", "execID", execID, "pid", pid, "error", err)
		return
	}

	if err := watcher.Start(); err != nil {
		h.logger.Error("Failed to start port watcher", "execID", execID, "pid", pid, "error", err)
		return
	}

	h.logger.Debug("Port watcher started successfully", "execID", execID, "pid", pid)

	// Monitor process lifecycle - stop when process exits
	go func() {
		defer func() {
			h.logger.Debug("Stopping port watcher", "execID", execID, "pid", pid)
			watcher.Stop()

			// When stopping, notify that all ports are closed
			for _, port := range activePorts {
				h.logger.Info("Process stopped listening on port",
					"execID", execID,
					"port", port.Port,
					"address", port.Address,
					"pid", port.PID)
				callback(port, false) // port closed
			}
		}()

		// Monitor process by checking if it's still running
		for {
			// Check if process is still running
			if !h.isProcessRunning(pid) {
				h.logger.Debug("Process is no longer running, stopping port monitoring", "execID", execID, "pid", pid)
				return
			}

			// Check every 5 seconds
			time.Sleep(5 * time.Second)
		}
	}()
}

// isProcessRunning checks if a process with the given PID is still running
func (h *Handlers) isProcessRunning(pid int) bool {
	// On Unix systems, sending signal 0 checks if process exists without actually sending a signal
	process, err := os.FindProcess(pid)
	if err != nil {
		return false
	}

	// Send signal 0 to check if process exists (using syscall.Signal)
	err = process.Signal(syscall.Signal(0))
	return err == nil
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

	// Return JSON response
	w.Header().Set("Content-Type", "application/json")
	response := map[string]interface{}{
		"sessions": sessions,
		"count":    len(sessions),
	}

	if err := json.NewEncoder(w).Encode(response); err != nil {
		h.logger.Error("Failed to encode response", "error", err)
	}
}
