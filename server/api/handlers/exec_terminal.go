package handlers

import (
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"strconv"
	"syscall"
	"time"

	portwatcher "github.com/superfly/sprite-env/packages/port-watcher"
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

	// Accept GET (for WebSocket upgrade) and POST requests
	if r.Method != http.MethodGet && r.Method != http.MethodPost {
		h.logger.Warn("HandleExec: Method not allowed", "method", r.Method)
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	query := r.URL.Query()
	h.logger.Debug("HandleExec: Parsed query parameters", "query", query)

	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		// Default to shell if no command specified
		cmdArgs = []string{"bash", "-l"}
		h.logger.Debug("HandleExec: No command specified, using default", "cmd", cmdArgs)
	} else {
		h.logger.Debug("HandleExec: Command arguments from query", "cmd", cmdArgs)
	}

	path := query.Get("path")
	if path == "" && len(cmdArgs) > 0 {
		path = cmdArgs[0]
	}
	if path == "" {
		path = "bash"
	}
	h.logger.Debug("HandleExec: Command path", "path", path)

	var (
		args []string
		tty  = (query.Get("tty") == "true")
	)
	if len(cmdArgs) > 1 {
		args = cmdArgs[1:]
	}
	options := []terminal.Option{
		terminal.WithCommand(path, args...),
		terminal.WithTTY(tty),
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

	if h.system.IsTranscriptsEnabled() {
		envVars := query["env"]

		transcriptCollector, err := h.system.CreateTranscriptCollector(envVars, tty)
		if err != nil {
			h.logger.Error("Failed to create transcript collector", "error", err)
			// Fail the request if transcript creation fails
			http.Error(w, "Failed to create transcript collector", http.StatusInternalServerError)
			return
		}
		options = append(options, terminal.WithTranscript(transcriptCollector))
	}

	var (
		session   = terminal.NewSession(options...)
		wsHandler = terminal.NewWebSocketHandler(session).WithOnConnected(func(sender terminal.TextMessageSender) {
			messageSender = sender
			h.logger.Debug("WebSocket connected for exec terminal", "execID", execID)
		})
	)
	h.logger.Info("HandleExec: Starting WebSocket command execution",
		"path", path,
		"args", args,
		"tty", tty,
		"wrapperCommand", h.execWrapperCommand)

	startTime := time.Now()

	// Execute the command directly
	err := wsHandler.Handle(w, r)

	h.logger.Info("Exec completed",
		"path", path,
		"args", args,
		"error", err,
		"requestDuration", time.Since(startTime).Milliseconds(),
	)
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
