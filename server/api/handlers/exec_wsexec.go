package handlers

import (
	"fmt"
	"net/http"
	"strconv"
	"time"

	"io"

	"github.com/sprite-env/packages/wsexec"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// transcriptAdapter adapts terminal.TranscriptCollector to wsexec.LogCollector
type transcriptAdapter struct {
	collector terminal.TranscriptCollector
}

func (t *transcriptAdapter) Stream(name string) io.Writer {
	return t.collector.StreamWriter(name)
}

func (t *transcriptAdapter) Close() error {
	return t.collector.Close()
}

// HandleExec handles GET/POST /sprites/{id}/exec - WebSocket upgrade endpoint for sprite execution
// @public
// @operation GET /v1/sprites/{id}/exec
// @summary Execute commands in a sprite
// @description Establish a WebSocket connection to execute commands in a specific sprite environment. Supports both TTY and non-TTY modes with real-time streaming.
// @tags Sprites
// @security Bearer
// @param id path string true "Sprite ID"
// @param cmd query string false "Command arguments to execute (defaults to 'bash -l')"
// @param tty query boolean false "Enable TTY mode for interactive shell (default: false)"
// @param dir query string false "Working directory for command execution"
// @param env query string false "Environment variables (format: KEY=value)"
// @param cols query integer false "Terminal columns (only used with tty=true)"
// @param rows query integer false "Terminal rows (only used with tty=true)"
// @response 101 {string} string "WebSocket connection established"
// @response 200 {string} string "Command execution successful"
// @response 400 {string} string "Bad request - invalid parameters"
// @response 401 {string} string "Unauthorized - invalid or missing authentication"
// @response 405 {string} string "Method not allowed - only GET/POST supported"
// @response 503 {string} string "Service unavailable - sprite not running"
func (h *Handlers) HandleExecWsexec(w http.ResponseWriter, r *http.Request) {
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

	h.logger.Debug("HandleExec: Method check passed")

	// Parse command from query parameters
	query := r.URL.Query()
	h.logger.Debug("HandleExec: Parsed query parameters", "query", query)

	// Get command arguments
	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		// Default to shell if no command specified
		cmdArgs = []string{"bash", "-l"}
		h.logger.Debug("HandleExec: No command specified, using default", "cmd", cmdArgs)
	} else {
		h.logger.Debug("HandleExec: Command arguments from query", "cmd", cmdArgs)
	}

	// Get command path (first argument)
	path := query.Get("path")
	if path == "" && len(cmdArgs) > 0 {
		path = cmdArgs[0]
	}
	if path == "" {
		path = "bash"
	}
	h.logger.Debug("HandleExec: Command path", "path", path)

	// Create command
	var args []string
	if len(cmdArgs) > 1 {
		args = cmdArgs[1:]
	}
	h.logger.Debug("HandleExec: Creating ServerCommand", "path", path, "args", args)

	cmd := wsexec.NewServerCommand(path, args...)

	// Set TTY based on query parameter
	tty := query.Get("tty") == "true"
	cmd.SetTTY(tty)
	h.logger.Debug("HandleExec: TTY setting", "tty", tty)

	// If TTY is requested and we have a wrapper command (exec.sh),
	// use console socket to avoid double-PTY issues
	if tty && len(h.execWrapperCommand) > 0 {
		// Generate a unique console socket path
		socketPath := fmt.Sprintf("/tmp/wsexec-console-%d.sock", time.Now().UnixNano())
		cmd.SetConsoleSocketPath(socketPath)
		h.logger.Debug("HandleExec: Using console socket for TTY", "socketPath", socketPath)
	}

	// Set working directory if specified
	if dir := query.Get("dir"); dir != "" {
		cmd.SetWorkingDir(dir)
		h.logger.Debug("HandleExec: Working directory set", "dir", dir)
	}

	// Set environment variables if specified
	if envVars := query["env"]; len(envVars) > 0 {
		cmd.SetEnv(envVars)
		h.logger.Debug("HandleExec: Environment variables set", "env", envVars)
	}

	// Set initial terminal size if specified (for TTY mode)
	if tty {
		if colsStr := query.Get("cols"); colsStr != "" {
			if cols, err := strconv.ParseUint(colsStr, 10, 16); err == nil {
				if rowsStr := query.Get("rows"); rowsStr != "" {
					if rows, err := strconv.ParseUint(rowsStr, 10, 16); err == nil {
						cmd.SetInitialTerminalSize(uint16(cols), uint16(rows))
						h.logger.Debug("HandleExec: Initial terminal size set", "cols", cols, "rows", rows)
					}
				}
			}
		}
	}

	// Set wrapper command and logger
	cmd.SetWrapperCommand(h.execWrapperCommand).
		SetLogger(h.logger)

	// Add transcript support if enabled
	if h.system.IsTranscriptsEnabled() {
		envVars := query["env"]
		transcriptCollector, err := h.system.CreateTranscriptCollector(envVars, tty)
		if err != nil {
			h.logger.Error("Failed to create transcript collector", "error", err)
			// Fail the request if transcript creation fails
			http.Error(w, "Failed to create transcript collector", http.StatusInternalServerError)
			return
		}
		cmd.SetLogCollector(&transcriptAdapter{collector: transcriptCollector})
		h.logger.Debug("HandleExec: Transcript collector set")
	}

	h.logger.Debug("HandleExec: Starting WebSocket command execution",
		"path", path,
		"args", args,
		"tty", tty,
		"wrapperCommand", h.execWrapperCommand)

	startTime := time.Now()

	// Create unique exec ID for tracking
	execID := fmt.Sprintf("wsexec-%d-%s", time.Now().UnixNano(), path)

	// Set up process start callback to monitor ports
	cmd.SetOnProcessStart(func(pid int) {
		h.logger.Debug("Process started via wsexec", "execID", execID, "pid", pid)
		if err := h.system.StartExecProcessTracking(execID, pid); err != nil {
			h.logger.Error("Failed to start port monitoring for wsexec process", "execID", execID, "pid", pid, "error", err)
		}
	})

	// Execute the command directly
	err := cmd.Handle(w, r)

	// Stop tracking when exec completes
	defer h.system.StopExecProcessTracking(execID)

	h.logger.Debug("Exec completed",
		"path", path,
		"args", args,
		"error", err,
		"requestDuration", time.Since(startTime).Milliseconds(),
	)
}
