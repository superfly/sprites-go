package handlers

import (
	"fmt"
	"net/http"
	"strconv"
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

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

	// working dir
	if dir := query.Get("dir"); dir != "" {
		options = append(options, terminal.WithDir(dir))
	}

	// Set environment variables if specified
	if envVars := query["env"]; len(envVars) > 0 {
		options = append(options, terminal.WithEnv(envVars))
	}

	// Set initial terminal size if specified (for TTY mode)
	if tty {
		if colsStr := query.Get("cols"); colsStr != "" {
			if cols, err := strconv.ParseUint(colsStr, 10, 16); err == nil {
				if rowsStr := query.Get("rows"); rowsStr != "" {
					if rows, err := strconv.ParseUint(rowsStr, 10, 16); err == nil {
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

	// Create transcript collector based on system configuration
	if h.system.IsTranscriptsEnabled() {
		// Get working directory from query
		var workDirPtr *string
		if dir := query.Get("dir"); dir != "" {
			workDirPtr = &dir
		}

		// Get environment variables
		envVars := query["env"]

		transcriptCollector, err := h.system.CreateTranscriptCollector(workDirPtr, envVars, tty)
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
		wsHandler = terminal.NewWebSocketHandler(session)
	)
	h.logger.Info("HandleExec: Starting WebSocket command execution",
		"path", path,
		"args", args,
		"tty", tty,
		"wrapperCommand", h.execWrapperCommand)

	startTime := time.Now()
	err := wsHandler.Handle(w, r)

	h.logger.Info("Exec completed",
		"path", path,
		"args", args,
		"error", err,
		"requestDuration", time.Since(startTime).Milliseconds(),
	)
}
