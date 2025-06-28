package handlers

import (
	"fmt"
	"net/http"
	"strconv"
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

// HandleExecRefactored demonstrates the new simplified exec handler using pkg/terminal.
// This will replace HandleExec once testing is complete.
func (h *Handlers) HandleExecRefactored(w http.ResponseWriter, r *http.Request) {
	h.logger.Debug("HandleExecRefactored called",
		"method", r.Method,
		"url", r.URL.String(),
		"headers", r.Header)

	// Accept GET (for WebSocket upgrade) and POST requests
	if r.Method != http.MethodGet && r.Method != http.MethodPost {
		h.logger.Warn("HandleExecRefactored: Method not allowed", "method", r.Method)
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Parse command from query parameters
	query := r.URL.Query()
	h.logger.Debug("HandleExecRefactored: Parsed query parameters", "query", query)

	// Get command arguments
	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		// Default to shell if no command specified
		cmdArgs = []string{"bash", "-l"}
		h.logger.Debug("HandleExecRefactored: No command specified, using default", "cmd", cmdArgs)
	} else {
		h.logger.Debug("HandleExecRefactored: Command arguments from query", "cmd", cmdArgs)
	}

	// Get command path (first argument)
	path := query.Get("path")
	if path == "" && len(cmdArgs) > 0 {
		path = cmdArgs[0]
	}
	if path == "" {
		path = "bash"
	}
	h.logger.Debug("HandleExecRefactored: Command path", "path", path)

	// Build session options
	var options []terminal.Option

	// Set command
	var args []string
	if len(cmdArgs) > 1 {
		args = cmdArgs[1:]
	}
	options = append(options, terminal.WithCommand(path, args...))

	// Set TTY based on query parameter
	tty := query.Get("tty") == "true"
	options = append(options, terminal.WithTTY(tty))
	h.logger.Debug("HandleExecRefactored: TTY setting", "tty", tty)

	// Set console socket for TTY + wrapper combination
	if tty && len(h.execWrapperCommand) > 0 {
		// Generate a unique console socket path
		socketPath := fmt.Sprintf("/tmp/wsexec-console-%d.sock", time.Now().UnixNano())
		options = append(options, terminal.WithConsoleSocket(socketPath))
		h.logger.Debug("HandleExecRefactored: Using console socket for TTY", "socketPath", socketPath)
	}

	// Set working directory if specified
	if dir := query.Get("dir"); dir != "" {
		options = append(options, terminal.WithDir(dir))
		h.logger.Debug("HandleExecRefactored: Working directory set", "dir", dir)
	}

	// Set environment variables if specified
	if envVars := query["env"]; len(envVars) > 0 {
		options = append(options, terminal.WithEnv(envVars))
		h.logger.Debug("HandleExecRefactored: Environment variables set", "env", envVars)
	}

	// Set initial terminal size if specified (for TTY mode)
	if tty {
		if colsStr := query.Get("cols"); colsStr != "" {
			if cols, err := strconv.ParseUint(colsStr, 10, 16); err == nil {
				if rowsStr := query.Get("rows"); rowsStr != "" {
					if rows, err := strconv.ParseUint(rowsStr, 10, 16); err == nil {
						options = append(options, terminal.WithTerminalSize(uint16(cols), uint16(rows)))
						h.logger.Debug("HandleExecRefactored: Initial terminal size set", "cols", cols, "rows", rows)
					}
				}
			}
		}
	}

	// Set wrapper command
	if len(h.execWrapperCommand) > 0 {
		options = append(options, terminal.WithWrapper(h.execWrapperCommand))
	}

	// Set logger
	options = append(options, terminal.WithLogger(h.logger))

	// Create transcript collector (using the existing fileCollector logic)
	// For now, we'll use a no-op transcript, but this could be enhanced
	// to use the same file-based logging as the original implementation
	transcript := terminal.NewMemoryTranscript() // Could be made configurable
	options = append(options, terminal.WithTranscript(transcript))

	// Create terminal session
	session := terminal.NewSession(options...)

	// Create WebSocket handler
	wsHandler := terminal.NewWebSocketHandler(session)

	h.logger.Info("HandleExecRefactored: Starting WebSocket command execution",
		"path", path,
		"args", args,
		"tty", tty,
		"wrapperCommand", h.execWrapperCommand)

	startTime := time.Now()
	err := wsHandler.Handle(w, r)

	h.logger.Info("Exec completed (refactored)",
		"path", path,
		"args", args,
		"error", err,
		"requestDuration", time.Since(startTime).Milliseconds(),
	)
}
