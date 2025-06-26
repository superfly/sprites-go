package handlers

import (
	"bytes"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/sprite-env/packages/wsexec"
)

// Handlers contains all HTTP handlers
type Handlers struct {
	logger *slog.Logger
	system SystemManager

	// Config fields
	maxWaitTime        time.Duration
	execWrapperCommand []string
}

// Config holds handler configuration
type Config struct {
	MaxWaitTime        time.Duration
	ExecWrapperCommand []string
}

// NewHandlers creates a new Handlers instance
func NewHandlers(logger *slog.Logger, system SystemManager, config Config) *Handlers {
	return &Handlers{
		logger:             logger,
		system:             system,
		maxWaitTime:        config.MaxWaitTime,
		execWrapperCommand: config.ExecWrapperCommand,
	}
}

// HandleExec handles GET/POST /exec - WebSocket upgrade endpoint
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

	h.logger.Debug("HandleExec: Method check passed")

	// The WebSocket upgrader will handle the upgrade check
	// Standard WebSocket handshake uses GET with Upgrade headers

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

	collector, err := newFileCollector("/var/log/execs.log")
	if err == nil {
		cmd.SetLogCollector(collector)
	} else {
		h.logger.Error("HandleExec", "collector", err)
	}

	cmd.SetWrapperCommand(h.execWrapperCommand).
		SetLogger(h.logger)

	h.logger.Info("HandleExec: Starting WebSocket command execution",
		"path", path,
		"args", args,
		"tty", tty,
		"wrapperCommand", h.execWrapperCommand)

	if err := cmd.Handle(w, r); err != nil {
		h.logger.Error("HandleExec: Failed to handle exec WebSocket", "error", err)
	} else {
		h.logger.Debug("HandleExec: Successfully handled WebSocket command")
	}
}

type lineWriter struct {
	logger *slog.Logger
	stream string
	mu     sync.Mutex
	buf    bytes.Buffer
}

func newLineWriter(name string, l *slog.Logger) *lineWriter {
	return &lineWriter{logger: l, stream: name}
}

func (l *lineWriter) Write(p []byte) (int, error) {
	if l == nil {
		return len(p), nil
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	n := len(p)
	l.buf.Write(p)
	for {
		line, err := l.buf.ReadString('\n')
		if err != nil {
			break
		}
		line = strings.TrimSuffix(line, "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	return n, nil
}

func (l *lineWriter) Close() {
	if l == nil {
		return
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	if l.logger != nil && l.buf.Len() > 0 {
		line := strings.TrimRight(l.buf.String(), "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	l.buf.Reset()
}

type fileCollector struct {
	file    *os.File
	logger  *slog.Logger
	streams []*lineWriter
}

func newFileCollector(base string) (*fileCollector, error) {
	ext := filepath.Ext(base)
	name := strings.TrimSuffix(base, ext)
	path := fmt.Sprintf("%s-%d%s", name, time.Now().UnixNano(), ext)
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, err
	}
	return &fileCollector{
		file:   f,
		logger: slog.New(slog.NewTextHandler(f, nil)),
	}, nil
}

func (f *fileCollector) Stream(name string) io.Writer {
	ll := newLineWriter(name, f.logger)
	f.streams = append(f.streams, ll)
	return ll
}

func (f *fileCollector) Close() error {
	var err error
	for _, s := range f.streams {
		s.Close()
	}
	if f.file != nil {
		err = f.file.Close()
	}
	return err
}
