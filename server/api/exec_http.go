package api

import (
	"net/http"

	"github.com/superfly/sprite-env/pkg/container"
	"github.com/superfly/sprite-env/pkg/runner"
)

// ExecHTTPHandler implements a simple HTTP/1.1 exec endpoint (non-TTY only).
//   - Method: POST
//   - Request body: forwarded to stdin only when stdin=true
//   - Response: application/octet-stream with framing identical to websocket non-TTY
//     stdout=0x01, stderr=0x02, final exit frame=0x03 <code>
func (h *Handlers) ExecHTTPHandler(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	query := r.URL.Query()

	// Reject unsupported options for HTTP exec
	if _, ok := query["tty"]; ok {
		http.Error(w, "TTY not supported on POST /exec", http.StatusBadRequest)
		return
	}
	if query.Get("id") != "" || query.Get("detachable") != "" || query.Get("cc") != "" {
		http.Error(w, "Unsupported parameters for POST /exec", http.StatusBadRequest)
		return
	}

	// Parse command
	cmdArgs := query["cmd"]
	if len(cmdArgs) == 0 {
		cmdArgs = query["cmd[]"]
	}
	path := query.Get("path")
	if path == "" && len(cmdArgs) > 0 {
		path = cmdArgs[0]
	}
	if path == "" {
		path = "bash"
	}
	var args []string
	if len(cmdArgs) > 1 {
		args = cmdArgs[1:]
	}

	// Build base cmd with env and dir
	baseCmd := h.buildExecCommand(path, args, query)

	// Container wrap when enabled (non-tmux path only)
	finalCmd := baseCmd
	var wrapped *container.WrappedCommand
	if h.containerEnabled {
		wrapped = container.Wrap(baseCmd, "app", container.WithTTY(false))
		if wrapped != nil {
			finalCmd = wrapped.Cmd
		}
	}

	// Response headers for streaming binary data
	w.Header().Set("Content-Type", "application/octet-stream")
	w.Header().Set("X-Content-Type-Options", "nosniff")

	// Runner options (non-TTY only)
	var opts []runner.Option

	// Stdin: default disabled; enable only if stdin=true
	stdinEnabled := (query.Get("stdin") == "true")
	if stdinEnabled {
		opts = append(opts, runner.WithStdin(r.Body))
	}

	// Non-TTY multiplexed stdout/stderr
	mux := runner.NewMultiplexedWriter(streamingWriter{w})
	opts = append(opts, runner.WithStdout(mux.StdoutWriter()))
	opts = append(opts, runner.WithStderr(mux.StderrWriter()))

	run, err := runner.NewWithContext(r.Context(), finalCmd, opts...)
	if err != nil {
		http.Error(w, "failed to create runner", http.StatusInternalServerError)
		return
	}

	if err := run.Start(); err != nil {
		http.Error(w, "failed to start process", http.StatusInternalServerError)
		return
	}

	// Wait for completion and then write exit frame
	_ = run.Wait()
	_ = mux.WriteExit(run.ExitCode())

	// Best-effort flush
	if f, ok := w.(http.Flusher); ok {
		f.Flush()
	}
}

// streamingWriter writes to the ResponseWriter and flushes after each write when possible.
type streamingWriter struct{ w http.ResponseWriter }

func (s streamingWriter) Write(p []byte) (int, error) {
	n, err := s.w.Write(p)
	if f, ok := s.w.(http.Flusher); ok {
		f.Flush()
	}
	return n, err
}

// buildExecCommand is defined in exec.go; reference here for clarity.
// func (h *Handlers) buildExecCommand(path string, args []string, query url.Values) *exec.Cmd
