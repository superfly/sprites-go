package exec

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os/exec"
	"time"
)

// Request represents the request body for exec endpoint
type Request struct {
	Command []string      `json:"command"`
	Timeout time.Duration `json:"timeout"`
}

// Message represents a line of output or the final exit status
type Message struct {
	Type     string    `json:"type"` // "stdout", "stderr", or "exit"
	Data     string    `json:"data,omitempty"`
	ExitCode int       `json:"exit_code"`
	Error    string    `json:"error,omitempty"`
	Time     time.Time `json:"time"`
}

// Handler handles the /exec endpoint
type Handler struct {
	logger *slog.Logger
}

// NewHandler creates a new exec handler
func NewHandler(logger *slog.Logger) *Handler {
	return &Handler{
		logger: logger,
	}
}

// ServeHTTP handles exec requests
func (h *Handler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req Request
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if len(req.Command) == 0 {
		http.Error(w, "Command array cannot be empty", http.StatusBadRequest)
		return
	}

	// Set default timeout if not specified
	if req.Timeout == 0 {
		req.Timeout = 30 * time.Second
	}

	// Create command context with timeout
	ctx, cancel := context.WithTimeout(r.Context(), req.Timeout)
	defer cancel()

	// Set up the command
	cmd := exec.CommandContext(ctx, req.Command[0], req.Command[1:]...)

	// Get stdout and stderr pipes
	stdoutPipe, err := cmd.StdoutPipe()
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to create stdout pipe: %v", err), http.StatusInternalServerError)
		return
	}

	stderrPipe, err := cmd.StderrPipe()
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to create stderr pipe: %v", err), http.StatusInternalServerError)
		return
	}

	// Start the command
	if err := cmd.Start(); err != nil {
		http.Error(w, fmt.Sprintf("Failed to start command: %v", err), http.StatusInternalServerError)
		return
	}

	// Set up response headers before writing any body
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("X-Content-Type-Options", "nosniff")

	// Write status code to commit headers
	w.WriteHeader(http.StatusOK)

	// Create encoder for JSON output
	encoder := json.NewEncoder(w)

	// Channel for messages to be written
	messageChan := make(chan Message, 10)
	writerDone := make(chan struct{})

	// Writer goroutine - single point of writing to avoid races
	go func() {
		defer close(writerDone)
		for msg := range messageChan {
			if err := encoder.Encode(&msg); err != nil {
				h.logger.Error("Failed to encode message", "error", err)
				return
			}
			if f, ok := w.(http.Flusher); ok {
				f.Flush()
			}
		}
	}()

	// Create channels for output goroutines
	outputDone := make(chan struct{}, 2)

	// Stream stdout
	go func() {
		defer func() { outputDone <- struct{}{} }()
		scanner := bufio.NewScanner(stdoutPipe)
		for scanner.Scan() {
			msg := Message{
				Type: "stdout",
				Data: scanner.Text(),
				Time: time.Now(),
			}
			select {
			case messageChan <- msg:
			case <-ctx.Done():
				return
			}
		}
		if err := scanner.Err(); err != nil && err != io.EOF {
			h.logger.Error("Error reading stdout", "error", err)
		}
	}()

	// Stream stderr
	go func() {
		defer func() { outputDone <- struct{}{} }()
		scanner := bufio.NewScanner(stderrPipe)
		for scanner.Scan() {
			msg := Message{
				Type: "stderr",
				Data: scanner.Text(),
				Time: time.Now(),
			}
			select {
			case messageChan <- msg:
			case <-ctx.Done():
				return
			}
		}
		if err := scanner.Err(); err != nil && err != io.EOF {
			h.logger.Error("Error reading stderr", "error", err)
		}
	}()

	// Wait for output goroutines to finish
	for i := 0; i < 2; i++ {
		<-outputDone
	}

	// Wait for command to finish
	err = cmd.Wait()

	// Send exit status
	exitMsg := Message{
		Type: "exit",
		Time: time.Now(),
	}

	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			exitMsg.ExitCode = exitErr.ExitCode()
		} else {
			exitMsg.ExitCode = -1
			exitMsg.Error = err.Error()
		}
	} else {
		exitMsg.ExitCode = 0
	}

	// Send exit message - use a short timeout to ensure we can send it
	sendCtx, sendCancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer sendCancel()

	select {
	case messageChan <- exitMsg:
	case <-sendCtx.Done():
		h.logger.Error("Failed to send exit message", "error", sendCtx.Err())
	}

	// Close message channel to signal writer to stop
	close(messageChan)

	// Wait for writer to finish
	<-writerDone
}
