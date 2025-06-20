package api

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os/exec"
	"time"
)

// handleCheckpoint handles the /checkpoint endpoint
func (s *Server) handleCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req struct {
		CheckpointID string `json:"checkpoint_id"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if req.CheckpointID == "" {
		http.Error(w, "checkpoint_id is required", http.StatusBadRequest)
		return
	}

	// Send checkpoint command
	responseCh := make(chan CommandResponse)
	s.commandCh <- Command{
		Type:     CommandCheckpoint,
		Response: responseCh,
		Data:     CheckpointData{CheckpointID: req.CheckpointID},
	}

	// Wait for response
	resp := <-responseCh
	if !resp.Success {
		s.logger.Error("Failed to create checkpoint", "error", resp.Error, "checkpointID", req.CheckpointID)
		http.Error(w, fmt.Sprintf("Failed to create checkpoint: %v", resp.Error), http.StatusInternalServerError)
		return
	}

	s.logger.Info("Checkpoint created via API", "checkpointID", req.CheckpointID)
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{
		"status":        "checkpoint created",
		"checkpoint_id": req.CheckpointID,
	})
}

// handleRestore handles the /restore endpoint
func (s *Server) handleRestore(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req struct {
		CheckpointID string `json:"checkpoint_id"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if req.CheckpointID == "" {
		http.Error(w, "checkpoint_id is required", http.StatusBadRequest)
		return
	}

	// Send restore command
	responseCh := make(chan CommandResponse)
	s.commandCh <- Command{
		Type:     CommandRestore,
		Response: responseCh,
		Data:     RestoreData{CheckpointID: req.CheckpointID},
	}

	// Wait for response (this just confirms the restore was initiated)
	resp := <-responseCh
	if !resp.Success {
		s.logger.Error("Failed to initiate restore", "error", resp.Error, "checkpointID", req.CheckpointID)
		http.Error(w, fmt.Sprintf("Failed to initiate restore: %v", resp.Error), http.StatusInternalServerError)
		return
	}

	s.logger.Info("Restore initiated via API", "checkpointID", req.CheckpointID)
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{
		"status":        "restore initiated",
		"checkpoint_id": req.CheckpointID,
	})
}

// handleExec handles the /exec endpoint
func (s *Server) handleExec(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req ExecRequest
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
		req.Timeout = Duration(30 * time.Second)
	}

	// Build the actual command with wrapper if configured
	var cmdArgs []string
	if req.TTY && len(s.config.ExecTTYWrapperCommand) > 0 {
		// Use TTY wrapper
		cmdArgs = append(cmdArgs, s.config.ExecTTYWrapperCommand...)
		cmdArgs = append(cmdArgs, req.Command...)
	} else if len(s.config.ExecWrapperCommand) > 0 {
		// Use regular wrapper
		cmdArgs = append(cmdArgs, s.config.ExecWrapperCommand...)
		cmdArgs = append(cmdArgs, req.Command...)
	} else {
		// No wrapper, use command directly
		cmdArgs = req.Command
	}

	s.logger.Debug("Executing command", "command", cmdArgs, "timeout", time.Duration(req.Timeout))

	// Create command context with timeout
	ctx, cancel := context.WithTimeout(r.Context(), time.Duration(req.Timeout))
	defer cancel()

	// Set up the command
	cmd := exec.CommandContext(ctx, cmdArgs[0], cmdArgs[1:]...)

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
	messageChan := make(chan ExecMessage, 10)
	writerDone := make(chan struct{})

	// Writer goroutine - single point of writing to avoid races
	go func() {
		defer close(writerDone)
		for msg := range messageChan {
			if err := encoder.Encode(&msg); err != nil {
				s.logger.Error("Failed to encode message", "error", err)
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
			msg := ExecMessage{
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
			s.logger.Error("Error reading stdout", "error", err)
		}
	}()

	// Stream stderr
	go func() {
		defer func() { outputDone <- struct{}{} }()
		scanner := bufio.NewScanner(stderrPipe)
		for scanner.Scan() {
			msg := ExecMessage{
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
			s.logger.Error("Error reading stderr", "error", err)
		}
	}()

	// Wait for output goroutines to finish
	for i := 0; i < 2; i++ {
		<-outputDone
	}

	// Wait for command to finish
	err = cmd.Wait()

	// Send exit status
	exitMsg := ExecMessage{
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
		s.logger.Error("Failed to send exit message", "error", sendCtx.Err())
	}

	// Close message channel to signal writer to stop
	close(messageChan)

	// Wait for writer to finish
	<-writerDone
}

// handleProxy handles the /proxy endpoint (placeholder for now)
func (s *Server) handleProxy(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodConnect {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// TODO: Implement proxy functionality
	http.Error(w, "Proxy endpoint not yet implemented", http.StatusNotImplemented)
}
