package handlers

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"lib/api"
	"lib/stdcopy"
	"net/http"
	"os/exec"
	"strings"
	"sync"
	"time"
)

// Default container ID (since we only have one container)
const defaultContainerID = "sprite-container"

// HandleDockerExecCreate handles POST /containers/{id}/exec
func (h *Handlers) HandleDockerExecCreate(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req api.DockerExecCreateRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	// Validate command
	if len(req.Cmd) == 0 {
		http.Error(w, "Cmd array cannot be empty", http.StatusBadRequest)
		return
	}

	// Generate exec ID
	idBytes := make([]byte, 32)
	if _, err := rand.Read(idBytes); err != nil {
		http.Error(w, fmt.Sprintf("Failed to generate ID: %v", err), http.StatusInternalServerError)
		return
	}
	execID := hex.EncodeToString(idBytes)

	// Create exec instance
	instance := &ExecInstance{
		ID:          execID,
		Config:      req,
		Running:     false,
		ExitCode:    -1,
		ContainerID: defaultContainerID,
	}

	// Store instance
	h.execMutex.Lock()
	h.execInstances[execID] = instance
	h.execMutex.Unlock()

	// Return response
	resp := api.DockerExecCreateResponse{
		Id: execID,
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(resp)
}

// HandleDockerExecStart handles POST /exec/{id}/start
func (h *Handlers) HandleDockerExecStart(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Extract exec ID from path
	parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
	if len(parts) < 2 {
		http.Error(w, "Invalid path", http.StatusBadRequest)
		return
	}
	execID := parts[1]

	// Get exec instance
	h.execMutex.RLock()
	instance, exists := h.execInstances[execID]
	h.execMutex.RUnlock()

	if !exists {
		http.Error(w, "Exec instance not found", http.StatusNotFound)
		return
	}

	// Parse start request
	var req api.DockerExecStartRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	// Mark as running
	h.execMutex.Lock()
	instance.Running = true
	instance.StartTime = time.Now()
	h.execMutex.Unlock()

	if req.Detach {
		// Detached mode - start command in background and return immediately
		go func() {
			exitCode := h.runExecCommand(instance, nil, nil)
			h.execMutex.Lock()
			instance.Running = false
			instance.ExitCode = exitCode
			instance.EndTime = time.Now()
			h.execMutex.Unlock()
		}()

		// Return 200 OK with empty body for detached
		w.Header().Set("Content-Type", "application/json")
		w.Header().Set("Content-Length", "0")
		w.WriteHeader(http.StatusOK)
		return
	}

	// Attached mode - upgrade to raw stream
	// Check if client supports upgrade
	if r.Header.Get("Connection") != "Upgrade" || r.Header.Get("Upgrade") != "tcp" {
		// Fallback to regular streaming without upgrade
		h.handleAttachedExecWithoutUpgrade(w, r, instance)
		return
	}

	// Send 101 Switching Protocols response
	w.Header().Set("Content-Type", "application/vnd.docker.raw-stream")
	w.Header().Set("Connection", "Upgrade")
	w.Header().Set("Upgrade", "tcp")
	w.WriteHeader(http.StatusSwitchingProtocols)

	// Flush headers
	if f, ok := w.(http.Flusher); ok {
		f.Flush()
	}

	// Get the underlying connection
	hijacker, ok := w.(http.Hijacker)
	if !ok {
		// Fallback if hijacking not supported
		h.handleAttachedExecWithoutUpgrade(w, r, instance)
		return
	}

	conn, bufrw, err := hijacker.Hijack()
	if err != nil {
		h.logger.Error("Failed to hijack connection", "error", err)
		return
	}
	defer conn.Close()

	// Make sure any buffered data is flushed
	if err := bufrw.Flush(); err != nil {
		h.logger.Error("Failed to flush buffer", "error", err)
		return
	}

	// Run command and stream output
	exitCode := h.runExecCommandWithStream(instance, conn)

	// Update instance
	h.execMutex.Lock()
	instance.Running = false
	instance.ExitCode = exitCode
	instance.EndTime = time.Now()
	h.execMutex.Unlock()
}

// handleAttachedExecWithoutUpgrade handles attached exec when upgrade is not possible
func (h *Handlers) handleAttachedExecWithoutUpgrade(w http.ResponseWriter, r *http.Request, instance *ExecInstance) {
	// Set headers for streaming
	w.Header().Set("Content-Type", "application/vnd.docker.raw-stream")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Run command and stream output
	exitCode := h.runExecCommandWithStream(instance, w)

	// Update instance
	h.execMutex.Lock()
	instance.Running = false
	instance.ExitCode = exitCode
	instance.EndTime = time.Now()
	h.execMutex.Unlock()
}

// runExecCommandWithStream runs the exec command and streams output to the writer
func (h *Handlers) runExecCommandWithStream(instance *ExecInstance, w io.Writer) int {
	// Build command
	var cmdArgs []string
	if instance.Config.Tty && len(h.execTTYWrapperCommand) > 0 {
		cmdArgs = append(cmdArgs, h.execTTYWrapperCommand...)
		cmdArgs = append(cmdArgs, instance.Config.Cmd...)
	} else if len(h.execWrapperCommand) > 0 {
		cmdArgs = append(cmdArgs, h.execWrapperCommand...)
		cmdArgs = append(cmdArgs, instance.Config.Cmd...)
	} else {
		cmdArgs = instance.Config.Cmd
	}

	// Create command with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, cmdArgs[0], cmdArgs[1:]...)

	// Set up pipes
	stdoutPipe, err := cmd.StdoutPipe()
	if err != nil {
		h.logger.Error("Failed to create stdout pipe", "error", err)
		return -1
	}

	stderrPipe, err := cmd.StderrPipe()
	if err != nil {
		h.logger.Error("Failed to create stderr pipe", "error", err)
		return -1
	}

	// Start command
	if err := cmd.Start(); err != nil {
		h.logger.Error("Failed to start command", "error", err)
		return -1
	}

	// Update PID
	h.execMutex.Lock()
	instance.Pid = cmd.Process.Pid
	h.execMutex.Unlock()

	// Create multiplexing writers using stdcopy
	var wg sync.WaitGroup

	// Stream stdout
	if instance.Config.AttachStdout {
		wg.Add(1)
		go func() {
			defer wg.Done()
			stdoutWriter := stdcopy.NewStdWriter(w, stdcopy.Stdout)
			if _, err := io.Copy(stdoutWriter, stdoutPipe); err != nil {
				h.logger.Error("Failed to copy stdout", "error", err)
			}
		}()
	}

	// Stream stderr
	if instance.Config.AttachStderr {
		wg.Add(1)
		go func() {
			defer wg.Done()
			stderrWriter := stdcopy.NewStdWriter(w, stdcopy.Stderr)
			if _, err := io.Copy(stderrWriter, stderrPipe); err != nil {
				h.logger.Error("Failed to copy stderr", "error", err)
			}
		}()
	}

	// Wait for output to complete
	wg.Wait()

	// Wait for command to finish
	err = cmd.Wait()
	exitCode := 0
	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			exitCode = exitErr.ExitCode()
		} else {
			exitCode = -1
		}
	}

	return exitCode
}

// runExecCommand runs the exec command without streaming (for detached mode)
func (h *Handlers) runExecCommand(instance *ExecInstance, stdout, stderr io.Writer) int {
	// Build command
	var cmdArgs []string
	if instance.Config.Tty && len(h.execTTYWrapperCommand) > 0 {
		cmdArgs = append(cmdArgs, h.execTTYWrapperCommand...)
		cmdArgs = append(cmdArgs, instance.Config.Cmd...)
	} else if len(h.execWrapperCommand) > 0 {
		cmdArgs = append(cmdArgs, h.execWrapperCommand...)
		cmdArgs = append(cmdArgs, instance.Config.Cmd...)
	} else {
		cmdArgs = instance.Config.Cmd
	}

	// Create command with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, cmdArgs[0], cmdArgs[1:]...)
	if stdout != nil {
		cmd.Stdout = stdout
	}
	if stderr != nil {
		cmd.Stderr = stderr
	}

	// Start and wait
	if err := cmd.Start(); err != nil {
		return -1
	}

	// Update PID
	h.execMutex.Lock()
	instance.Pid = cmd.Process.Pid
	h.execMutex.Unlock()

	err := cmd.Wait()
	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return exitErr.ExitCode()
		}
		return -1
	}
	return 0
}

// HandleDockerExecInspect handles GET /exec/{id}/json
func (h *Handlers) HandleDockerExecInspect(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Extract exec ID from path
	parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
	if len(parts) < 2 {
		http.Error(w, "Invalid path", http.StatusBadRequest)
		return
	}
	execID := parts[1]

	// Get exec instance
	h.execMutex.RLock()
	instance, exists := h.execInstances[execID]
	h.execMutex.RUnlock()

	if !exists {
		http.Error(w, "Exec instance not found", http.StatusNotFound)
		return
	}

	// Build response
	resp := api.DockerExecInspectResponse{
		Id:       instance.ID,
		Running:  instance.Running,
		ExitCode: instance.ExitCode,
		ProcessConfig: api.DockerProcessConfig{
			Entrypoint: instance.Config.Cmd[0],
			Arguments:  instance.Config.Cmd[1:],
			Privileged: instance.Config.Privileged,
			Tty:        instance.Config.Tty,
			User:       instance.Config.User,
		},
		OpenStdin:   instance.Config.AttachStdin,
		OpenStderr:  instance.Config.AttachStderr,
		OpenStdout:  instance.Config.AttachStdout,
		CanRemove:   !instance.Running,
		ContainerID: instance.ContainerID,
		DetachKeys:  instance.Config.DetachKeys,
		Pid:         instance.Pid,
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(resp)
}
