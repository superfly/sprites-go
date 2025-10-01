package system

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tap"
)

// SockServer handles the Unix socket API for service management
type SockServer struct {
	system   *System
	listener net.Listener
	server   *http.Server
	ctx      context.Context
	logDir   string // Base directory for service logs
}

// ServiceRequest represents the request body for creating/updating services
type ServiceRequest struct {
	Cmd   string   `json:"cmd"`
	Args  []string `json:"args"`
	Needs []string `json:"needs"`
}

// ServiceSignalRequest represents the request body for signaling services
type ServiceSignalRequest struct {
	Name   string `json:"name"`
	Signal string `json:"signal"`
}

// NewSockServer creates a new Unix socket server
func NewSockServer(ctx context.Context, system *System, logDir string) (*SockServer, error) {
	return &SockServer{
		system: system,
		ctx:    ctx,
		logDir: logDir,
	}, nil
}

// Start starts the Unix socket server
func (s *SockServer) Start(socketPath string) error {
	// Remove existing socket if it exists
	if err := os.RemoveAll(socketPath); err != nil {
		return fmt.Errorf("failed to remove existing socket: %w", err)
	}

	// Ensure directory exists
	if err := os.MkdirAll(filepath.Dir(socketPath), 0755); err != nil {
		return fmt.Errorf("failed to create socket directory: %w", err)
	}

	// Create Unix socket listener
	listener, err := net.Listen("unix", socketPath)
	if err != nil {
		return fmt.Errorf("failed to create unix socket: %w", err)
	}
	s.listener = listener

	// Set socket permissions
	if err := os.Chmod(socketPath, 0666); err != nil {
		listener.Close()
		return fmt.Errorf("failed to set socket permissions: %w", err)
	}

	// Create HTTP server with routes
	mux := http.NewServeMux()
	s.setupRoutes(mux)

	s.server = &http.Server{
		Handler:     mux,
		ReadTimeout: 30 * time.Second,
	}

	// Start serving
	go func() {
		if err := s.server.Serve(listener); err != nil && err != http.ErrServerClosed {
			tap.Logger(s.ctx).Error("socket server error", "error", err)
		}
	}()

	tap.Logger(s.ctx).Info("services API socket server started", "path", socketPath)
	return nil
}

// Stop stops the Unix socket server
func (s *SockServer) Stop() error {
	if s.server != nil {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		if err := s.server.Shutdown(ctx); err != nil {
			return fmt.Errorf("failed to shutdown server: %w", err)
		}
	}

	return nil
}

func (s *SockServer) setupRoutes(mux *http.ServeMux) {
	// List services
	mux.HandleFunc("GET /v1/services", s.handleListServices)

	// Create service
	mux.HandleFunc("PUT /v1/services/{name}", s.handleCreateService)

	// Get service state
	mux.HandleFunc("GET /v1/services/{name}", s.handleGetService)

	// Delete service
	mux.HandleFunc("DELETE /v1/services/{name}", s.handleDeleteService)

	// Signal service
	mux.HandleFunc("POST /v1/services/signal", s.handleSignalService)
}

func (s *SockServer) handleListServices(w http.ResponseWriter, r *http.Request) {
	svcList, err := s.system.ServicesManager.ListServices()
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	// Get states for all services
	type serviceWithState struct {
		*services.Service
		State *services.ServiceState `json:"state,omitempty"`
	}

	result := make([]serviceWithState, len(svcList))
	for i, svc := range svcList {
		state, _ := s.system.ServicesManager.GetServiceState(svc.Name)
		result[i] = serviceWithState{
			Service: svc,
			State:   state,
		}
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

func (s *SockServer) handleCreateService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	var req ServiceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "invalid request body", http.StatusBadRequest)
		return
	}

	// Validate required fields
	if req.Cmd == "" {
		http.Error(w, "cmd field is required", http.StatusBadRequest)
		return
	}

	// Parse monitoring duration from query parameter (default to 5 seconds)
	duration := 5 * time.Second
	if durationStr := r.URL.Query().Get("duration"); durationStr != "" {
		if d, err := time.ParseDuration(durationStr); err == nil && d > 0 {
			duration = d
		}
	}
	// Also support "timeout" for backwards compatibility
	if durationStr := r.URL.Query().Get("timeout"); durationStr != "" {
		if d, err := time.ParseDuration(durationStr); err == nil && d > 0 {
			duration = d
		}
	}

	svc := &services.Service{
		Name:  name,
		Cmd:   req.Cmd,
		Args:  req.Args,
		Needs: req.Needs,
	}

	// Create the service without starting it
	if err := s.system.ServicesManager.CreateService(svc); err != nil {
		if strings.Contains(err.Error(), "dependency") || strings.Contains(err.Error(), "circular") {
			http.Error(w, err.Error(), http.StatusBadRequest)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// Set up streaming response headers
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Enable flushing
	flusher, ok := w.(http.Flusher)
	if !ok {
		// Fall back to non-streaming response
		event := LogEvent{
			Type:      "error",
			Data:      "streaming not supported",
			Timestamp: time.Now().UnixMilli(),
		}
		json.NewEncoder(w).Encode(event)
		return
	}

	// Start the service and stream logs for the duration
	s.streamServiceExecution(w, name, duration, flusher)
}

func (s *SockServer) handleGetService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	svc, err := s.system.ServicesManager.GetService(name)
	if err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	state, _ := s.system.ServicesManager.GetServiceState(name)

	result := struct {
		*services.Service
		State *services.ServiceState `json:"state,omitempty"`
	}{
		Service: svc,
		State:   state,
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

func (s *SockServer) handleDeleteService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	// Delete the service (which stops it)
	if err := s.system.ServicesManager.DeleteService(name); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else if strings.Contains(err.Error(), "running") || strings.Contains(err.Error(), "depends") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// Wait for the service to stop (max 10 seconds)
	if err := s.system.ServicesManager.WaitForStop(name, 10*time.Second); err != nil {
		tap.Logger(s.ctx).Warn("service did not stop within timeout", "name", name, "error", err)
		// Don't fail the request - the delete was successful
	}

	w.WriteHeader(http.StatusNoContent)
}

func (s *SockServer) handleSignalService(w http.ResponseWriter, r *http.Request) {
	var req ServiceSignalRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "invalid request body", http.StatusBadRequest)
		return
	}

	// Validate request
	if req.Name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}
	if req.Signal == "" {
		http.Error(w, "signal required", http.StatusBadRequest)
		return
	}

	// Send the signal
	if err := s.system.ServicesManager.SignalService(req.Name, req.Signal); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else if strings.Contains(err.Error(), "not running") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else if strings.Contains(err.Error(), "invalid signal") || strings.Contains(err.Error(), "unknown signal") {
			http.Error(w, err.Error(), http.StatusBadRequest)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// For TERM and KILL signals, wait for the process to stop
	if strings.ToUpper(req.Signal) == "TERM" || strings.ToUpper(req.Signal) == "SIGTERM" ||
		strings.ToUpper(req.Signal) == "KILL" || strings.ToUpper(req.Signal) == "SIGKILL" {
		// Wait for the service to stop (max 10 seconds)
		if err := s.system.ServicesManager.WaitForStop(req.Name, 10*time.Second); err != nil {
			tap.Logger(s.ctx).Warn("service did not stop within timeout after signal", "name", req.Name, "signal", req.Signal, "error", err)
			// Don't fail the request - the signal was sent successfully
		}
	}

	w.WriteHeader(http.StatusNoContent)
}

// LogEvent represents a log event in NDJSON format
type LogEvent struct {
	Type      string            `json:"type"` // "stdout", "stderr", "exit", "error", "complete"
	Data      string            `json:"data,omitempty"`
	ExitCode  *int              `json:"exit_code,omitempty"`
	Timestamp int64             `json:"timestamp"`
	LogFiles  map[string]string `json:"log_files,omitempty"` // For "complete" event
}

// logEventWriter implements io.Writer to capture output and send as log events
type logEventWriter struct {
	logType string
	events  chan<- LogEvent
}

func (w *logEventWriter) Write(p []byte) (n int, err error) {
	// Send the data as a log event
	event := LogEvent{
		Type:      w.logType,
		Data:      string(p),
		Timestamp: time.Now().UnixMilli(),
	}

	// Non-blocking send to avoid deadlock
	select {
	case w.events <- event:
	default:
		// Channel full, drop event
	}

	return len(p), nil
}

func (s *SockServer) streamServiceExecution(w http.ResponseWriter, name string, duration time.Duration, flusher http.Flusher) {
	// Create context for the monitoring duration
	ctx, cancel := context.WithTimeout(context.Background(), duration)
	defer cancel()

	// Channel to collect events
	events := make(chan LogEvent, 100)
	encoder := json.NewEncoder(w)

	// First start the service
	err := s.system.ServicesManager.StartService(name)
	if err != nil {
		// Send error event directly
		event := LogEvent{
			Type:      "error",
			Data:      fmt.Sprintf("Failed to start service: %v", err),
			Timestamp: time.Now().UnixMilli(),
		}
		encoder.Encode(event)
		flusher.Flush()

		// Send exit event with non-zero code
		exitCode := 1
		exitEvent := LogEvent{
			Type:      "exit",
			ExitCode:  &exitCode,
			Timestamp: time.Now().UnixMilli(),
		}
		encoder.Encode(exitEvent)
		flusher.Flush()

		// Send completion event
		s.sendCompletionEvent(encoder, name)
		flusher.Flush()
		return
	}

	// Service started - send started event immediately
	startEvent := LogEvent{
		Type:      "started",
		Data:      fmt.Sprintf("Service %s started", name),
		Timestamp: time.Now().UnixMilli(),
	}
	if err := encoder.Encode(startEvent); err != nil {
		return
	}
	flusher.Flush()

	// Channel to communicate if we attached writers
	attachedChan := make(chan bool, 1)

	// Now monitor the service in the background
	go func() {
		// Wait to see if service stops within the duration
		err := s.system.ServicesManager.WaitForStop(name, duration)
		serviceCompleted := err == nil // nil means it stopped, error means timeout

		// If service completed (stopped), handle it
		if serviceCompleted {
			// Give a small delay to ensure process output is fully written to files
			time.Sleep(50 * time.Millisecond)

			// Check if we attached writers
			wasAttached := false
			select {
			case wasAttached = <-attachedChan:
			default:
			}

			// Get exit code
			state, _ := s.system.ServicesManager.GetServiceState(name)
			exitCode := 0
			if state != nil && state.Status == services.StatusFailed && state.Error != "" {
				// Try to parse exit code from error message "exited with code X"
				var code int
				if _, err := fmt.Sscanf(state.Error, "exited with code %d", &code); err == nil {
					exitCode = code
				} else {
					exitCode = 1 // Default non-zero for failed status
				}
			}

			// Only read logs if we haven't been streaming
			// (i.e., process exited before we could attach writers)
			if !wasAttached {
				// Read stdout log
				stdoutPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.log", name))
				if content, err := os.ReadFile(stdoutPath); err == nil && len(content) > 0 {
					event := LogEvent{
						Type:      "stdout",
						Data:      string(content),
						Timestamp: time.Now().UnixMilli(),
					}
					select {
					case events <- event:
					case <-ctx.Done():
					}
				}

				// Read stderr log
				stderrPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.stderr.log", name))
				if content, err := os.ReadFile(stderrPath); err == nil && len(content) > 0 {
					event := LogEvent{
						Type:      "stderr",
						Data:      string(content),
						Timestamp: time.Now().UnixMilli(),
					}
					select {
					case events <- event:
					case <-ctx.Done():
					}
				}
			}

			// Send exit event
			event := LogEvent{
				Type:      "exit",
				ExitCode:  &exitCode,
				Timestamp: time.Now().UnixMilli(),
			}
			select {
			case events <- event:
			case <-ctx.Done():
			}

			// Close events channel to signal completion
			close(events)
			return
		}

		// Service is still running after monitoring duration - watch for exit
		// Start a goroutine to watch for service exit
		go func() {
			ticker := time.NewTicker(100 * time.Millisecond)
			defer ticker.Stop()

			for {
				select {
				case <-ticker.C:
					state, err := s.system.ServicesManager.GetServiceState(name)
					if err != nil || state == nil {
						// Service deleted or error
						close(events)
						return
					}

					if state.Status == services.StatusStopped || state.Status == services.StatusFailed {
						// Service has stopped
						exitCode := 0
						if state.Status == services.StatusFailed && state.Error != "" {
							// Try to parse exit code from error message "exited with code X"
							var code int
							if _, err := fmt.Sscanf(state.Error, "exited with code %d", &code); err == nil {
								exitCode = code
							} else {
								exitCode = 1 // Default non-zero for failed status
							}
						}

						// Send exit event
						event := LogEvent{
							Type:      "exit",
							ExitCode:  &exitCode,
							Timestamp: time.Now().UnixMilli(),
						}
						select {
						case events <- event:
						default:
						}

						// Close events channel
						close(events)
						return
					}
				case <-ctx.Done():
					// Context cancelled
					close(events)
					return
				}
			}
		}()
	}()

	// Track positions for avoiding duplicate reads
	lastStdoutPos := int64(0)
	lastStderrPos := int64(0)

	// Try to attach writers for streaming if service is still running
	handleAttached := false
	attachTimeout := time.After(1 * time.Second) // Reduced timeout for faster attachment

attachLoop:
	for {
		select {
		case event, ok := <-events:
			if !ok {
				// Channel closed, service completed
				s.sendCompletionEvent(encoder, name)
				flusher.Flush()
				return
			}
			// Send event
			if err := encoder.Encode(event); err != nil {
				return
			}
			flusher.Flush()
			if event.Type == "exit" {
				s.drainAndComplete(events, encoder, flusher, name)
				return
			}
		case <-attachTimeout:
			// Timeout trying to attach - read any accumulated logs
			if !handleAttached {
				stdoutPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.log", name))
				if data, err := os.ReadFile(stdoutPath); err == nil && len(data) > 0 {
					event := LogEvent{
						Type:      "stdout",
						Data:      string(data),
						Timestamp: time.Now().UnixMilli(),
					}
					encoder.Encode(event)
					flusher.Flush()
					lastStdoutPos = int64(len(data))
				}

				stderrPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.stderr.log", name))
				if data, err := os.ReadFile(stderrPath); err == nil && len(data) > 0 {
					event := LogEvent{
						Type:      "stderr",
						Data:      string(data),
						Timestamp: time.Now().UnixMilli(),
					}
					encoder.Encode(event)
					flusher.Flush()
					lastStderrPos = int64(len(data))
				}
			}
			break attachLoop
		default:
			if !handleAttached {
				// Try to get process handle
				handle, err := s.system.ServicesManager.GetProcessHandle(name)
				if err == nil && handle != nil {
					// Successfully got handle - attach writers for streaming
					stdoutWriter := &logEventWriter{
						logType: "stdout",
						events:  events,
					}
					stderrWriter := &logEventWriter{
						logType: "stderr",
						events:  events,
					}

					handle.AttachStdout(stdoutWriter)
					defer handle.RemoveStdout(stdoutWriter)
					handle.AttachStderr(stderrWriter)
					defer handle.RemoveStderr(stderrWriter)

					handleAttached = true
					// Notify monitoring goroutine that we attached
					select {
					case attachedChan <- true:
					default:
					}
				} else {
					// Wait a bit before retrying
					time.Sleep(20 * time.Millisecond)
				}
			} else {
				// Already attached, just wait for events
				time.Sleep(10 * time.Millisecond)
			}
		}
	}

	// Stream events until completion or timeout
	for {
		select {
		case <-ctx.Done():
			// Monitoring duration reached
			// If we never attached writers and never read logs, read them now
			if !handleAttached && lastStdoutPos == 0 && lastStderrPos == 0 {
				// Read all accumulated logs
				stdoutPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.log", name))
				if data, err := os.ReadFile(stdoutPath); err == nil && len(data) > 0 {
					event := LogEvent{
						Type:      "stdout",
						Data:      string(data),
						Timestamp: time.Now().UnixMilli(),
					}
					encoder.Encode(event)
					flusher.Flush()
				}

				stderrPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.stderr.log", name))
				if data, err := os.ReadFile(stderrPath); err == nil && len(data) > 0 {
					event := LogEvent{
						Type:      "stderr",
						Data:      string(data),
						Timestamp: time.Now().UnixMilli(),
					}
					encoder.Encode(event)
					flusher.Flush()
				}
			}
			// Note: If we were streaming via attached writers, we don't need to read anything
			// The attached writers already sent all the output
			s.sendCompletionEvent(encoder, name)
			flusher.Flush()
			return
		case event, ok := <-events:
			if !ok {
				// Channel closed, done
				s.sendCompletionEvent(encoder, name)
				flusher.Flush()
				return
			}
			if err := encoder.Encode(event); err != nil {
				return
			}
			flusher.Flush()

			if event.Type == "exit" {
				s.drainAndComplete(events, encoder, flusher, name)
				return
			}
		}
	}
}

func (s *SockServer) drainAndComplete(events <-chan LogEvent, encoder *json.Encoder, flusher http.Flusher, name string) {
	// Wait a bit more for any final output after exit
	finalWait := time.After(200 * time.Millisecond)
	for {
		select {
		case <-finalWait:
			// Final wait complete, send completion and exit
			s.sendCompletionEvent(encoder, name)
			flusher.Flush()
			return
		case finalEvent := <-events:
			// Send any remaining output events
			if finalEvent.Type == "stdout" || finalEvent.Type == "stderr" {
				if err := encoder.Encode(finalEvent); err != nil {
					return
				}
				flusher.Flush()
			}
		default:
			// No more events immediately available, check if final wait is done
			select {
			case <-finalWait:
				s.sendCompletionEvent(encoder, name)
				flusher.Flush()
				return
			default:
				// Continue draining
				time.Sleep(10 * time.Millisecond)
			}
		}
	}
}

// sendAccumulatedLogsFrom reads and sends logs from the given positions
func (s *SockServer) sendAccumulatedLogsFrom(encoder *json.Encoder, serviceName string, flusher http.Flusher, lastStdoutPos, lastStderrPos int64) {
	// Read stdout log from last position
	stdoutPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.log", serviceName))
	if file, err := os.Open(stdoutPath); err == nil {
		defer file.Close()
		if info, err := file.Stat(); err == nil && info.Size() > lastStdoutPos {
			// Seek to last read position
			file.Seek(lastStdoutPos, 0)
			// Read new content
			newContent := make([]byte, info.Size()-lastStdoutPos)
			if n, err := file.Read(newContent); err == nil && n > 0 {
				event := LogEvent{
					Type:      "stdout",
					Data:      string(newContent[:n]),
					Timestamp: time.Now().UnixMilli(),
				}
				encoder.Encode(event)
				flusher.Flush()
			}
		}
	}

	// Read stderr log from last position
	stderrPath := filepath.Join(s.logDir, "services", fmt.Sprintf("%s.stderr.log", serviceName))
	if file, err := os.Open(stderrPath); err == nil {
		defer file.Close()
		if info, err := file.Stat(); err == nil && info.Size() > lastStderrPos {
			// Seek to last read position
			file.Seek(lastStderrPos, 0)
			// Read new content
			newContent := make([]byte, info.Size()-lastStderrPos)
			if n, err := file.Read(newContent); err == nil && n > 0 {
				event := LogEvent{
					Type:      "stderr",
					Data:      string(newContent[:n]),
					Timestamp: time.Now().UnixMilli(),
				}
				encoder.Encode(event)
				flusher.Flush()
			}
		}
	}
}

// sendCompletionEvent sends a completion event with log file locations
func (s *SockServer) sendCompletionEvent(encoder *json.Encoder, serviceName string) {
	event := LogEvent{
		Type:      "complete",
		Timestamp: time.Now().UnixMilli(),
		LogFiles: map[string]string{
			"stdout": fmt.Sprintf("/.sprite/logs/services/%s.log", serviceName),
			"stderr": fmt.Sprintf("/.sprite/logs/services/%s.stderr.log", serviceName),
		},
	}
	encoder.Encode(event)
}

func (s *SockServer) tailLogFile(ctx context.Context, path string, logType string, events chan<- LogEvent) {
	// Wait a bit for log file to be created
	time.Sleep(50 * time.Millisecond)

	file, err := os.Open(path)
	if err != nil {
		// Log file might not exist yet if service hasn't started
		return
	}
	defer file.Close()

	// Seek to end of file to only get new content
	file.Seek(0, io.SeekEnd)

	reader := bufio.NewReader(file)
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			// Read new lines
			for {
				line, err := reader.ReadString('\n')
				if err == io.EOF {
					break
				}
				if err != nil {
					return
				}

				// Trim newline and send event
				line = strings.TrimSuffix(line, "\n")
				if line != "" {
					select {
					case events <- LogEvent{
						Type:      logType,
						Data:      line,
						Timestamp: time.Now().UnixMilli(),
					}:
					case <-ctx.Done():
						return
					}
				}
			}
		}
	}
}
