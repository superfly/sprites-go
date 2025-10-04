package api

import (
	"context"
	"encoding/json"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"time"

	"github.com/superfly/sprite-env/pkg/services"
)

// logEventWriter implements io.Writer to capture output and send as log events
type logEventWriter struct {
	logType string
	events  chan<- ServiceLogEvent
}

func (w *logEventWriter) Write(p []byte) (n int, err error) {
	// Send the data as a log event
	event := ServiceLogEvent{
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

// streamServiceExecution starts a service and streams its logs for the specified duration
func streamServiceExecution(
	servicesManager *services.Manager,
	logDir string,
	w http.ResponseWriter,
	name string,
	duration time.Duration,
	flusher http.Flusher,
	logger *slog.Logger,
) {
	// Create context for the monitoring duration
	ctx, cancel := context.WithTimeout(context.Background(), duration)
	defer cancel()

	// Channel to collect events
	events := make(chan ServiceLogEvent, 100)
	encoder := json.NewEncoder(w)

	// First start the service
	err := servicesManager.StartService(name)
	if err != nil {
		// Send error event directly
		event := ServiceLogEvent{
			Type:      "error",
			Data:      fmt.Sprintf("Failed to start service: %v", err),
			Timestamp: time.Now().UnixMilli(),
		}
		encoder.Encode(event)
		flusher.Flush()

		// Send exit event with non-zero code
		exitCode := 1
		exitEvent := ServiceLogEvent{
			Type:      "exit",
			ExitCode:  &exitCode,
			Timestamp: time.Now().UnixMilli(),
		}
		encoder.Encode(exitEvent)
		flusher.Flush()

		// Send completion event
		sendCompletionEvent(encoder, name, logDir)
		flusher.Flush()
		return
	}

	// Service started - send started event immediately
	startEvent := ServiceLogEvent{
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
		err := servicesManager.WaitForStop(name, duration)
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
			state, _ := servicesManager.GetServiceState(name)
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
				stdoutPath := filepath.Join(logDir, "services", fmt.Sprintf("%s.log", name))
				if content, err := os.ReadFile(stdoutPath); err == nil && len(content) > 0 {
					event := ServiceLogEvent{
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
				stderrPath := filepath.Join(logDir, "services", fmt.Sprintf("%s.stderr.log", name))
				if content, err := os.ReadFile(stderrPath); err == nil && len(content) > 0 {
					event := ServiceLogEvent{
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
			event := ServiceLogEvent{
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
					state, err := servicesManager.GetServiceState(name)
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
						event := ServiceLogEvent{
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
				sendCompletionEvent(encoder, name, logDir)
				flusher.Flush()
				return
			}
			// Send event
			if err := encoder.Encode(event); err != nil {
				return
			}
			flusher.Flush()
			if event.Type == "exit" {
				drainAndComplete(events, encoder, flusher, name, logDir)
				return
			}
		case <-attachTimeout:
			// Timeout trying to attach - read any accumulated logs
			if !handleAttached {
				stdoutPath := filepath.Join(logDir, "services", fmt.Sprintf("%s.log", name))
				if data, err := os.ReadFile(stdoutPath); err == nil && len(data) > 0 {
					event := ServiceLogEvent{
						Type:      "stdout",
						Data:      string(data),
						Timestamp: time.Now().UnixMilli(),
					}
					encoder.Encode(event)
					flusher.Flush()
					lastStdoutPos = int64(len(data))
				}

				stderrPath := filepath.Join(logDir, "services", fmt.Sprintf("%s.stderr.log", name))
				if data, err := os.ReadFile(stderrPath); err == nil && len(data) > 0 {
					event := ServiceLogEvent{
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
				handle, err := servicesManager.GetProcessHandle(name)
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
				stdoutPath := filepath.Join(logDir, "services", fmt.Sprintf("%s.log", name))
				if data, err := os.ReadFile(stdoutPath); err == nil && len(data) > 0 {
					event := ServiceLogEvent{
						Type:      "stdout",
						Data:      string(data),
						Timestamp: time.Now().UnixMilli(),
					}
					encoder.Encode(event)
					flusher.Flush()
				}

				stderrPath := filepath.Join(logDir, "services", fmt.Sprintf("%s.stderr.log", name))
				if data, err := os.ReadFile(stderrPath); err == nil && len(data) > 0 {
					event := ServiceLogEvent{
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
			sendCompletionEvent(encoder, name, logDir)
			flusher.Flush()
			return
		case event, ok := <-events:
			if !ok {
				// Channel closed, done
				sendCompletionEvent(encoder, name, logDir)
				flusher.Flush()
				return
			}
			if err := encoder.Encode(event); err != nil {
				return
			}
			flusher.Flush()

			if event.Type == "exit" {
				drainAndComplete(events, encoder, flusher, name, logDir)
				return
			}
		}
	}
}

func drainAndComplete(events <-chan ServiceLogEvent, encoder *json.Encoder, flusher http.Flusher, name string, logDir string) {
	// Wait a bit more for any final output after exit
	finalWait := time.After(200 * time.Millisecond)
	for {
		select {
		case <-finalWait:
			// Final wait complete, send completion and exit
			sendCompletionEvent(encoder, name, logDir)
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
				sendCompletionEvent(encoder, name, logDir)
				flusher.Flush()
				return
			default:
				// Continue draining
				time.Sleep(10 * time.Millisecond)
			}
		}
	}
}

// sendCompletionEvent sends a completion event with log file locations
func sendCompletionEvent(encoder *json.Encoder, serviceName string, logDir string) {
	event := ServiceLogEvent{
		Type:      "complete",
		Timestamp: time.Now().UnixMilli(),
		LogFiles: map[string]string{
			"stdout": fmt.Sprintf("%s/services/%s.log", logDir, serviceName),
			"stderr": fmt.Sprintf("%s/services/%s.stderr.log", logDir, serviceName),
		},
	}
	encoder.Encode(event)
}
