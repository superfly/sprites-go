package juicefs

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"regexp"
	"strings"
	"sync"
	"time"
)

// OutputWatcher monitors JuiceFS stdout/stderr for ready signals and errors
type OutputWatcher struct {
	logger       *slog.Logger
	mountPath    string
	readyCh      chan struct{}
	errorCh      chan error
	readyOnce    sync.Once
	outputBuffer []string
	bufferMu     sync.Mutex
	structured   io.Writer
}

// NewOutputWatcher creates a new output watcher
func NewOutputWatcher(logger *slog.Logger, mountPath string, structured io.Writer) *OutputWatcher {
	return &OutputWatcher{
		logger:       logger,
		mountPath:    mountPath,
		readyCh:      make(chan struct{}),
		errorCh:      make(chan error, 1),
		outputBuffer: make([]string, 0, 100),
		structured:   structured,
	}
}

// Watch starts watching stdout and stderr for ready signals
func (w *OutputWatcher) Watch(stdout, stderr io.ReadCloser) {
	// Start goroutines to read from both streams
	go w.watchStream(stdout, "stdout")
	go w.watchStream(stderr, "stderr")
}

// WaitForReady waits for JuiceFS to be ready or timeout
func (w *OutputWatcher) WaitForReady(ctx context.Context, verifyFn func() bool) error {
	ticker := time.NewTicker(500 * time.Millisecond)
	defer ticker.Stop()

	readySignalReceived := false

	for {
		select {
		case <-w.readyCh:
			// Ready signal detected, verify mount is actually ready
			if verifyFn != nil && verifyFn() {
				w.logger.Info("JuiceFS mount verified as ready")
				return nil
			}
			// If verification fails, log once and continue with periodic checks
			if !readySignalReceived {
				w.logger.Warn("JuiceFS ready signal received but mount verification failed, continuing to wait")
				readySignalReceived = true
			}
			// Don't select on readyCh again since it's closed

		case err := <-w.errorCh:
			return fmt.Errorf("JuiceFS mount error: %w", err)

		case <-ticker.C:
			// Periodic check in case we missed the log message or verification wasn't ready yet
			if verifyFn != nil && verifyFn() {
				w.logger.Info("JuiceFS mount detected as ready (no log signal)")
				w.signalReady()
				return nil
			}

		case <-ctx.Done():
			// Dump recent output for debugging
			w.bufferMu.Lock()
			if len(w.outputBuffer) > 0 {
				w.logger.Info("Recent JuiceFS output before timeout:",
					"lines", len(w.outputBuffer),
					"output", strings.Join(w.outputBuffer, "\n"))
			}
			w.bufferMu.Unlock()
			return ctx.Err()
		}

		// If ready signal was received, only check ticker and context from now on
		if readySignalReceived {
			select {
			case err := <-w.errorCh:
				return fmt.Errorf("JuiceFS mount error: %w", err)

			case <-ticker.C:
				if verifyFn != nil && verifyFn() {
					w.logger.Info("JuiceFS mount detected as ready (no log signal)")
					w.signalReady()
					return nil
				}

			case <-ctx.Done():
				w.bufferMu.Lock()
				if len(w.outputBuffer) > 0 {
					w.logger.Info("Recent JuiceFS output before timeout:",
						"lines", len(w.outputBuffer),
						"output", strings.Join(w.outputBuffer, "\n"))
				}
				w.bufferMu.Unlock()
				return ctx.Err()
			}
		}
	}
}

// watchStream monitors a single output stream
func (w *OutputWatcher) watchStream(stream io.ReadCloser, streamName string) {
	defer stream.Close()
	scanner := bufio.NewScanner(stream)

	// Split on either \n or \r to stream progress updates immediately
	scanner.Split(func(data []byte, atEOF bool) (advance int, token []byte, err error) {
		if atEOF && len(data) == 0 {
			return 0, nil, nil
		}
		// Look for \n or \r
		if i := strings.IndexAny(string(data), "\n\r"); i >= 0 {
			// Found a delimiter, return everything before it
			return i + 1, data[0:i], nil
		}
		// If at EOF, return remaining data
		if atEOF {
			return len(data), data, nil
		}
		// Request more data
		return 0, nil, nil
	})

	for scanner.Scan() {
		line := scanner.Text()

		// Skip empty or whitespace-only lines (from \r sequences used to clear progress)
		if strings.TrimSpace(line) == "" {
			continue
		}

		// Store in buffer for debugging
		w.bufferMu.Lock()
		w.outputBuffer = append(w.outputBuffer, fmt.Sprintf("[%s] %s", streamName, line))
		if len(w.outputBuffer) > 100 {
			// Keep only last 100 lines
			w.outputBuffer = w.outputBuffer[len(w.outputBuffer)-100:]
		}
		w.bufferMu.Unlock()

		// Try JSON parse first; if it parses, we will not emit a duplicate raw debug line
		var parsed map[string]any
		parsedOK := json.Unmarshal([]byte(line), &parsed) == nil && len(parsed) > 0
		if !parsedOK {
			w.logger.Debug(fmt.Sprintf("[JuiceFS %s]", streamName), "line", line)
		}

		// Forward as structured JSON if configured
		if w.structured != nil {
			// If the line itself is JSON, use the parsed object; otherwise forward as plain text
			if parsedOK {
				// Extract level and message from known keys
				levelVal := "info"
				if v, ok := parsed["level"].(string); ok && v != "" {
					levelVal = strings.ToLower(v)
				} else if v, ok := parsed["severity"].(string); ok && v != "" {
					levelVal = strings.ToLower(v)
				}
				msgVal := ""
				if v, ok := parsed["msg"].(string); ok {
					msgVal = v
					delete(parsed, "msg")
				} else if v, ok := parsed["message"].(string); ok {
					msgVal = v
					delete(parsed, "message")
				}
				// Remove level/severity keys if present
				delete(parsed, "level")
				delete(parsed, "severity")
				// Remove source to avoid duplication (logger already has source=juicefs)
				delete(parsed, "source")
				// Build event with remaining attributes flattened
				evt := map[string]any{
					"level":  levelVal,
					"msg":    msgVal,
					"stream": streamName,
				}
				for k, v := range parsed {
					// Preserve additional fields from JuiceFS JSON (e.g., file, line, method, pid, time)
					evt[k] = v
				}
				if b, err := json.Marshal(evt); err == nil {
					_, _ = w.structured.Write(append(b, '\n'))
				}
			} else {
				// Plain text line: map to level by heuristic and forward
				level := "info"
				if w.isErrorMessage(line) {
					level = "error"
				}
				evt := map[string]any{
					"level":  level,
					"msg":    line,
					"stream": streamName,
				}
				if b, err := json.Marshal(evt); err == nil {
					_, _ = w.structured.Write(append(b, '\n'))
				}
			}
		}

		// Check for ready indicators
		if w.isReadyMessage(line) {
			w.logger.Info("JuiceFS ready signal detected",
				"stream", streamName,
				"line", line)
			w.signalReady()
			return
		}

		// Check for error indicators
		if w.isErrorMessage(line) {
			w.logger.Error("JuiceFS error detected",
				"stream", streamName,
				"line", line)
			select {
			case w.errorCh <- fmt.Errorf("%s: %s", streamName, line):
			default:
			}
		}
	}

	if err := scanner.Err(); err != nil {
		w.logger.Warn("Error reading JuiceFS output",
			"stream", streamName,
			"error", err)
	}

	// Do not close structured writer here; shared between streams
}

// isReadyMessage checks if a log line indicates JuiceFS is ready
func (w *OutputWatcher) isReadyMessage(line string) bool {
	// We only consider the explicit JuiceFS readiness message emitted by checkMountpoint:
	//   "OK, <VOLUME_NAME> is ready at <mountPath>"
	// Message may contain ANSI color codes; strip them before matching.

	stripANSI := func(s string) string {
		// Matches ESC[...m sequences
		ansiRegexp := regexp.MustCompile(`\x1b\[[0-9;]*m`)
		return ansiRegexp.ReplaceAllString(s, "")
	}

	// Try to parse JSON line and inspect the msg/method/file fields
	var parsed map[string]any
	if err := json.Unmarshal([]byte(line), &parsed); err == nil && len(parsed) > 0 {
		msg, _ := parsed["msg"].(string)
		if msg == "" {
			msg, _ = parsed["message"].(string)
		}
		msg = stripANSI(msg)
		msgLower := strings.ToLower(msg)

		// Ensure the canonical readiness phrase and the mountPath are present
		if strings.Contains(msgLower, "ok,") && strings.Contains(msgLower, " is ready at ") && strings.Contains(msg, w.mountPath) {
			// Prefer when method indicates the source is checkMountpoint, but don't require it
			if m, ok := parsed["method"].(string); ok && m == "checkMountpoint" {
				return true
			}
			if f, ok := parsed["file"].(string); ok && f == "mount_unix.go" {
				return true
			}
			return true
		}
		return false
	}

	// Fallback: treat as plain text
	lineStripped := stripANSI(line)
	lower := strings.ToLower(lineStripped)
	return strings.Contains(lower, "ok,") && strings.Contains(lower, " is ready at ") && strings.Contains(lineStripped, w.mountPath)
}

// isErrorMessage checks if a log line indicates an error
func (w *OutputWatcher) isErrorMessage(line string) bool {
	// Skip certain non-critical "errors"
	if strings.Contains(line, "error reading /proc/") {
		return false
	}
	if strings.Contains(line, "Failed to open /proc/") {
		return false
	}

	lineLower := strings.ToLower(line)
	errorIndicators := []string{
		"error:",
		"fatal:",
		"failed:",
		"cannot ",
		"unable to",
		"permission denied",
		"no such file",
		"connection refused",
		"timeout",
	}

	for _, indicator := range errorIndicators {
		if strings.Contains(lineLower, indicator) {
			return true
		}
	}

	return false
}

// signalReady signals that JuiceFS is ready
func (w *OutputWatcher) signalReady() {
	w.readyOnce.Do(func() {
		close(w.readyCh)
	})
}
