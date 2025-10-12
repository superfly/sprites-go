package services

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// startService starts a service and its dependencies
func (m *Manager) startService(svc *Service, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	state, exists := states[svc.Name]
	if !exists {
		return fmt.Errorf("service state not found: %s", svc.Name)
	}

	// Check if already running
	if state.Status == StatusRunning {
		return nil
	}

	if state.Status == StatusStarting {
		return fmt.Errorf("service is already starting: %s", svc.Name)
	}

	// Start dependencies first
	for _, dep := range svc.Needs {
		depSvc, err := m.db.GetService(dep)
		if err != nil {
			return fmt.Errorf("failed to get dependency %s: %w", dep, err)
		}

		// Ensure dependency has a state entry
		if _, exists := states[depSvc.Name]; !exists {
			states[depSvc.Name] = &ServiceState{
				Name:   depSvc.Name,
				Status: StatusStopped,
			}
		}

		// Check if dependency is already running
		if states[depSvc.Name].Status != StatusRunning {
			tap.Logger(m.ctx).Info("starting dependency", "service", svc.Name, "dependency", dep)
			if err := m.startService(depSvc, states, processes); err != nil {
				return fmt.Errorf("failed to start dependency %s: %w", dep, err)
			}
		} else {
			tap.Logger(m.ctx).Info("dependency already running", "service", svc.Name, "dependency", dep)
		}
	}

	// Update state to starting
	state.Status = StatusStarting
	state.Error = ""

	// Start the process
	handle, err := m.startProcess(svc.Name, svc.Cmd, svc.Args)
	if err != nil {
		state.Status = StatusFailed
		state.Error = err.Error()
		return fmt.Errorf("failed to start process: %w", err)
	}

	// Update state to running
	state.Status = StatusRunning
	state.PID = handle.PID
	state.StartedAt = time.Now()
	processes[svc.Name] = handle

	tap.Logger(m.ctx).Info("service started", "name", svc.Name, "pid", handle.PID)

	// Monitor the process in a separate goroutine
	go m.monitorProcess(svc.Name, handle)

	return nil
}

// stopService stops a running service
func (m *Manager) stopService(name string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	state, exists := states[name]
	if !exists {
		return fmt.Errorf("service state not found: %s", name)
	}

	if state.Status != StatusRunning {
		return fmt.Errorf("service is not running: %s", name)
	}

	// Check if any other services depend on this one and are running
	for svcName, svcState := range states {
		if svcName == name {
			continue
		}
		if svcState.Status == StatusRunning || svcState.Status == StatusStarting {
			// Get the service to check its dependencies
			svc, err := m.db.GetService(svcName)
			if err != nil {
				continue
			}
			for _, dep := range svc.Needs {
				if dep == name {
					return fmt.Errorf("cannot stop service %s: service %s depends on it and is running", name, svcName)
				}
			}
		}
	}

	handle, exists := processes[name]
	if !exists {
		// Process handle missing, mark as stopped
		state.Status = StatusStopped
		state.PID = 0
		return nil
	}

	// Update state
	state.Status = StatusStopping

	// Send SIGTERM for graceful shutdown
	process, err := os.FindProcess(handle.PID)
	if err == nil {
		// Send SIGTERM
		if err := process.Signal(syscall.SIGTERM); err != nil {
			tap.Logger(m.ctx).Warn("failed to send SIGTERM", "name", name, "pid", handle.PID, "error", err)
		} else {
			tap.Logger(m.ctx).Info("sent SIGTERM", "name", name, "pid", handle.PID)
		}
	} else {
		tap.Logger(m.ctx).Warn("failed to find process", "name", name, "pid", handle.PID, "error", err)
	}

	tap.Logger(m.ctx).Info("service stop requested", "name", name, "pid", handle.PID)

	// Wait up to 1 second for graceful exit
	select {
	case <-handle.Done:
		tap.Logger(m.ctx).Info("service stopped gracefully", "name", name, "pid", handle.PID)
	case <-time.After(1 * time.Second):
		// Force kill
		tap.Logger(m.ctx).Warn("service did not stop gracefully, force killing", "name", name, "pid", handle.PID)
		if err := forceKillProcess(handle.PID); err != nil {
			tap.Logger(m.ctx).Error("failed to force kill process", "name", name, "pid", handle.PID, "error", err)
			return fmt.Errorf("failed to force kill process: %w", err)
		}
		// Wait a bit for the process to actually die
		select {
		case <-handle.Done:
			tap.Logger(m.ctx).Info("service force killed successfully", "name", name, "pid", handle.PID)
		case <-time.After(100 * time.Millisecond):
			tap.Logger(m.ctx).Error("process still running after force kill", "name", name, "pid", handle.PID)
		}
		// Cancel the context to clean up resources
		handle.Cancel()
	}

	return nil
}

// monitorProcess monitors a running process and updates state when it exits
func (m *Manager) monitorProcess(name string, handle *ProcessHandle) {
	// Wait for process to exit and get exit code
	<-handle.Done

	exitCode := 0
	select {
	case code := <-handle.ExitCode:
		exitCode = code
		// Store the exit code in the handle for later retrieval
		handle.SetExitCode(code)
	case <-time.After(100 * time.Millisecond):
		// Exit code not available after timeout
		exitCode = -1
	}

	// Send process exit notification through channel
	// Don't wait for result since we're in a goroutine
	select {
	case m.commands <- command{
		op:       opProcessExit,
		name:     name,
		exitCode: exitCode,
		result:   nil, // No result needed
	}:
	case <-m.ctx.Done():
		// Manager is shutting down
	}
}

// forceKillProcess sends SIGKILL to a process
func forceKillProcess(pid int) error {
	process, err := os.FindProcess(pid)
	if err != nil {
		return err
	}
	return process.Signal(syscall.SIGKILL)
}

// startProcess starts a process with optional prefix and logging
func (m *Manager) startProcess(name string, cmd string, args []string) (*ProcessHandle, error) {
	fullCmd := []string{cmd}
	fullCmd = append(fullCmd, args...)

	// If we have a prefix (like crun exec), prepend it
	if len(m.cmdPrefix) > 0 {
		fullCmd = append(m.cmdPrefix, fullCmd...)
	}

	logger := tap.Logger(m.ctx).With("service", name)
	logger.Info("starting service process", "cmd", cmd, "args", args, "full_command", fullCmd)

	// Create a context that we can cancel
	procCtx, cancel := context.WithCancel(m.ctx)
	command := exec.CommandContext(procCtx, fullCmd[0], fullCmd[1:]...)

	var stdoutLogger, stderrLogger *LineLogger
	// Set up logging if configured
	if m.logDir != "" {
		var err error
		stdoutLogger, stderrLogger, err = m.setupProcessLogging(command, name, logger, procCtx)
		if err != nil {
			cancel()
			return nil, fmt.Errorf("failed to setup logging: %w", err)
		}
	}

	// Start the command
	if err := command.Start(); err != nil {
		cancel()
		return nil, fmt.Errorf("failed to start command: %w", err)
	}

	// Create done and exit code channels
	done := make(chan struct{})
	exitCode := make(chan int, 1)

	// Monitor process exit
	go func() {
		err := command.Wait()
		code := 0
		if err != nil {
			if exitErr, ok := err.(*exec.ExitError); ok {
				code = exitErr.ExitCode()
			} else {
				code = -1
			}
		}
		exitCode <- code
		close(done)
	}()

	handle := &ProcessHandle{
		PID:      command.Process.Pid,
		Cancel:   cancel,
		Done:     done,
		ExitCode: exitCode,
	}

	// Set loggers if logging is enabled
	if stdoutLogger != nil {
		handle.stdoutLogger = stdoutLogger
		handle.stderrLogger = stderrLogger
	}

	return handle, nil
}

// setupProcessLogging sets up stdout/stderr logging to files
func (m *Manager) setupProcessLogging(cmd *exec.Cmd, name string, logger *slog.Logger, procCtx context.Context) (*LineLogger, *LineLogger, error) {
	stdoutPath := filepath.Join(m.logDir, "services", fmt.Sprintf("%s.log", name))
	stderrPath := filepath.Join(m.logDir, "services", fmt.Sprintf("%s.stderr.log", name))

	// Open or create stdout log file
	stdoutFile, err := openLogFile(stdoutPath)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to open stdout log: %w", err)
	}

	// Open or create stderr log file
	stderrFile, err := openLogFile(stderrPath)
	if err != nil {
		stdoutFile.Close()
		return nil, nil, fmt.Errorf("failed to open stderr log: %w", err)
	}

	// Create line loggers for structured logging
	stdoutLogger := &LineLogger{
		file: stdoutFile,
		logFunc: func(line string) {
			logger.Info(line)
		},
	}
	stderrLogger := &LineLogger{
		file: stderrFile,
		logFunc: func(line string) {
			logger.Error(line)
		},
	}

	// Use the line loggers which will write to file and log
	cmd.Stdout = stdoutLogger
	cmd.Stderr = stderrLogger

	// Track files to close when process exits
	go func() {
		<-procCtx.Done()
		// Give a moment for final writes
		time.Sleep(10 * time.Millisecond)
		stdoutLogger.Close()
		stderrLogger.Close()
		stdoutFile.Close()
		stderrFile.Close()
	}()

	return stdoutLogger, stderrLogger, nil
}

// LineLogger writes to a file and calls logFunc for each complete line
type LineLogger struct {
	file    *os.File
	buffer  []byte
	logFunc func(string)
	mu      sync.Mutex
	writers []io.Writer // Additional writers that can be attached/removed at runtime
}

func (l *LineLogger) Write(p []byte) (n int, err error) {
	l.mu.Lock()
	defer l.mu.Unlock()

	// Write to file immediately
	if _, err := l.file.Write(p); err != nil {
		return 0, err
	}

	// Write to all additional writers (ignore errors, as requested)
	for _, w := range l.writers {
		w.Write(p)
	}

	// Buffer for line processing
	l.buffer = append(l.buffer, p...)

	// Process complete lines for logging
	for {
		idx := indexByte(l.buffer, '\n')
		if idx < 0 {
			break
		}

		line := string(l.buffer[:idx])
		if line != "" {
			l.logFunc(line)
		}

		// Move remaining data to beginning
		l.buffer = l.buffer[idx+1:]
	}

	return len(p), nil
}

// Close flushes any remaining buffered data
func (l *LineLogger) Close() error {
	l.mu.Lock()
	defer l.mu.Unlock()

	if len(l.buffer) > 0 {
		l.logFunc(string(l.buffer))
		l.buffer = nil
	}
	return nil
}

// AttachWriter adds a new writer to receive output
func (l *LineLogger) AttachWriter(w io.Writer) {
	l.mu.Lock()
	defer l.mu.Unlock()
	l.writers = append(l.writers, w)
}

// RemoveWriter removes a writer from receiving output
func (l *LineLogger) RemoveWriter(w io.Writer) {
	l.mu.Lock()
	defer l.mu.Unlock()

	// Find and remove the writer
	for i, writer := range l.writers {
		if writer == w {
			l.writers = append(l.writers[:i], l.writers[i+1:]...)
			break
		}
	}
}

// indexByte finds the first instance of b in data
func indexByte(data []byte, b byte) int {
	for i, c := range data {
		if c == b {
			return i
		}
	}
	return -1
}

// openLogFile opens a log file, truncating it if it's larger than maxLogSize
func openLogFile(path string) (*os.File, error) {
	const maxLogSize = 1024 * 1024 // 1MB

	// Check if file exists and its size
	info, err := os.Stat(path)
	if err == nil && info.Size() > maxLogSize {
		// Truncate the file if it's too large
		return os.Create(path)
	}

	// Open for append, create if doesn't exist
	return os.OpenFile(path, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0644)
}
