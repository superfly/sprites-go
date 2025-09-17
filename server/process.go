package main

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/fsnotify/fsnotify"
	"github.com/superfly/sprite-env/pkg/tap"
)

// StartProcess starts the configured process
func (s *System) StartProcess() error {
	s.processMu.Lock()
	defer s.processMu.Unlock()

	if s.processCmd != nil && s.processCmd.Process != nil {
		return fmt.Errorf("process already started")
	}

	if len(s.config.ProcessCommand) == 0 {
		return fmt.Errorf("no process command configured")
	}

	// Determine working directory
	workingDir := s.config.ProcessWorkingDir
	if workingDir == "" {
		workingDir = "/dev/fly_vol"
		s.logger.Info("No working directory specified, using default", "workingDir", workingDir)
	}

	// Check if we're running crun and need to add --pid-file
	pidFile := ""
	cmd := s.config.ProcessCommand[0]
	args := s.config.ProcessCommand[1:]

	// Check if the command is crun or if launch.sh is being used (which internally uses crun)
	isCrun := strings.HasSuffix(cmd, "crun") || (strings.HasSuffix(cmd, "launch.sh") && len(args) == 0)

	if isCrun {
		// Generate a unique PID file path
		pidFile = filepath.Join("/tmp", fmt.Sprintf("sprite-crun-%d.pid", time.Now().UnixNano()))

		// If it's direct crun, add --pid-file
		if strings.HasSuffix(cmd, "crun") {
			// Find where to insert --pid-file (before "run" subcommand)
			runIndex := -1
			for i, arg := range args {
				if arg == "run" {
					runIndex = i
					break
				}
			}

			if runIndex >= 0 {
				// Insert --pid-file before "run"
				newArgs := make([]string, 0, len(args)+2)
				newArgs = append(newArgs, args[:runIndex]...)
				newArgs = append(newArgs, "--pid-file", pidFile)
				newArgs = append(newArgs, args[runIndex:]...)
				args = newArgs
			}
		} else if strings.HasSuffix(cmd, "launch.sh") {
			// For launch.sh, we need to set an environment variable
			// that the script can use to pass to crun
			s.config.ProcessEnvironment = append(s.config.ProcessEnvironment,
				fmt.Sprintf("CRUN_PID_FILE=%s", pidFile))
		}
	}

	// Prepare the command
	processCmd := exec.Command(cmd, args...)
	processCmd.Dir = workingDir
	processCmd.Env = append(os.Environ(), s.config.ProcessEnvironment...)

	// Set process group for signal forwarding
	processCmd.SysProcAttr = &syscall.SysProcAttr{
		Setpgid: true,
	}

	// Set up output capturing for crash reporting
	var stdoutBuffer, stderrBuffer *tap.CircularBuffer
	if s.crashReporter != nil {
		// Create circular buffers to capture recent output (32KB each)
		stdoutBuffer = tap.NewCircularBuffer(32 * 1024)
		stderrBuffer = tap.NewCircularBuffer(32 * 1024)
	}

	// Set up stdout - write to parent stdout and optional buffer
	stdoutWriters := []io.Writer{os.Stdout}
	if stdoutBuffer != nil {
		stdoutWriters = append(stdoutWriters, stdoutBuffer)
	}
	processCmd.Stdout = io.MultiWriter(stdoutWriters...)

	// Set up stderr - write to parent stderr and optional buffer
	stderrWriters := []io.Writer{os.Stderr}
	if stderrBuffer != nil {
		stderrWriters = append(stderrWriters, stderrBuffer)
	}
	processCmd.Stderr = io.MultiWriter(stderrWriters...)

	// Connect stdin
	processCmd.Stdin = os.Stdin

	// If we're using crun with a PID file, set up monitoring BEFORE starting the process
	var pidFileWatcher *pidFileMonitor
	if pidFile != "" {
		monitor, err := s.setupPIDFileMonitor(pidFile)
		if err != nil {
			return fmt.Errorf("failed to set up PID file monitor: %w", err)
		}
		pidFileWatcher = monitor
		defer monitor.cleanup()
	}

	// Start the process
	if err := processCmd.Start(); err != nil {
		return fmt.Errorf("failed to start process: %w", err)
	}

	s.processCmd = processCmd
	s.processStartTime = time.Now()

	s.logger.Info("Process started",
		"pid", processCmd.Process.Pid,
		"command", s.config.ProcessCommand,
		"pidFile", pidFile)

	// If we're using crun with a PID file, wait for it to be written
	if pidFileWatcher != nil {
		// Create a context that we can cancel if process exits
		ctx, cancel := context.WithCancel(context.Background())
		defer cancel()

		// Monitor for process exit in background
		// We need a separate channel to know when the process exits
		processDone := make(chan error, 1)
		go func() {
			err := processCmd.Wait()
			processDone <- err
		}()
		s.processWaitStarted = true

		// Create a channel to signal early exit
		processExited := make(chan bool, 1)
		go func() {
			select {
			case err := <-processDone:
				s.logger.Info("Process exited early", "pid", processCmd.Process.Pid, "error", err)
				processExited <- true
			case <-ctx.Done():
				s.logger.Debug("Process exit monitor cancelled")
			}
		}()

		// Wait for either PID file or process exit
		select {
		case result := <-pidFileWatcher.wait():
			cancel() // Stop monitoring for process exit
			if result.err != nil {
				// Kill the process if we fail to get the PID
				processCmd.Process.Kill()
				return fmt.Errorf("failed to get crun PID: %w", result.err)
			}

			s.logger.Info("Crun container started successfully",
				"containerPID", result.containerPID,
				"initPID", result.initPID,
				"supervisorPID", processCmd.Process.Pid)

			// Process Wait() is already running, set up monitoring
			go func() {
				err := <-processDone
				processRuntime := time.Since(s.processStartTime)
				s.logger.Info("Process exited", "error", err, "runtime", processRuntime)
				s.generateCrashReport(err, processRuntime, stdoutBuffer, stderrBuffer)
				s.processDoneCh <- err
				s.setState("processRunning", false)

				// Reset the wait flag under lock
				s.processMu.Lock()
				s.processWaitStarted = false
				s.processMu.Unlock()
			}()

		case <-processExited:
			cancel() // Stop waiting for PID file
			pidFileWatcher.cleanup()

			s.logger.Error("Process exited before PID file was written",
				"pid", processCmd.Process.Pid)

			// Process has already been waited on in the goroutine
			// We just need to mark that initialization failed
			s.processWaitStarted = false // Reset the flag
			return fmt.Errorf("process exited before initialization")
		}
	}

	// Mark process as running
	s.setState("processRunning", true)

	// Close the ready channel to unblock waiting requests
	close(s.processReadyCh)
	s.processReadyCh = make(chan struct{})

	// Monitor process in background
	// Only start monitoring if we haven't already started waiting on the process
	if !s.processWaitStarted {
		go s.monitorProcess(processCmd, stdoutBuffer, stderrBuffer)
	}

	return nil
}

// pidFileMonitor manages the PID file monitoring
type pidFileMonitor struct {
	pidFile  string
	watcher  *fsnotify.Watcher
	resultCh chan pidFileResult
	system   *System
}

type pidFileResult struct {
	containerPID int
	initPID      int
	err          error
}

// setupPIDFileMonitor sets up monitoring for the PID file before the process starts
func (s *System) setupPIDFileMonitor(pidFile string) (*pidFileMonitor, error) {
	// Set up file watcher
	watcher, err := fsnotify.NewWatcher()
	if err != nil {
		return nil, fmt.Errorf("failed to create file watcher: %w", err)
	}

	// Watch the directory containing the PID file
	pidDir := filepath.Dir(pidFile)
	if err := watcher.Add(pidDir); err != nil {
		watcher.Close()
		return nil, fmt.Errorf("failed to watch directory %s: %w", pidDir, err)
	}

	monitor := &pidFileMonitor{
		pidFile:  pidFile,
		watcher:  watcher,
		resultCh: make(chan pidFileResult, 1),
		system:   s,
	}

	// Start monitoring in background
	go monitor.monitor()

	// Check once if file already exists (very unlikely but handles edge case)
	if containerPID, err := readPIDFile(pidFile); err == nil && containerPID > 0 {
		// File already exists, get the init PID and send result immediately
		go func() {
			initPID, err := s.getCrunInitPID(containerPID)
			if err != nil {
				monitor.resultCh <- pidFileResult{err: fmt.Errorf("failed to get init PID: %w", err)}
				return
			}
			monitor.resultCh <- pidFileResult{containerPID: containerPID, initPID: initPID}
		}()
	}

	return monitor, nil
}

// monitor watches for the PID file to be created
func (m *pidFileMonitor) monitor() {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	for {
		select {
		case <-ctx.Done():
			m.resultCh <- pidFileResult{err: fmt.Errorf("timeout waiting for PID file %s: %w", m.pidFile, ctx.Err())}
			return

		case event, ok := <-m.watcher.Events:
			if !ok {
				m.resultCh <- pidFileResult{err: fmt.Errorf("watcher channel closed")}
				return
			}

			// Check if this is our PID file
			if event.Name == m.pidFile && (event.Op&fsnotify.Create == fsnotify.Create || event.Op&fsnotify.Write == fsnotify.Write) {
				// Give crun a moment to finish writing
				time.Sleep(50 * time.Millisecond)

				// Read the PID
				containerPID, err := readPIDFile(m.pidFile)
				if err != nil {
					m.system.logger.Warn("Failed to read PID file, will retry", "error", err)
					continue
				}

				// Get the init PID from crun state
				initPID, err := m.system.getCrunInitPID(containerPID)
				if err != nil {
					m.resultCh <- pidFileResult{err: fmt.Errorf("failed to get init PID: %w", err)}
					return
				}

				m.resultCh <- pidFileResult{containerPID: containerPID, initPID: initPID}
				return
			}

		case err, ok := <-m.watcher.Errors:
			if !ok {
				m.resultCh <- pidFileResult{err: fmt.Errorf("watcher error channel closed")}
				return
			}
			m.system.logger.Warn("File watcher error", "error", err)
		}
	}
}

// wait returns a channel that receives the result when the PID file is written
func (m *pidFileMonitor) wait() <-chan pidFileResult {
	return m.resultCh
}

// cleanup cleans up the monitor resources
func (m *pidFileMonitor) cleanup() {
	if m.watcher != nil {
		m.watcher.Close()
	}
}

// readPIDFile reads a PID from a file
func readPIDFile(pidFile string) (int, error) {
	data, err := os.ReadFile(pidFile)
	if err != nil {
		return 0, err
	}

	pidStr := strings.TrimSpace(string(data))
	pid, err := strconv.Atoi(pidStr)
	if err != nil {
		return 0, fmt.Errorf("invalid PID in file: %s", pidStr)
	}

	return pid, nil
}

// getCrunInitPID queries crun state to get the init process PID
func (s *System) getCrunInitPID(containerPID int) (int, error) {
	// We need to call "crun state <container-name>" to get the state
	// The container name is typically "app" based on the launch.sh script

	cmd := exec.Command("crun", "state", "app")
	output, err := cmd.Output()
	if err != nil {
		// If crun state fails, it might be because we're not actually using crun
		// or the container name is different. Log and continue.
		s.logger.Warn("Failed to get crun state, continuing without init PID",
			"error", err,
			"output", string(output))
		return 0, nil
	}

	// Parse the JSON output
	var state struct {
		Pid int `json:"pid"`
	}

	if err := json.Unmarshal(output, &state); err != nil {
		return 0, fmt.Errorf("failed to parse crun state: %w", err)
	}

	return state.Pid, nil
}

// monitorProcess monitors the running process and handles its exit
func (s *System) monitorProcess(cmd *exec.Cmd, stdoutBuffer, stderrBuffer *tap.CircularBuffer) {
	err := cmd.Wait()
	processRuntime := time.Since(s.processStartTime)
	s.logger.Info("Process exited", "error", err, "runtime", processRuntime)

	// Generate crash report if needed
	s.generateCrashReport(err, processRuntime, stdoutBuffer, stderrBuffer)

	s.processDoneCh <- err
	s.setState("processRunning", false)

	// Reset the wait flag under lock
	s.processMu.Lock()
	s.processWaitStarted = false
	s.processMu.Unlock()
}

// generateCrashReport generates a crash report if the process exited with an error
func (s *System) generateCrashReport(err error, processRuntime time.Duration, stdoutBuffer, stderrBuffer *tap.CircularBuffer) {
	if err != nil && s.crashReporter != nil {
		report := &tap.CrashReport{
			Command:  s.config.ProcessCommand[0],
			Args:     s.config.ProcessCommand[1:],
			Runtime:  processRuntime,
			ExitCode: -1,
		}

		// Extract exit code and signal if available
		if exitErr, ok := err.(*exec.ExitError); ok {
			if status, ok := exitErr.Sys().(syscall.WaitStatus); ok {
				report.ExitCode = status.ExitStatus()
				if status.Signaled() {
					report.Signal = status.Signal().String()
				}
			}
		}

		report.Error = err.Error()
		if stdoutBuffer != nil {
			report.RecentStdout = stdoutBuffer.GetContents()
		}
		if stderrBuffer != nil {
			report.RecentStderr = stderrBuffer.GetContents()
		}

		// Report the crash
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		if reportErr := s.crashReporter.ReportSupervisedProcessCrash(ctx, report); reportErr != nil {
			s.logger.Error("Failed to report process crash", "error", reportErr)
		}

		// Send notification to admin channel
		if s.adminChannel != nil {
			s.adminChannel.SendActivityEvent("supervised_process_crashed", report.ToMap())
		}
	}
}

// StopProcess stops the supervised process gracefully
func (s *System) StopProcess() error {
	s.processMu.Lock()
	defer s.processMu.Unlock()

	if s.processCmd == nil || s.processCmd.Process == nil {
		return nil
	}

	s.logger.Info("Stopping process", "pid", s.processCmd.Process.Pid)

	// Send SIGTERM to process group
	if err := syscall.Kill(-s.processCmd.Process.Pid, syscall.SIGTERM); err != nil {
		s.logger.Warn("Failed to send SIGTERM to process group", "error", err)
		// Try just the process
		if err := s.processCmd.Process.Signal(syscall.SIGTERM); err != nil {
			s.logger.Warn("Failed to send SIGTERM to process", "error", err)
		}
	}

	// Wait for graceful shutdown
	gracePeriod := s.config.ProcessGracefulShutdownTimeout
	if gracePeriod == 0 {
		gracePeriod = 30 * time.Second
	}

	// Declare done channel outside of conditional blocks
	var done chan struct{}

	// If Wait() has already been called, we need to wait for the process to be marked as not running
	if s.processWaitStarted {
		timer := time.NewTimer(gracePeriod)
		defer timer.Stop()

		for {
			if !s.IsProcessRunning() {
				s.logger.Info("Process stopped gracefully")
				s.processCmd = nil
				s.processWaitStarted = false
				return nil
			}

			select {
			case <-timer.C:
				// Grace period expired, continue to force kill
				s.logger.Warn("Process did not stop within grace period, sending SIGKILL")
				goto forceKill
			case <-time.After(100 * time.Millisecond):
				// Check again
			}
		}
	}

	// Normal path - Wait() hasn't been called yet
	done = make(chan struct{})
	go func() {
		s.processCmd.Wait()
		close(done)
	}()

	select {
	case <-done:
		s.logger.Info("Process stopped gracefully")
		s.processCmd = nil
		s.processWaitStarted = false
		return nil
	case <-time.After(gracePeriod):
	}

forceKill:
	// Send SIGKILL to process group
	if err := syscall.Kill(-s.processCmd.Process.Pid, syscall.SIGKILL); err != nil {
		s.logger.Error("Failed to send SIGKILL to process group", "error", err)
		// Try just the process
		if err := s.processCmd.Process.Kill(); err != nil {
			s.logger.Error("Failed to kill process", "error", err)
		}
	}

	// Wait a bit for the process to die
	if s.processWaitStarted {
		// Wait() already running, check if process becomes not running
		waitTimer := time.NewTimer(5 * time.Second)
		defer waitTimer.Stop()

		for {
			if !s.IsProcessRunning() {
				s.logger.Info("Process killed successfully")
				s.processCmd = nil
				s.processWaitStarted = false
				return nil
			}

			select {
			case <-waitTimer.C:
				return fmt.Errorf("process did not exit after SIGKILL")
			case <-time.After(100 * time.Millisecond):
				// Check again
			}
		}
	} else {
		// Normal path - wait for done channel
		select {
		case <-done:
			s.logger.Info("Process killed successfully")
			s.processCmd = nil
			s.processWaitStarted = false
			return nil
		case <-time.After(5 * time.Second):
			return fmt.Errorf("process did not exit after SIGKILL")
		}
	}
}

// ForwardSignal forwards a signal to the supervised process
func (s *System) ForwardSignal(sig os.Signal) error {
	s.processMu.Lock()
	defer s.processMu.Unlock()

	if s.processCmd == nil || s.processCmd.Process == nil {
		return fmt.Errorf("no process running")
	}

	s.logger.Debug("Forwarding signal to process", "signal", sig, "pid", s.processCmd.Process.Pid)

	// Forward signal to the process group
	if err := syscall.Kill(-s.processCmd.Process.Pid, sig.(syscall.Signal)); err != nil {
		s.logger.Warn("Failed to forward signal to process group", "signal", sig, "error", err)
		// Try sending to just the process
		if err := s.processCmd.Process.Signal(sig); err != nil {
			return fmt.Errorf("failed to forward signal: %w", err)
		}
	}

	return nil
}

// Wait waits for the process to exit
func (s *System) Wait() error {
	if s.processDoneCh == nil {
		return fmt.Errorf("no process to wait for")
	}
	return <-s.processDoneCh
}

// MonitorExecProcess monitors an exec session
func (s *System) MonitorExecProcess(execID string, execFunc func() error) error {
	// Just run the function - exec process tracking not implemented
	return execFunc()
}

// StartExecProcessTracking starts tracking an exec process
func (s *System) StartExecProcessTracking(execID string, pid int) error {
	// Exec process tracking not implemented
	return nil
}

// StopExecProcessTracking stops tracking an exec process
func (s *System) StopExecProcessTracking(execID string) {
	// Exec process tracking not implemented
}
