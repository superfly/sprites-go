package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	"log/slog"

	"github.com/superfly/sprite-env/packages/container"
	portwatcher "github.com/superfly/sprite-env/packages/port-watcher"
	"github.com/superfly/sprite-env/packages/supervisor"
)

// portTracker tracks active ports and detects changes
type portTracker struct {
	mu          sync.RWMutex
	activePorts map[string]portwatcher.Port // key: "address:port:pid"
	logger      *slog.Logger
	pid         int
	stopCh      chan struct{}
}

func newPortTracker(logger *slog.Logger, pid int) *portTracker {
	return &portTracker{
		activePorts: make(map[string]portwatcher.Port),
		logger:      logger,
		pid:         pid,
		stopCh:      make(chan struct{}),
	}
}

func (pt *portTracker) portKey(port portwatcher.Port) string {
	return fmt.Sprintf("%s:%d:%d", port.Address, port.Port, port.PID)
}

func (pt *portTracker) addPort(port portwatcher.Port) {
	pt.mu.Lock()
	defer pt.mu.Unlock()

	key := pt.portKey(port)
	if _, exists := pt.activePorts[key]; !exists {
		pt.activePorts[key] = port
		pt.logger.Info("Process started listening on port",
			"port", port.Port,
			"address", port.Address,
			"pid", port.PID)
	}
}

func (pt *portTracker) getCurrentPorts() []portwatcher.Port {
	// Create a temporary port watcher to scan current ports
	tempCallback := func(port portwatcher.Port) {
		// This callback is used internally for scanning
	}

	tempWatcher, err := portwatcher.New(pt.pid, tempCallback)
	if err != nil {
		return nil
	}
	defer tempWatcher.Stop()

	// We can't easily extract current ports from the port-watcher package
	// So we'll use a different approach: track ports when the process exits
	return nil
}

func (pt *portTracker) checkRemovedPorts() {
	pt.mu.Lock()
	defer pt.mu.Unlock()

	// For now, we'll detect removed ports when the process stops
	// This is a simplified implementation
	// In a full implementation, we'd scan /proc/net/tcp directly

	// When the process stops, all ports are removed
	for key, port := range pt.activePorts {
		pt.logger.Info("Process stopped listening on port",
			"port", port.Port,
			"address", port.Address,
			"pid", port.PID)

		delete(pt.activePorts, key)
	}
}

func (pt *portTracker) stop() {
	close(pt.stopCh)
	pt.checkRemovedPorts()
}

func (pt *portTracker) clear() {
	pt.mu.Lock()
	defer pt.mu.Unlock()
	pt.activePorts = make(map[string]portwatcher.Port)
}

func (s *System) startPortWatcher(pid int) error {
	if s.portWatcher != nil {
		s.portWatcher.Stop()
	}

	tracker := newPortTracker(s.logger, pid)

	callback := func(port portwatcher.Port) {
		tracker.addPort(port)
	}

	// Create port watcher
	pw, err := portwatcher.New(pid, callback)
	if err != nil {
		return fmt.Errorf("failed to create port watcher: %w", err)
	}

	// Start port watcher
	if err := pw.Start(); err != nil {
		return fmt.Errorf("failed to start port watcher: %w", err)
	}

	s.portWatcher = pw
	s.logger.Debug("Port watcher started for process", "pid", pid)

	// Store the tracker so we can use it when stopping
	s.portTracker = tracker

	return nil
}

// StartProcess starts the supervised process
func (s *System) StartProcess() error {
	s.logger.Info("StartProcess: Entering method")

	if len(s.config.ProcessCommand) == 0 {
		s.logger.Error("StartProcess: No process command configured")
		return fmt.Errorf("no process command configured")
	}

	s.logger.Info("StartProcess: Setting up working directory", "command", s.config.ProcessCommand)

	// Set up process working directory
	workingDir := s.config.ProcessWorkingDir
	if s.juicefs != nil && workingDir == "" {
		// Default to JuiceFS active directory if available
		workingDir = filepath.Join(s.config.JuiceFSBaseDir, "data", "active", "fs")
		s.logger.Info("StartProcess: Using JuiceFS default working directory", "workingDir", workingDir)
	}

	s.logger.Info("StartProcess: Final working directory", "workingDir", workingDir)

	// Check if working directory exists
	if workingDir != "" {
		if stat, err := os.Stat(workingDir); err != nil {
			s.logger.Error("StartProcess: Working directory does not exist", "workingDir", workingDir, "error", err)
			return fmt.Errorf("working directory does not exist: %s: %w", workingDir, err)
		} else {
			s.logger.Info("StartProcess: Working directory exists", "workingDir", workingDir, "isDir", stat.IsDir())
		}
	}

	// Log the full command and environment for debugging
	s.logger.Info("StartProcess: Full command details",
		"command", s.config.ProcessCommand[0],
		"args", s.config.ProcessCommand[1:],
		"workingDir", workingDir,
		"envCount", len(s.config.ProcessEnvironment),
		"env", s.config.ProcessEnvironment)

	supervisorConfig := supervisor.Config{
		Command:     s.config.ProcessCommand[0],
		Args:        s.config.ProcessCommand[1:],
		GracePeriod: s.config.ProcessGracefulShutdownTimeout,
		Env:         append(os.Environ(), s.config.ProcessEnvironment...),
		Dir:         workingDir,
		Logger:      s.logger,
	}

	s.logger.Info("StartProcess: Creating supervisor",
		"command", supervisorConfig.Command,
		"args", supervisorConfig.Args,
		"gracePeriod", supervisorConfig.GracePeriod,
		"dir", supervisorConfig.Dir,
		"envCount", len(supervisorConfig.Env))

	// Validate that the command exists and is executable
	cmdPath := supervisorConfig.Command
	if !filepath.IsAbs(cmdPath) {
		// For relative paths, check in PATH
		if resolvedPath, err := exec.LookPath(cmdPath); err != nil {
			s.logger.Error("StartProcess: Command not found in PATH",
				"command", cmdPath,
				"error", err,
				"PATH", os.Getenv("PATH"))
			// Try to provide more context about what's available
			if cmdPath == "crun" {
				s.logger.Error("StartProcess: crun is required but not found. Ensure crun is installed and in PATH")
			}
			return fmt.Errorf("command not found in PATH: %s: %w", cmdPath, err)
		} else {
			s.logger.Info("StartProcess: Command resolved in PATH",
				"command", cmdPath,
				"resolvedPath", resolvedPath)
			cmdPath = resolvedPath
		}
	}

	// Check if it's an absolute path that exists
	if filepath.IsAbs(cmdPath) {
		if stat, err := os.Stat(cmdPath); err != nil {
			s.logger.Error("StartProcess: Command file does not exist", "command", cmdPath, "error", err)
			return fmt.Errorf("command file does not exist: %s: %w", cmdPath, err)
		} else if stat.Mode()&0111 == 0 {
			s.logger.Error("StartProcess: Command file is not executable",
				"command", cmdPath,
				"mode", stat.Mode())
			return fmt.Errorf("command file is not executable: %s", cmdPath)
		} else {
			s.logger.Info("StartProcess: Command file exists and is executable",
				"command", cmdPath,
				"mode", stat.Mode())
		}
	}

	s.logger.Info("StartProcess: Command validation successful")

	// Use container-wrapped process if containers are enabled, otherwise use basic supervisor
	if s.config.ContainerEnabled {
		s.logger.Info("StartProcess: Creating container-wrapped process")

		// For container processes, we need to ensure the command exists in the container context
		// The exec.sh wrapper will handle the actual command execution
		if s.config.ProcessCommand[0] == "/home/sprite/launch.sh" {
			// Check if the file exists before trying to run it
			if _, err := os.Stat(s.config.ProcessCommand[0]); err != nil {
				s.logger.Error("StartProcess: launch.sh not found or not accessible",
					"path", s.config.ProcessCommand[0],
					"error", err,
					"cwd", workingDir)
				// This might be expected if the file is in the container, not the host
				s.logger.Info("StartProcess: Note - file may exist inside container even if not found on host")
			}
		}

		processConfig := container.ProcessConfig{
			Config: supervisor.Config{
				Command:     s.config.ProcessCommand[0],
				Args:        s.config.ProcessCommand[1:],
				GracePeriod: s.config.ProcessGracefulShutdownTimeout,
				Env:         append(os.Environ(), s.config.ProcessEnvironment...),
				Dir:         workingDir,
				Logger:      s.logger,
			},
			TTYTimeout: s.config.ContainerTTYTimeout,
			TTYOutput:  os.Stdout, // Forward TTY output to logs
		}

		containerProcess, err := container.NewProcess(processConfig)
		if err != nil {
			s.logger.Error("StartProcess: Failed to create container process", "error", err)
			return fmt.Errorf("failed to create container process: %w", err)
		}

		s.logger.Info("StartProcess: Container process created successfully, starting process")

		pid, err := containerProcess.Start()
		if err != nil {
			s.logger.Error("StartProcess: Failed to start container process", "error", err)
			return fmt.Errorf("failed to start container process: %w", err)
		}

		// Store the container process (which embeds the supervisor)
		s.supervisor = containerProcess.Supervisor
		s.containerProcess = containerProcess
		s.setState("processRunning", true)

		s.logger.Info("StartProcess: Container process started successfully", "pid", pid, "command", s.config.ProcessCommand)

		// Start port watcher for the container process
		if err := s.startPortWatcher(pid); err != nil {
			s.logger.Error("StartProcess: Failed to start port watcher for container process", "error", err)
			return fmt.Errorf("failed to start port watcher for container process: %w", err)
		}

	} else {
		s.logger.Info("StartProcess: Creating basic supervisor (containers disabled)")

		sup, err := supervisor.New(supervisorConfig)
		if err != nil {
			s.logger.Error("StartProcess: Failed to create supervisor", "error", err)
			return fmt.Errorf("failed to create supervisor: %w", err)
		}

		s.logger.Info("StartProcess: Supervisor created successfully, starting process")

		pid, err := sup.Start()
		if err != nil {
			s.logger.Error("StartProcess: Failed to start process", "error", err)
			return fmt.Errorf("failed to start process: %w", err)
		}

		s.supervisor = sup
		s.setState("processRunning", true)

		s.logger.Info("StartProcess: Process started successfully", "pid", pid, "command", s.config.ProcessCommand)

		// Start port watcher for the basic supervisor process
		if err := s.startPortWatcher(pid); err != nil {
			s.logger.Error("StartProcess: Failed to start port watcher for basic supervisor process", "error", err)
			return fmt.Errorf("failed to start port watcher for basic supervisor process: %w", err)
		}
	}

	// Close the old channel and create a new one for future waits
	close(s.processReadyCh)
	s.processReadyCh = make(chan struct{})

	// Monitor process in background
	go func() {
		s.logger.Info("StartProcess: Starting background process monitor")
		err := s.supervisor.Wait()
		s.logger.Info("StartProcess: Process monitor detected process exit", "error", err)
		s.processDoneCh <- err

		s.setState("processRunning", false)
		s.logger.Info("StartProcess: Background monitor completed")
	}()

	s.logger.Info("StartProcess: Method completed successfully")
	return nil
}

// StopProcess stops the supervised process
func (s *System) StopProcess() error {
	if !s.getState("processRunning").(bool) || s.supervisor == nil {
		return nil
	}

	s.logger.Info("Stopping supervised process...")

	// Stop port tracker if running (this will log stopped ports)
	if s.portTracker != nil {
		if tracker, ok := s.portTracker.(*portTracker); ok {
			tracker.stop()
		}
		s.portTracker = nil
	}

	// Stop port watcher if running
	if s.portWatcher != nil {
		s.logger.Debug("Stopping port watcher...")
		s.portWatcher.Stop()
		s.portWatcher = nil
	}

	// Stop container process if available, otherwise stop basic supervisor
	if s.containerProcess != nil {
		if err := s.containerProcess.Stop(); err != nil {
			return fmt.Errorf("failed to stop container process: %w", err)
		}
		s.containerProcess = nil
	} else {
		if err := s.supervisor.Stop(); err != nil {
			return fmt.Errorf("failed to stop process: %w", err)
		}
	}

	s.setState("processRunning", false)
	s.logger.Info("Process stopped successfully")
	return nil
}

// Wait waits for the supervised process to complete
func (s *System) Wait() error {
	// If no process is running, return immediately
	if !s.getState("processRunning").(bool) {
		return nil
	}

	// Wait for process to complete
	err := <-s.processDoneCh
	return err
}

// ForwardSignal forwards a signal to the supervised process
func (s *System) ForwardSignal(sig os.Signal) error {
	if s.getState("processRunning").(bool) && s.supervisor != nil {
		return s.supervisor.Signal(sig)
	}
	return nil
}

// execProcessTracker tracks processes created by exec operations
type execProcessTracker struct {
	mu       sync.RWMutex
	trackers map[string]*execPortTracker // key: unique exec ID
	logger   *slog.Logger
}

type execPortTracker struct {
	portWatcher *portwatcher.PortWatcher
	portTracker *portTracker
	processIds  []int // PIDs being monitored
	stopCh      chan struct{}
}

func newExecProcessTracker(logger *slog.Logger) *execProcessTracker {
	return &execProcessTracker{
		trackers: make(map[string]*execPortTracker),
		logger:   logger,
	}
}

func (ept *execProcessTracker) startTracking(execID string, watchPID int) error {
	ept.mu.Lock()
	defer ept.mu.Unlock()

	// Stop any existing tracker for this exec ID
	if existing, exists := ept.trackers[execID]; exists {
		existing.stop()
		delete(ept.trackers, execID)
	}

	// Create new port tracker for the exec process
	tracker := newPortTracker(ept.logger, watchPID)

	callback := func(port portwatcher.Port) {
		tracker.addPort(port)
	}

	// Create port watcher for the exec process and its children
	pw, err := portwatcher.New(watchPID, callback)
	if err != nil {
		return fmt.Errorf("failed to create port watcher for exec process: %w", err)
	}

	if err := pw.Start(); err != nil {
		return fmt.Errorf("failed to start port watcher for exec process: %w", err)
	}

	execTracker := &execPortTracker{
		portWatcher: pw,
		portTracker: tracker,
		processIds:  []int{watchPID},
		stopCh:      make(chan struct{}),
	}

	ept.trackers[execID] = execTracker
	ept.logger.Debug("Started port monitoring for exec process", "execID", execID, "pid", watchPID)

	return nil
}

func (ept *execProcessTracker) stopTracking(execID string) {
	ept.mu.Lock()
	defer ept.mu.Unlock()

	if tracker, exists := ept.trackers[execID]; exists {
		tracker.stop()
		delete(ept.trackers, execID)
		ept.logger.Debug("Stopped port monitoring for exec process", "execID", execID)
	}
}

func (ett *execPortTracker) stop() {
	close(ett.stopCh)
	if ett.portWatcher != nil {
		ett.portWatcher.Stop()
	}
	if ett.portTracker != nil {
		ett.portTracker.stop()
	}
}

func (s *System) getExecProcessTracker() *execProcessTracker {
	if s.execProcessTracker == nil {
		s.execProcessTracker = newExecProcessTracker(s.logger)
	}

	if ept, ok := s.execProcessTracker.(*execProcessTracker); ok {
		return ept
	}

	// This shouldn't happen, but handle it gracefully
	s.execProcessTracker = newExecProcessTracker(s.logger)
	return s.execProcessTracker.(*execProcessTracker)
}

// getCurrentProcesses returns a set of currently running process PIDs that are children of the current process
func getCurrentProcesses() (map[int]bool, error) {
	processes := make(map[int]bool)

	// Get current process PID
	currentPID := os.Getpid()

	// Use ps to get all processes and their parent PIDs
	cmd := exec.Command("ps", "-eo", "pid,ppid")
	output, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("failed to get process list: %w", err)
	}

	lines := strings.Split(string(output), "\n")
	for _, line := range lines[1:] { // Skip header
		fields := strings.Fields(line)
		if len(fields) < 2 {
			continue
		}

		pid, err := strconv.Atoi(fields[0])
		if err != nil {
			continue
		}

		ppid, err := strconv.Atoi(fields[1])
		if err != nil {
			continue
		}

		// Check if this process is a descendant of current process
		if ppid == currentPID || isDescendantOf(pid, currentPID) {
			processes[pid] = true
		}
	}

	return processes, nil
}

// isDescendantOf checks if pid is a descendant of ancestorPID
func isDescendantOf(pid, ancestorPID int) bool {
	if pid == ancestorPID {
		return true
	}

	// Get parent PID
	parentPID := getParentPID(pid)
	if parentPID <= 1 {
		return false
	}

	return isDescendantOf(parentPID, ancestorPID)
}

// getParentPID returns the parent PID of the given PID
func getParentPID(pid int) int {
	statPath := fmt.Sprintf("/proc/%d/stat", pid)
	data, err := os.ReadFile(statPath)
	if err != nil {
		return 0
	}

	// Parse the stat file to get PPID (4th field after the comm field)
	statStr := string(data)

	// Find the last occurrence of ')' to handle process names with spaces/parens
	lastParen := strings.LastIndex(statStr, ")")
	if lastParen == -1 {
		return 0
	}

	// Skip the ') ' and split the remaining fields
	fields := strings.Fields(statStr[lastParen+2:])
	if len(fields) < 2 {
		return 0
	}

	ppid, err := strconv.Atoi(fields[1]) // PPID is the 3rd field after ')'
	if err != nil {
		return 0
	}

	return ppid
}

// findNewProcesses compares two process snapshots and returns newly created processes
func findNewProcesses(before, after map[int]bool) []int {
	var newPIDs []int

	for pid := range after {
		if !before[pid] {
			newPIDs = append(newPIDs, pid)
		}
	}

	return newPIDs
}

// monitorExecProcess wraps an exec operation to monitor any new processes it creates
func (s *System) monitorExecProcess(execID string, execFunc func() error) error {
	// Get process snapshot before exec
	beforeProcs, err := getCurrentProcesses()
	if err != nil {
		s.logger.Debug("Failed to get process snapshot before exec", "error", err)
		// Continue without monitoring
		return execFunc()
	}

	// Execute the actual exec operation
	execErr := execFunc()

	// Small delay to allow process to start
	time.Sleep(100 * time.Millisecond)

	// Get process snapshot after exec
	afterProcs, err := getCurrentProcesses()
	if err != nil {
		s.logger.Debug("Failed to get process snapshot after exec", "error", err)
		return execErr
	}

	// Find new processes
	newPIDs := findNewProcesses(beforeProcs, afterProcs)

	if len(newPIDs) > 0 {
		s.logger.Debug("Found new processes from exec", "execID", execID, "pids", newPIDs)

		// Start monitoring the first new process (usually the main exec'd process)
		tracker := s.getExecProcessTracker()
		if tracker != nil {
			if err := tracker.startTracking(execID, newPIDs[0]); err != nil {
				s.logger.Error("Failed to start tracking exec process", "execID", execID, "pid", newPIDs[0], "error", err)
			}
		}
	} else {
		s.logger.Debug("No new processes detected from exec", "execID", execID)
	}

	return execErr
}

// MonitorExecProcess wraps an exec operation to monitor any new processes it creates
func (s *System) MonitorExecProcess(execID string, execFunc func() error) error {
	return s.monitorExecProcess(execID, execFunc)
}

// StartExecProcessTracking starts monitoring an exec process by PID directly
func (s *System) StartExecProcessTracking(execID string, pid int) error {
	tracker := s.getExecProcessTracker()
	if tracker != nil {
		return tracker.startTracking(execID, pid)
	}
	return nil
}

// StopExecProcessTracking stops monitoring an exec process
func (s *System) StopExecProcessTracking(execID string) {
	tracker := s.getExecProcessTracker()
	if tracker != nil {
		tracker.stopTracking(execID)
	}
}
