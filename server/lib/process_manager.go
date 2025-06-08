package lib

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"
)

// ProcessConfig holds configuration for the supervised process
type ProcessConfig struct {
	Command           []string
	WorkingDir        string
	Environment       []string
	RestartMaxRetries int
	RestartBackoffMax time.Duration
}

// ProcessStateObserver interface for observing process state changes
type ProcessStateObserver interface {
	OnProcessStateChanged(ctx context.Context, newState string, exitCode int) error
}

// ProcessManager manages the lifecycle of a supervised process
type ProcessManager struct {
	config ProcessConfig
	ctx    *AppContext

	mu           sync.RWMutex
	process      *exec.Cmd
	running      bool
	exitCode     int
	restartCount int

	// Observer for state changes
	observer ProcessStateObserver
}

// NewProcessManager creates a new process manager
func NewProcessManager(config ProcessConfig, appCtx *AppContext) *ProcessManager {
	return &ProcessManager{
		config:       config,
		ctx:          appCtx.WithComponent("Process"),
		running:      false,
		exitCode:     0,
		restartCount: 0,
	}
}

// SetObserver sets the process state observer
func (pm *ProcessManager) SetObserver(observer ProcessStateObserver) {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.observer = observer
}

// Start starts the supervised process
func (pm *ProcessManager) Start(ctx context.Context) error {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if pm.process != nil && pm.running {
		return fmt.Errorf("process is already running")
	}

	pm.ctx.Info("Starting supervised process", "command", pm.config.Command)

	// Create the command
	cmd := exec.CommandContext(ctx, pm.config.Command[0], pm.config.Command[1:]...)

	// Set working directory if configured
	if pm.config.WorkingDir != "" {
		cmd.Dir = pm.config.WorkingDir
	}

	// Set environment if configured
	if len(pm.config.Environment) > 0 {
		cmd.Env = append(os.Environ(), pm.config.Environment...)
	}

	// Start the process
	if err := cmd.Start(); err != nil {
		pm.ctx.Error("Failed to start supervised process", err)
		return fmt.Errorf("failed to start process: %w", err)
	}

	pm.process = cmd
	pm.running = true
	pm.exitCode = 0
	pm.ctx.Info("Supervised process started", "pid", cmd.Process.Pid)

	// Notify observer of state change
	if pm.observer != nil {
		if err := pm.observer.OnProcessStateChanged(ctx, "Running", 0); err != nil {
			pm.ctx.Error("Failed to notify observer of process start", err)
		}
	}

	// Start monitoring the process in a goroutine
	go pm.monitorProcess()

	return nil
}

// Stop gracefully stops the supervised process
func (pm *ProcessManager) Stop(ctx context.Context) error {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if pm.process == nil || !pm.running {
		pm.ctx.Debug("Process not running, nothing to stop")
		return nil
	}

	command := "unknown"
	if len(pm.config.Command) > 0 {
		command = pm.config.Command[0]
	}
	pm.ctx.Info("Stopping supervised process", "pid", pm.process.Process.Pid, "command", command)

	// Send SIGTERM for graceful shutdown
	if err := pm.process.Process.Signal(syscall.SIGTERM); err != nil {
		pm.ctx.Error("Failed to send SIGTERM to process", err)
		return fmt.Errorf("failed to signal process: %w", err)
	}

	// Wait for graceful shutdown with timeout
	done := make(chan error, 1)
	go func() {
		done <- pm.process.Wait()
	}()

	select {
	case err := <-done:
		pm.ctx.Info("Process stopped gracefully")
		pm.handleProcessExit(err)
		return nil
	case <-time.After(5 * time.Second):
		// Force kill if graceful shutdown times out
		pm.ctx.Warn("Process didn't stop gracefully, force killing")
		return pm.Kill()
	}
}

// Kill forcefully terminates the supervised process
func (pm *ProcessManager) Kill() error {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if pm.process == nil || !pm.running {
		return nil
	}

	command := "unknown"
	if len(pm.config.Command) > 0 {
		command = pm.config.Command[0]
	}
	pm.ctx.Info("Force killing supervised process", "pid", pm.process.Process.Pid, "command", command)

	if err := pm.process.Process.Kill(); err != nil {
		pm.ctx.Error("Failed to kill process", err)
		return fmt.Errorf("failed to kill process: %w", err)
	}

	// Wait for process to exit
	_ = pm.process.Wait()
	pm.running = false
	pm.exitCode = -9 // SIGKILL
	pm.ctx.Info("Process killed")

	return nil
}

// Signal sends a signal to the supervised process
func (pm *ProcessManager) Signal(sig os.Signal) error {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	if pm.process == nil || !pm.running {
		return fmt.Errorf("no running process to signal")
	}

	command := "unknown"
	if len(pm.config.Command) > 0 {
		command = pm.config.Command[0]
	}
	pm.ctx.Info("Sending signal to process", "signal", sig, "pid", pm.process.Process.Pid, "command", command)

	return pm.process.Process.Signal(sig)
}

// IsRunning returns true if the process is currently running
func (pm *ProcessManager) IsRunning() bool {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	return pm.running
}

// GetExitCode returns the last exit code
func (pm *ProcessManager) GetExitCode() int {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	return pm.exitCode
}

// GetRestartCount returns the current restart count
func (pm *ProcessManager) GetRestartCount() int {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	return pm.restartCount
}

// monitorProcess runs in a goroutine to monitor the process and handle exits
func (pm *ProcessManager) monitorProcess() {
	if pm.process == nil {
		return
	}

	// Wait for process to exit
	err := pm.process.Wait()

	pm.mu.Lock()
	defer pm.mu.Unlock()

	pm.handleProcessExit(err)
}

// handleProcessExit processes the exit of the supervised process (called with lock held)
func (pm *ProcessManager) handleProcessExit(err error) {
	pm.running = false

	command := "unknown"
	if len(pm.config.Command) > 0 {
		command = pm.config.Command[0]
	}

	var processState string

	if err != nil {
		if exitError, ok := err.(*exec.ExitError); ok {
			if status, ok := exitError.Sys().(syscall.WaitStatus); ok {
				pm.exitCode = status.ExitStatus()
				pm.ctx.Info("Process exited", "exit_code", pm.exitCode, "command", command)

				// Determine process state based on exit code
				if pm.exitCode == 137 { // SIGKILL
					processState = "Killed"
				} else if pm.exitCode > 128 { // Other signals
					processState = "Crashed"
				} else {
					processState = "Exited"
				}
			} else {
				pm.exitCode = -1
				processState = "Crashed"
				pm.ctx.Error("Process exited with unknown status", err, "command", command)
			}
		} else {
			pm.exitCode = -1
			processState = "Crashed"
			pm.ctx.Error("Process failed", err, "command", command)
		}
	} else {
		pm.exitCode = 0
		processState = "Exited"
		pm.ctx.Info("Process exited normally", "command", command)
	}

	// Notify observer of state change
	if pm.observer != nil {
		if err := pm.observer.OnProcessStateChanged(context.Background(), processState, pm.exitCode); err != nil {
			pm.ctx.Error("Failed to notify observer of process exit", err)
		}
	}
}
