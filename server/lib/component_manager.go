package lib

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os/exec"
	"sync"
)

// ComponentType represents the type of component
type ComponentType string

const (
	ComponentTypeDB ComponentType = "DB"
	ComponentTypeFS ComponentType = "FS"
)

// ComponentConfig holds configuration for a component
type ComponentConfig struct {
	Type              ComponentType
	StartCommand      []string // Start script, REQUIRED
	ReadyCommand      []string // Ready check script, nil if not available
	CheckpointCommand []string // Checkpoint script, nil if not available
	RestoreCommand    []string // Restore script, nil if not available
}

// ComponentManager manages the lifecycle of a single storage component (DB or FS)
type ComponentManager struct {
	config ComponentConfig
	ctx    *AppContext

	mu         sync.RWMutex
	process    *exec.Cmd
	ready      bool
	readyCmd   *exec.Cmd
	readyStdin io.WriteCloser
	readyDone  chan error
}

// NewComponentManager creates a new component manager
func NewComponentManager(config ComponentConfig, appCtx *AppContext) *ComponentManager {
	return &ComponentManager{
		config: config,
		ctx:    appCtx.WithComponent(string(config.Type)),
		ready:  false,
	}
}

// Start initiates the component startup process
func (cm *ComponentManager) Start(ctx context.Context) error {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	if cm.process != nil {
		return fmt.Errorf("component %s is already started", cm.config.Type)
	}

	// Start command is required for all components
	if len(cm.config.StartCommand) == 0 {
		return fmt.Errorf("no start command configured for %s component", cm.config.Type)
	}

	cm.ctx.Info("Starting component", "type", cm.config.Type, "command", cm.config.StartCommand)

	// Start the component process with captured output
	cmd := exec.CommandContext(ctx, cm.config.StartCommand[0], cm.config.StartCommand[1:]...)

	// Capture stdout and stderr for streaming
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return fmt.Errorf("failed to create stdout pipe for %s component: %w", cm.config.Type, err)
	}

	stderr, err := cmd.StderrPipe()
	if err != nil {
		return fmt.Errorf("failed to create stderr pipe for %s component: %w", cm.config.Type, err)
	}

	if err := cmd.Start(); err != nil {
		cm.ctx.Error("Failed to start component", err, "type", cm.config.Type)
		return fmt.Errorf("failed to start %s component: %w", cm.config.Type, err)
	}

	cm.process = cmd
	cm.ctx.Info("Component process started", "type", cm.config.Type, "pid", cmd.Process.Pid)

	// Start ready script if configured
	if len(cm.config.ReadyCommand) > 0 {
		if err := cm.startReadyScript(ctx); err != nil {
			cm.ctx.Error("Failed to start ready script", err, "type", cm.config.Type)
			// Continue anyway - ready script is optional
		}
	}

	// Start streaming output in background
	go cm.streamOutput(ctx, stdout, stderr)

	return nil
}

// WaitForReady blocks until the component is ready or context is cancelled
func (cm *ComponentManager) WaitForReady(ctx context.Context) error {
	cm.ctx.Debug("Waiting for component readiness", "type", cm.config.Type)

	// If no ready command configured, assume ready immediately
	if len(cm.config.ReadyCommand) == 0 {
		cm.ctx.Debug("No ready command for component, assuming ready", "type", cm.config.Type)
		cm.setReady(true)
		return nil
	}

	// Wait for ready script to complete (no more polling)
	cm.mu.RLock()
	readyDone := cm.readyDone
	cm.mu.RUnlock()

	if readyDone == nil {
		// No ready script was started
		cm.ctx.Debug("No ready script started, assuming ready", "type", cm.config.Type)
		cm.setReady(true)
		return nil
	}

	// Wait for ready script to complete
	select {
	case <-ctx.Done():
		return ctx.Err()
	case err := <-readyDone:
		if err == nil {
			cm.ctx.Info("Component is ready", "type", cm.config.Type)
			cm.setReady(true)
			return nil
		} else {
			cm.ctx.Error("Ready script failed", err, "type", cm.config.Type)
			return fmt.Errorf("ready script failed for %s component: %w", cm.config.Type, err)
		}
	}
}

// Stop stops the component by terminating the process that was started
func (cm *ComponentManager) Stop(ctx context.Context) error {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	if cm.process == nil {
		cm.ctx.Debug("Component not running, nothing to stop", "type", cm.config.Type)
		return nil
	}

	cm.ctx.Info("Stopping component", "type", cm.config.Type)

	// Stop ready script first
	if cm.readyCmd != nil {
		if cm.readyStdin != nil {
			cm.readyStdin.Close()
			cm.readyStdin = nil
		}
		_ = cm.readyCmd.Process.Kill()
		_ = cm.readyCmd.Wait()
		cm.readyCmd = nil
	}

	// Terminate the component process
	if cm.process.ProcessState == nil {
		if err := cm.process.Process.Kill(); err != nil {
			cm.ctx.Error("Failed to kill component process", err, "type", cm.config.Type)
			return fmt.Errorf("failed to kill %s component: %w", cm.config.Type, err)
		}
	}

	// Wait for process to exit
	_ = cm.process.Wait()

	cm.process = nil
	cm.setReady(false)
	cm.ctx.Info("Component stopped", "type", cm.config.Type)

	return nil
}

// IsReady returns true if the component is ready
func (cm *ComponentManager) IsReady() bool {
	cm.mu.RLock()
	defer cm.mu.RUnlock()
	return cm.ready
}

// IsRunning returns true if the component process is running
func (cm *ComponentManager) IsRunning() bool {
	cm.mu.RLock()
	defer cm.mu.RUnlock()
	return cm.process != nil && cm.process.ProcessState == nil
}

// GetType returns the component type
func (cm *ComponentManager) GetType() ComponentType {
	return cm.config.Type
}

// Checkpoint performs a checkpoint operation on the component
func (cm *ComponentManager) Checkpoint(ctx context.Context) error {
	if len(cm.config.CheckpointCommand) == 0 {
		cm.ctx.Debug("No checkpoint command for component", "type", cm.config.Type)
		return nil
	}

	cm.ctx.Info("Checkpointing component", "type", cm.config.Type, "command", cm.config.CheckpointCommand)

	cmd := exec.CommandContext(ctx, cm.config.CheckpointCommand[0], cm.config.CheckpointCommand[1:]...)
	if err := cmd.Run(); err != nil {
		cm.ctx.Error("Failed to checkpoint component", err, "type", cm.config.Type)
		return fmt.Errorf("failed to checkpoint %s component: %w", cm.config.Type, err)
	}

	cm.ctx.Info("Component checkpoint completed", "type", cm.config.Type)
	return nil
}

// Restore performs a restore operation on the component
func (cm *ComponentManager) Restore(ctx context.Context) error {
	if len(cm.config.RestoreCommand) == 0 {
		cm.ctx.Debug("No restore command for component", "type", cm.config.Type)
		return nil
	}

	cm.ctx.Info("Restoring component", "type", cm.config.Type, "command", cm.config.RestoreCommand)

	cmd := exec.CommandContext(ctx, cm.config.RestoreCommand[0], cm.config.RestoreCommand[1:]...)
	if err := cmd.Run(); err != nil {
		cm.ctx.Error("Failed to restore component", err, "type", cm.config.Type)
		return fmt.Errorf("failed to restore %s component: %w", cm.config.Type, err)
	}

	cm.ctx.Info("Component restore completed", "type", cm.config.Type)
	return nil
}

// startReadyScript starts the ready check script
func (cm *ComponentManager) startReadyScript(ctx context.Context) error {
	cm.readyDone = make(chan error, 1)

	cm.ctx.Debug("Starting ready script", "type", cm.config.Type, "command", cm.config.ReadyCommand)

	readyCmd := exec.CommandContext(ctx, cm.config.ReadyCommand[0], cm.config.ReadyCommand[1:]...)

	readyStdin, err := readyCmd.StdinPipe()
	if err != nil {
		return fmt.Errorf("failed to create stdin pipe for ready script: %w", err)
	}

	// Capture ready script's stdout and stderr to forward to parent
	readyStdout, err := readyCmd.StdoutPipe()
	if err != nil {
		readyStdin.Close()
		return fmt.Errorf("failed to create stdout pipe for ready script: %w", err)
	}

	readyStderr, err := readyCmd.StderrPipe()
	if err != nil {
		readyStdin.Close()
		readyStdout.Close()
		return fmt.Errorf("failed to create stderr pipe for ready script: %w", err)
	}

	if err := readyCmd.Start(); err != nil {
		readyStdin.Close()
		readyStdout.Close()
		readyStderr.Close()
		return fmt.Errorf("failed to start ready script: %w", err)
	}

	cm.readyCmd = readyCmd
	cm.readyStdin = readyStdin

	// Forward ready script output to parent
	go cm.forwardReadyOutput(ctx, readyStdout, readyStderr)

	// Monitor ready script completion
	go func() {
		err := readyCmd.Wait()
		cm.readyDone <- err
		close(cm.readyDone)

		cm.mu.Lock()
		if cm.readyStdin != nil {
			cm.readyStdin.Close()
			cm.readyStdin = nil
		}
		cm.readyCmd = nil
		cm.mu.Unlock()
	}()

	return nil
}

// streamOutput handles streaming component output to both parent and ready script
func (cm *ComponentManager) streamOutput(ctx context.Context, stdout, stderr io.Reader) {
	// Merge stdout and stderr
	combined := io.MultiReader(stdout, stderr)
	scanner := bufio.NewScanner(combined)

	for scanner.Scan() {
		line := scanner.Text()

		// Always forward to parent (existing behavior)
		cm.ctx.Info(line, "type", cm.config.Type)

		// Send to ready script if it's still running
		cm.mu.RLock()
		readyStdin := cm.readyStdin
		cm.mu.RUnlock()

		if readyStdin != nil {
			// Non-blocking write attempt
			select {
			case <-ctx.Done():
				return
			default:
				if _, err := readyStdin.Write([]byte(line + "\n")); err != nil {
					// Ready script stdin closed or errored, stop sending
					cm.mu.Lock()
					if cm.readyStdin != nil {
						cm.readyStdin.Close()
						cm.readyStdin = nil
					}
					cm.mu.Unlock()
				}
			}
		}
	}

	// Component output ended, close ready script stdin if still open
	cm.mu.Lock()
	if cm.readyStdin != nil {
		cm.readyStdin.Close()
		cm.readyStdin = nil
	}
	cm.mu.Unlock()
}

// forwardReadyOutput forwards ready script output to parent
func (cm *ComponentManager) forwardReadyOutput(ctx context.Context, stdout, stderr io.Reader) {
	// Forward stdout from ready script
	go func() {
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			line := scanner.Text()
			cm.ctx.Info(line, "type", cm.config.Type, "source", "ready-script")
		}
	}()

	// Forward stderr from ready script
	go func() {
		scanner := bufio.NewScanner(stderr)
		for scanner.Scan() {
			line := scanner.Text()
			cm.ctx.Info(line, "type", cm.config.Type, "source", "ready-script")
		}
	}()
}

// setReady updates the ready state (called with lock held)
func (cm *ComponentManager) setReady(ready bool) {
	if cm.ready != ready {
		cm.ready = ready
		cm.ctx.Debug("Component readiness changed", "type", cm.config.Type, "ready", ready)
	}
}
