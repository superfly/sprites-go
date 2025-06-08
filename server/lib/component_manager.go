package lib

import (
	"context"
	"fmt"
	"os/exec"
	"sync"
	"time"
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

	mu      sync.RWMutex
	process *exec.Cmd
	ready   bool
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

	// Start the component process
	cmd := exec.CommandContext(ctx, cm.config.StartCommand[0], cm.config.StartCommand[1:]...)

	if err := cmd.Start(); err != nil {
		cm.ctx.Error("Failed to start component", err, "type", cm.config.Type)
		return fmt.Errorf("failed to start %s component: %w", cm.config.Type, err)
	}

	cm.process = cmd
	cm.ctx.Info("Component process started", "type", cm.config.Type, "pid", cmd.Process.Pid)

	// Don't wait for readiness here - that's handled by the state machine
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

	// Poll for readiness using the ready script
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-ticker.C:
			cmd := exec.CommandContext(ctx, cm.config.ReadyCommand[0], cm.config.ReadyCommand[1:]...)
			if err := cmd.Run(); err == nil {
				cm.ctx.Info("Component is ready", "type", cm.config.Type)
				cm.setReady(true)
				return nil
			}
			// Continue polling on error
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

	// Terminate the process that was started
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

// setReady updates the ready state (called with lock held)
func (cm *ComponentManager) setReady(ready bool) {
	if cm.ready != ready {
		cm.ready = ready
		cm.ctx.Debug("Component readiness changed", "type", cm.config.Type, "ready", ready)
	}
}
