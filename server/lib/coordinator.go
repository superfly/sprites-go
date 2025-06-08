package lib

import (
	"context"
	"fmt"
	"sync"
	"time"

	"sprite-env/lib/states"
)

// Coordinator orchestrates the overall sprite-env system using the new state architecture
type Coordinator struct {
	ctx       *AppContext
	tlaTracer *TLATracer

	// State managers - new architecture
	systemStateManager  *states.SystemStateManager
	dbStateManager      *states.ComponentStateManager
	fsStateManager      *states.ComponentStateManager
	processStateManager *states.ProcessStateManager

	// Legacy component managers (for actual component business logic)
	dbManager      *ComponentManager
	fsManager      *ComponentManager
	processManager *ProcessManager

	mu             sync.RWMutex
	running        bool
	shutdownCtx    context.Context
	shutdownCancel context.CancelFunc
}

// CoordinatorConfig holds configuration for the coordinator
type CoordinatorConfig struct {
	DBConfig      ComponentConfig
	FSConfig      ComponentConfig
	ProcessConfig ProcessConfig
}

// NewCoordinator creates a new system coordinator with the new state architecture
func NewCoordinator(config CoordinatorConfig, appCtx *AppContext) *Coordinator {
	shutdownCtx, shutdownCancel := context.WithCancel(context.Background())

	c := &Coordinator{
		ctx:            appCtx.WithComponent("Coordinator"),
		tlaTracer:      appCtx.TLATracer,
		dbManager:      NewComponentManager(config.DBConfig, appCtx),
		fsManager:      NewComponentManager(config.FSConfig, appCtx),
		processManager: NewProcessManager(config.ProcessConfig, appCtx),
		running:        false,
		shutdownCtx:    shutdownCtx,
		shutdownCancel: shutdownCancel,
	}

	// Create state managers
	c.systemStateManager = states.NewSystemStateManager()
	c.dbStateManager = states.NewComponentStateManager("db", "DB")
	c.fsStateManager = states.NewComponentStateManager("fs", "FS")
	c.processStateManager = states.NewProcessStateManager()

	// Inject TLA tracer into system state manager
	c.systemStateManager.SetTLATracer(appCtx.TLATracer)

	// Wire up OnTransitioned callbacks for communication
	c.dbStateManager.SetTransitionCallback(c.systemStateManager.OnComponentTransition)
	c.fsStateManager.SetTransitionCallback(c.systemStateManager.OnComponentTransition)
	c.processStateManager.SetTransitionCallback(c.systemStateManager.OnProcessTransition)

	return c
}

// Start initiates the sprite-env system startup sequence
func (c *Coordinator) Start(ctx context.Context) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.running {
		return fmt.Errorf("coordinator is already running")
	}

	c.ctx.Info("Starting sprite-env system")

	// Initialize all state managers
	if err := c.initializeStateManagers(); err != nil {
		c.ctx.Error("Failed to initialize state managers", err)
		return fmt.Errorf("failed to initialize state managers: %w", err)
	}

	// Register components with system state manager
	c.systemStateManager.RegisterComponent("db", states.ComponentInitializing)
	c.systemStateManager.RegisterComponent("fs", states.ComponentInitializing)

	c.running = true

	// Start the startup sequence
	if err := c.triggerSystemStart(ctx); err != nil {
		c.running = false
		c.ctx.Error("Failed to start system", err)
		return fmt.Errorf("failed to start system: %w", err)
	}

	c.ctx.Info("Sprite-env system started successfully")
	return nil
}

// Stop initiates graceful shutdown of the sprite-env system
func (c *Coordinator) Stop(ctx context.Context) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if !c.running {
		c.ctx.Debug("Coordinator not running, nothing to stop")
		return nil
	}

	c.ctx.Info("Stopping sprite-env system")

	// Cancel shutdown context to signal all components
	c.shutdownCancel()

	// Trigger shutdown through state managers
	if err := c.systemStateManager.TriggerShutdown(ctx); err != nil {
		c.ctx.Error("Failed to trigger graceful shutdown", err)
	}

	// Command all state managers to shut down
	c.processStateManager.TriggerStop(ctx)
	c.dbStateManager.TriggerShutdown(ctx)
	c.fsStateManager.TriggerShutdown(ctx)

	// Wait for graceful shutdown with timeout
	shutdownComplete := make(chan struct{})
	go func() {
		c.waitForShutdownCompletion()
		close(shutdownComplete)
	}()

	select {
	case <-shutdownComplete:
		c.ctx.Info("Graceful shutdown completed")
	case <-time.After(30 * time.Second):
		c.ctx.Warn("Graceful shutdown timeout, forcing shutdown")
		c.forceShutdown()
	}

	c.running = false
	c.ctx.Info("Sprite-env system stopped")
	return nil
}

// IsRunning returns true if the coordinator is running
func (c *Coordinator) IsRunning() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return c.running
}

// GetCurrentState returns the current system state
func (c *Coordinator) GetCurrentState() string {
	return c.systemStateManager.GetCurrentState()
}

// GetComponentStates returns current states of all components
func (c *Coordinator) GetComponentStates() map[string]string {
	return c.systemStateManager.GetComponentStates()
}

// GetProcessState returns the current process state
func (c *Coordinator) GetProcessState() string {
	return c.processStateManager.GetCurrentState()
}

// initializeStateManagers sets up all state managers
func (c *Coordinator) initializeStateManagers() error {
	// Initialize system state manager
	if err := c.systemStateManager.Initialize(); err != nil {
		return fmt.Errorf("failed to initialize system state manager: %w", err)
	}

	// Initialize component state managers
	if err := c.dbStateManager.Initialize(); err != nil {
		return fmt.Errorf("failed to initialize DB state manager: %w", err)
	}

	if err := c.fsStateManager.Initialize(); err != nil {
		return fmt.Errorf("failed to initialize FS state manager: %w", err)
	}

	// Initialize process state manager
	if err := c.processStateManager.Initialize(); err != nil {
		return fmt.Errorf("failed to initialize process state manager: %w", err)
	}

	return nil
}

// triggerSystemStart initiates the system startup sequence through state managers
func (c *Coordinator) triggerSystemStart(ctx context.Context) error {
	c.ctx.Info("Triggering system startup sequence through state managers")

	// Start all components concurrently through their state managers
	var wg sync.WaitGroup
	errChan := make(chan error, 3)

	// Start DB component through state manager
	wg.Add(1)
	go func() {
		defer wg.Done()
		if err := c.dbStateManager.TriggerStart(ctx); err != nil {
			errChan <- fmt.Errorf("failed to start DB state manager: %w", err)
			return
		}
		// The state manager will handle the business logic and transitions
		// We need to also start the actual component
		if err := c.dbManager.Start(ctx); err != nil {
			errChan <- fmt.Errorf("failed to start DB component: %w", err)
		}
	}()

	// Start FS component through state manager
	wg.Add(1)
	go func() {
		defer wg.Done()
		if err := c.fsStateManager.TriggerStart(ctx); err != nil {
			errChan <- fmt.Errorf("failed to start FS state manager: %w", err)
			return
		}
		// Start the actual component
		if err := c.fsManager.Start(ctx); err != nil {
			errChan <- fmt.Errorf("failed to start FS component: %w", err)
		}
	}()

	// Start process through state manager
	wg.Add(1)
	go func() {
		defer wg.Done()
		if err := c.processStateManager.TriggerStart(ctx); err != nil {
			errChan <- fmt.Errorf("failed to start process state manager: %w", err)
			return
		}
		// Start the actual process
		if err := c.processManager.Start(ctx); err != nil {
			errChan <- fmt.Errorf("failed to start supervised process: %w", err)
		}
	}()

	// Wait for all to complete
	go func() {
		wg.Wait()
		close(errChan)
	}()

	// Check for errors
	for err := range errChan {
		if err != nil {
			return err
		}
	}

	c.ctx.Info("All components and process started through state managers")
	return nil
}

// waitForShutdownCompletion waits for all state managers to reach shutdown state
func (c *Coordinator) waitForShutdownCompletion() {
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for range ticker.C {
		systemState := c.systemStateManager.GetCurrentState()
		if systemState == states.SystemShutdown {
			return
		}

		// Also check if all individual components are shut down
		dbState := c.dbStateManager.GetCurrentState()
		fsState := c.fsStateManager.GetCurrentState()
		processState := c.processStateManager.GetCurrentState()

		if dbState == states.ComponentShutdown &&
			fsState == states.ComponentShutdown &&
			(processState == states.ProcessStopped ||
				processState == states.ProcessExited ||
				processState == states.ProcessCrashed ||
				processState == states.ProcessKilled) {
			return
		}
	}
}

// forceShutdown forcefully shuts down all components
func (c *Coordinator) forceShutdown() {
	c.ctx.Warn("Force shutting down all components")

	// Force kill the process
	if err := c.processManager.Kill(); err != nil {
		c.ctx.Error("Failed to force kill supervised process", err)
	}

	// Force stop components
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	_ = c.dbManager.Stop(ctx)
	_ = c.fsManager.Stop(ctx)

	// Trigger error states in state managers if they're not already shut down
	c.dbStateManager.TriggerError(ctx)
	c.fsStateManager.TriggerError(ctx)
	c.processStateManager.TriggerError(ctx)
}

// Integration methods for process monitoring

// OnProcessExit is called when the supervised process exits
func (c *Coordinator) OnProcessExit(ctx context.Context, exitCode int) error {
	c.ctx.Info("Process exited, notifying process state manager", "exitCode", exitCode)

	// Update TLA tracer
	if exitCode == 0 {
		c.tlaTracer.UpdateProcessState("Exited")
	} else {
		c.tlaTracer.UpdateProcessState("Crashed")
	}

	// Notify process state manager
	return c.processStateManager.OnProcessExit(ctx, exitCode)
}

// OnProcessKilled is called when the process is killed by a signal
func (c *Coordinator) OnProcessKilled(ctx context.Context, signal string) error {
	c.ctx.Info("Process killed, notifying process state manager", "signal", signal)

	// Update TLA tracer
	c.tlaTracer.UpdateProcessState("Killed")

	// Notify process state manager (we'd need to convert string to syscall.Signal)
	// For now, just trigger the killed transition
	return c.processStateManager.TriggerError(ctx) // Simplified for demo
}

// OnProcessCrashed is called when the process crashes
func (c *Coordinator) OnProcessCrashed(ctx context.Context, reason string) error {
	c.ctx.Info("Process crashed, notifying process state manager", "reason", reason)

	// Update TLA tracer
	c.tlaTracer.UpdateProcessState("Crashed")

	// Notify process state manager
	return c.processStateManager.OnProcessCrashed(ctx, reason)
}

// GetSystemStateManager returns the system state manager for external access
func (c *Coordinator) GetSystemStateManager() *states.SystemStateManager {
	return c.systemStateManager
}

// GetDBStateManager returns the DB state manager for external access
func (c *Coordinator) GetDBStateManager() *states.ComponentStateManager {
	return c.dbStateManager
}

// GetFSStateManager returns the FS state manager for external access
func (c *Coordinator) GetFSStateManager() *states.ComponentStateManager {
	return c.fsStateManager
}

// GetProcessStateManager returns the process state manager for external access
func (c *Coordinator) GetProcessStateManager() *states.ProcessStateManager {
	return c.processStateManager
}
