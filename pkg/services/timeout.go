package services

import (
	"context"
	"fmt"
	"log/slog"
	"sync"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// progressReporter implements ProgressReporter interface
type progressReporter struct {
	serviceName  string
	logger       *slog.Logger
	lastProgress time.Time
	mu           sync.Mutex
}

func newProgressReporter(serviceName string, logger *slog.Logger) *progressReporter {
	return &progressReporter{
		serviceName:  serviceName,
		logger:       logger,
		lastProgress: time.Now(),
	}
}

// ReportProgress logs the progress and updates the last progress time
func (p *progressReporter) ReportProgress(message string) {
	p.mu.Lock()
	p.lastProgress = time.Now()
	p.mu.Unlock()

	p.logger.Info("Service progress", "service", p.serviceName, "message", message)
}

// timeSinceLastProgress returns the duration since the last progress report
func (p *progressReporter) timeSinceLastProgress() time.Duration {
	p.mu.Lock()
	defer p.mu.Unlock()
	return time.Since(p.lastProgress)
}

// startWithMonitoring wraps a service start with progress monitoring
// It will log warnings if the service appears hung (no progress for maxHungDuration)
// and abort if it exceeds the context deadline
func (m *Manager) startWithMonitoring(ctx context.Context, name string, svcDef *ServiceDefinition) error {
	logger := tap.Logger(m.ctx)

	// Set default hung duration if not specified
	maxHungDuration := svcDef.MaxHungDuration
	if maxHungDuration == 0 {
		maxHungDuration = 2 * time.Minute
	}

	// Create progress reporter
	progress := newProgressReporter(name, logger)

	// Create a channel to receive the result
	resultCh := make(chan error, 1)

	// Start the service in a goroutine
    go func() {
        var err error
        if svcDef.Hooks != nil && svcDef.Hooks.Start != nil {
            err = svcDef.Hooks.Start(ctx, progress)
        } else if svcDef.ManagedService != nil {
            err = svcDef.ManagedService.Start(ctx, progress)
        } else if svcDef.ProcessService != nil {
            // For process services, start normally (they don't use progress reporting yet)
            err = m.startProcessService(name, svcDef.ProcessService)
        } else {
            err = fmt.Errorf("service definition has neither Hooks, ManagedService nor ProcessService")
        }
        resultCh <- err
    }()

	// Monitor progress
	ticker := time.NewTicker(10 * time.Second)
	defer ticker.Stop()

	warningLogged := false

	for {
		select {
		case err := <-resultCh:
			// Service completed
			if err != nil {
				logger.Error("Service start failed", "service", name, "error", err)
				return err
			}
			logger.Info("Service started successfully", "service", name)
			return nil

		case <-ticker.C:
			// Check for hung service
			timeSinceProgress := progress.timeSinceLastProgress()

			if timeSinceProgress > maxHungDuration {
				// Service appears hung
				logger.Error("Service appears hung during start",
					"service", name,
					"time_since_progress", timeSinceProgress,
					"max_hung_duration", maxHungDuration)
				return fmt.Errorf("service %s hung during start (no progress for %v)", name, timeSinceProgress)
			} else if timeSinceProgress > 30*time.Second && !warningLogged {
				// Log warning once after 30s
				logger.Warn("Service start taking longer than expected",
					"service", name,
					"time_since_progress", timeSinceProgress)
				warningLogged = true
			}

		case <-ctx.Done():
			// Context cancelled or deadline exceeded
			logger.Error("Service start cancelled", "service", name, "error", ctx.Err())
			return fmt.Errorf("service %s start cancelled: %w", name, ctx.Err())
		}
	}
}

// stopWithMonitoring wraps a service stop with progress monitoring
func (m *Manager) stopWithMonitoring(ctx context.Context, name string, svcDef *ServiceDefinition) error {
	logger := tap.Logger(m.ctx)

	// Set default hung duration if not specified
	maxHungDuration := svcDef.MaxHungDuration
	if maxHungDuration == 0 {
		maxHungDuration = 2 * time.Minute
	}

	// Create progress reporter
	progress := newProgressReporter(name, logger)

	// Create a channel to receive the result
	resultCh := make(chan error, 1)

	// Stop the service in a goroutine
    go func() {
        var err error
        if svcDef.Hooks != nil && svcDef.Hooks.Stop != nil {
            err = svcDef.Hooks.Stop(ctx, progress)
        } else if svcDef.ManagedService != nil {
            err = svcDef.ManagedService.Stop(ctx, progress)
        } else if svcDef.ProcessService != nil {
            // For process services, stop normally
            err = m.stopProcessService(name)
        } else {
            err = fmt.Errorf("service definition has neither Hooks, ManagedService nor ProcessService")
        }
        resultCh <- err
    }()

	// Monitor progress
	ticker := time.NewTicker(10 * time.Second)
	defer ticker.Stop()

	warningLogged := false

	for {
		select {
		case err := <-resultCh:
			// Service completed
			if err != nil {
				logger.Error("Service stop failed", "service", name, "error", err)
				return err
			}
			logger.Info("Service stopped successfully", "service", name)
			return nil

		case <-ticker.C:
			// Check for hung service
			timeSinceProgress := progress.timeSinceLastProgress()

			if timeSinceProgress > maxHungDuration {
				// Service appears hung
				logger.Error("Service appears hung during stop",
					"service", name,
					"time_since_progress", timeSinceProgress,
					"max_hung_duration", maxHungDuration)
				return fmt.Errorf("service %s hung during stop (no progress for %v)", name, timeSinceProgress)
			} else if timeSinceProgress > 30*time.Second && !warningLogged {
				// Log warning once after 30s
				logger.Warn("Service stop taking longer than expected",
					"service", name,
					"time_since_progress", timeSinceProgress)
				warningLogged = true
			}

		case <-ctx.Done():
			// Context cancelled or deadline exceeded
			logger.Error("Service stop cancelled", "service", name, "error", ctx.Err())
			return fmt.Errorf("service %s stop cancelled: %w", name, ctx.Err())
		}
	}
}

// startProcessService starts a process-based service (internal helper)
func (m *Manager) startProcessService(name string, svc *Service) error {
	// This will be called from the event loop via the command channel
	result := make(chan interface{})
	m.commands <- command{
		op:     opStart,
		name:   name,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// stopProcessService stops a process-based service (internal helper)
func (m *Manager) stopProcessService(name string) error {
	// This will be called from the event loop via the command channel
	result := make(chan interface{})
	m.commands <- command{
		op:     opStop,
		name:   name,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}
