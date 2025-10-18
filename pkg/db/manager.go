package db

import (
	"context"
	"fmt"
	"log/slog"
	"path/filepath"
	"sync"
	"time"

	"github.com/superfly/sprite-env/pkg/leaser"
)

// Config holds configuration for the database manager
type Config struct {
	BaseDir           string
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string
	S3Region          string   // S3 region for leaser
	HostID            string   // Host identifier for leaser (e.g., machine ID)
	Logger            *slog.Logger

	// Databases to manage with litestream
	DatabasePaths []string
}

// Manager handles database leasing and litestream replication
type Manager struct {
	config     Config
	logger     *slog.Logger
	leaser     *leaser.Leaser
	litestream *Litestream
	mu         sync.Mutex
	started    bool
	stopCh     chan struct{} // Signals shutdown request
	stoppedCh  chan struct{} // Closed when shutdown complete
	errCh      chan error    // Reports panics from goroutines

	// Verifiers for external resources
	// These check actual system state, not internal Go values
	setupVerifiers   []func(context.Context) error // verify resources exist
	cleanupVerifiers []func(context.Context) error // verify resources cleaned up
}

// New creates a new database manager
func New(config Config) (*Manager, error) {
	if config.Logger == nil {
		config.Logger = slog.Default()
	}

	m := &Manager{
		config:    config,
		logger:    config.Logger,
		stopCh:    make(chan struct{}),
		stoppedCh: make(chan struct{}),
		errCh:     make(chan error, 1), // Buffered to avoid blocking on panic
	}

	// Create leaser for S3 mode if configured
	if config.S3AccessKey != "" && config.S3SecretAccessKey != "" &&
		config.S3EndpointURL != "" && config.S3Bucket != "" && config.HostID != "" {
		leaserConfig := leaser.Config{
			S3AccessKey:       config.S3AccessKey,
			S3SecretAccessKey: config.S3SecretAccessKey,
			S3EndpointURL:     config.S3EndpointURL,
			S3Bucket:          config.S3Bucket,
			S3Region:          config.S3Region,
			BaseDir:           config.BaseDir,
			HostID:            config.HostID,
			Logger:            config.Logger, // keep base logger for leaser
		}
		m.leaser = leaser.New(leaserConfig)
	}

	// Initialize litestream if we have databases to manage
	if len(config.DatabasePaths) > 0 && config.S3AccessKey != "" {
		// Tag litestream logs with source label
		lsLogger := config.Logger.With("source", "litestream")
		ls, err := NewLitestream(LitestreamConfig{
			BaseDir:           config.BaseDir,
			S3AccessKey:       config.S3AccessKey,
			S3SecretAccessKey: config.S3SecretAccessKey,
			S3EndpointURL:     config.S3EndpointURL,
			S3Bucket:          config.S3Bucket,
			DatabasePaths:     config.DatabasePaths,
			Logger:            lsLogger,
		})
		if err != nil {
			return nil, fmt.Errorf("failed to create litestream: %w", err)
		}
		m.litestream = ls
	}

	return m, nil
}

// Start starts the database manager (leasing and litestream)
// Returns error if already started (NOT idempotent)
func (m *Manager) Start(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.started {
		return fmt.Errorf("db manager already started")
	}

	// Clear verifiers from any previous run
	m.setupVerifiers = nil
	m.cleanupVerifiers = nil

	// Recreate channels if they were closed by a previous Stop()
	// This enables restart after Stop()
	select {
	case <-m.stopCh:
		m.stopCh = make(chan struct{})
	default:
	}
	select {
	case <-m.stoppedCh:
		m.stoppedCh = make(chan struct{})
	default:
	}

	// CRITICAL: Acquire lease FIRST, then start litestream
	// This order must be preserved for data integrity

	// Wait for lease if configured
	if m.leaser != nil {
		m.logger.Info("Acquiring database lease...")
		if err := m.leaser.Start(ctx); err != nil {
			return fmt.Errorf("failed to acquire lease: %w", err)
		}
		m.logger.Info("Database lease acquired")
	}

	// Start litestream replication
	if m.litestream != nil {
		m.logger.Info("Starting litestream replication...")
		if err := m.litestream.Start(ctx); err != nil {
			// If litestream fails, stop the lease
			if m.leaser != nil {
				stopCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				defer cancel()
				m.leaser.Stop(stopCtx)
			}
			return fmt.Errorf("failed to start litestream: %w", err)
		}
		m.logger.Info("Litestream replication started")
	}

	m.started = true
	return nil
}

// Stop stops the database manager
// Can be called multiple times safely (idempotent)
func (m *Manager) Stop(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	// Signal shutdown
	select {
	case <-m.stopCh:
		// Already stopping
	default:
		close(m.stopCh)
	}

	if !m.started {
		// Not started, but make sure stoppedCh is closed
		select {
		case <-m.stoppedCh:
		default:
			close(m.stoppedCh)
		}
		return nil
	}

	var firstErr error

	// CRITICAL: Stop in REVERSE ORDER of startup
	// Stop litestream first
	if m.litestream != nil {
		m.logger.Info("Stopping litestream...")
		if err := m.litestream.Stop(ctx); err != nil {
			m.logger.Error("Failed to stop litestream", "error", err)
			firstErr = err
		}
	}

	// Then stop the lease
	if m.leaser != nil {
		m.logger.Info("Stopping lease...")
		if err := m.leaser.Stop(ctx); err != nil {
			m.logger.Error("Failed to stop lease", "error", err)
			if firstErr == nil {
				firstErr = err
			}
		}
	}

	// Close stoppedCh to signal completion
	select {
	case <-m.stoppedCh:
		// Already closed
	default:
		close(m.stoppedCh)
	}

	// Mark as not started so it can be restarted
	m.started = false
	return firstErr
}

// GetLeaser returns the lease manager (for tests to verify leaser resources)
func (m *Manager) GetLeaser() *leaser.Leaser {
	return m.leaser
}

// GetLitestream returns the litestream manager (for tests to verify litestream resources)
func (m *Manager) GetLitestream() *Litestream {
	return m.litestream
}

// AddDatabase adds a database path to be managed by litestream
func (m *Manager) AddDatabase(dbPath string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.started {
		return fmt.Errorf("cannot add database after manager is started")
	}

	m.config.DatabasePaths = append(m.config.DatabasePaths, dbPath)
	return nil
}

// DatabasePath returns the full path for a database file
func (m *Manager) DatabasePath(name string) string {
	return filepath.Join(m.config.BaseDir, name)
}

// StopLitestream stops litestream replication without affecting the lease
func (m *Manager) StopLitestream(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.litestream == nil {
		return nil
	}

	m.logger.Info("Stopping litestream replication...")
	if err := m.litestream.Stop(ctx); err != nil {
		m.logger.Error("Failed to stop litestream", "error", err)
		return err
	}
	m.logger.Info("Litestream replication stopped")
	return nil
}

// StartLitestream starts litestream replication without affecting the lease
func (m *Manager) StartLitestream(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.litestream == nil {
		return nil
	}

	m.logger.Info("Starting litestream replication...")
	if err := m.litestream.Start(ctx); err != nil {
		m.logger.Error("Failed to start litestream", "error", err)
		return err
	}
	m.logger.Info("Litestream replication started")
	return nil
}

// Wait blocks until Stop completes or a panic occurs in any goroutine
func (m *Manager) Wait() error {
	select {
	case <-m.stoppedCh:
		return nil
	case err := <-m.errCh:
		return err
	}
}

// SetupVerifiers returns functions that verify resources are set up correctly
// Each function checks actual system state (files, processes, etc.)
func (m *Manager) SetupVerifiers() []func(context.Context) error {
	return m.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
// Each function checks actual system state (files, processes, etc.)
func (m *Manager) CleanupVerifiers() []func(context.Context) error {
	return m.cleanupVerifiers
}

// GetLitestreamPid returns the PID of the litestream process, or 0 if not running
func (m *Manager) GetLitestreamPid() int {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.litestream != nil {
		return m.litestream.GetPid()
	}
	return 0
}
