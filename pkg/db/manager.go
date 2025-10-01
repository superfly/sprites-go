package db

import (
	"context"
	"fmt"
	"log/slog"
	"path/filepath"
	"sync"

	"github.com/superfly/sprite-env/pkg/leaser"
)

// Config holds configuration for the database manager
type Config struct {
	BaseDir           string
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string
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
	errCh      chan error // Reports panics from goroutines
}

// New creates a new database manager
func New(config Config) (*Manager, error) {
	if config.Logger == nil {
		config.Logger = slog.Default()
	}

	m := &Manager{
		config: config,
		logger: config.Logger,
		errCh:  make(chan error, 1), // Buffered to avoid blocking on panic
	}

	// Create leaser for S3 mode if configured
	if config.S3AccessKey != "" && config.S3SecretAccessKey != "" &&
		config.S3EndpointURL != "" && config.S3Bucket != "" {
		leaserConfig := leaser.Config{
			S3AccessKey:       config.S3AccessKey,
			S3SecretAccessKey: config.S3SecretAccessKey,
			S3EndpointURL:     config.S3EndpointURL,
			S3Bucket:          config.S3Bucket,
			BaseDir:           config.BaseDir,
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
func (m *Manager) Start(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.started {
		return nil
	}

	// Wait for lease if configured
	if m.leaser != nil {
		m.logger.Info("Waiting for database lease...")
		if err := m.leaser.Wait(ctx); err != nil {
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
				m.leaser.Stop()
			}
			return fmt.Errorf("failed to start litestream: %w", err)
		}
		m.logger.Info("Litestream replication started")
	}

	m.started = true
	return nil
}

// Stop stops the database manager
func (m *Manager) Stop(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if !m.started {
		return nil
	}

	var firstErr error

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
		m.leaser.Stop()
	}

	m.started = false
	return firstErr
}

// GetLeaser returns the lease manager (for compatibility)
func (m *Manager) GetLeaser() *leaser.Leaser {
	return m.leaser
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
	// If litestream is active, wait on it (it has the only goroutine)
	if m.litestream != nil {
		return m.litestream.Wait()
	}
	// No goroutines, just block on error channel
	return <-m.errCh
}
