package lib

import (
	"log/slog"
	"time"
)

// ComponentScripts holds the script commands for a component
type ComponentScripts struct {
	StartCommand      []string
	ReadyCommand      []string
	CheckpointCommand []string
	RestoreCommand    []string
}

// ApplicationConfig holds configuration for the application
type ApplicationConfig struct {
	// Logging configuration
	LogLevel slog.Level
	LogJSON  bool
	TLATrace bool
	Debug    bool

	// API Server configuration
	APIListenAddr string

	// Dynamic component configurations (keyed by component name)
	Components map[string]ComponentScripts

	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessRestartMaxRetries       int
	ProcessRestartBackoffMax       time.Duration
	ProcessGracefulShutdownTimeout time.Duration
}
