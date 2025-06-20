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

// S3Config holds S3 configuration
type S3Config struct {
	AccessKey string `json:"access_key"`
	SecretKey string `json:"secret_key"`
	Endpoint  string `json:"endpoint"`
}

// ExecConfig holds configuration for exec endpoint
type ExecConfig struct {
	WrapperCommand    []string `json:"wrapper_command"`     // Command wrapper for exec (e.g., ["crun", "exec", "app"])
	TTYWrapperCommand []string `json:"tty_wrapper_command"` // Command wrapper for TTY exec
}

// ApplicationConfig holds configuration for the application
type ApplicationConfig struct {
	// Logging configuration
	LogLevel slog.Level
	LogJSON  bool
	Debug    bool

	// API Server configuration
	APIListenAddr  string
	APIMaxWaitTime time.Duration // Maximum time to wait for system to be ready (default 30s)

	// Dynamic component configurations (keyed by component name)
	Components map[string]ComponentScripts

	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessRestartMaxRetries       int
	ProcessRestartBackoffMax       time.Duration
	ProcessGracefulShutdownTimeout time.Duration

	// S3 configuration
	S3 S3Config

	// Exec configuration
	Exec ExecConfig
}
