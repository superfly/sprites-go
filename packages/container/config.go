package container

import (
	"os"
	"path/filepath"
)

// Config holds system-level configuration for container features
type Config struct {
	// Enabled determines if container features are enabled system-wide
	Enabled bool
	
	// SocketDir is the directory where TTY sockets will be created
	// Defaults to /tmp if not specified
	SocketDir string
}

// DefaultConfig returns the default configuration
func DefaultConfig() Config {
	return Config{
		Enabled:   false,
		SocketDir: "/tmp",
	}
}

// globalConfig holds the system-wide configuration
var globalConfig = DefaultConfig()

// Configure sets the global container configuration
func Configure(cfg Config) {
	// Ensure socket directory has a valid default
	if cfg.SocketDir == "" {
		cfg.SocketDir = "/tmp"
	}
	
	// Ensure socket directory exists and is absolute
	if cfg.Enabled {
		absDir, err := filepath.Abs(cfg.SocketDir)
		if err == nil {
			cfg.SocketDir = absDir
		}
		
		// Try to create the directory if it doesn't exist
		os.MkdirAll(cfg.SocketDir, 0755)
	}
	
	globalConfig = cfg
}

// GetConfig returns the current global configuration
func GetConfig() Config {
	return globalConfig
}

// IsEnabled returns whether container features are enabled
func IsEnabled() bool {
	return globalConfig.Enabled
}

// GetSocketDir returns the configured socket directory
func GetSocketDir() string {
	return globalConfig.SocketDir
}