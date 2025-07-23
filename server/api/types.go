package api

import (
	"time"
)

// Config holds the API server configuration
type Config struct {
	ListenAddr  string
	APIToken    string
	AdminToken  string // Optional admin-specific token for privileged operations
	MaxWaitTime time.Duration

	// Exec configuration
	ExecWrapperCommand []string

	// Sync configuration
	SyncTargetPath string
}
