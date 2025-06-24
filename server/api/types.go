package api

import (
	"time"
)

// Config holds the API server configuration
type Config struct {
	ListenAddr  string
	APIToken    string
	MaxWaitTime time.Duration

	// Exec configuration
	ExecWrapperCommand []string
}
