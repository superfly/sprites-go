package api

import (
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

// Config holds the API server configuration
type Config struct {
	ListenAddr  string
	APIToken    string
	AdminToken  string // Optional admin-specific token for privileged operations
	MaxWaitTime time.Duration

	// Exec configuration
	ExecWrapperCommand []string
	TMUXManager        *terminal.TMUXManager // Optional, will be passed to handlers

	// Sync configuration
	SyncTargetPath string

	// Proxy configuration
	ProxyLocalhostIPv4 string
	ProxyLocalhostIPv6 string
}
