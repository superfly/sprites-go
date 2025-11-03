package api

import (
	"time"
)

// RequestInfo contains information about a request
type RequestInfo struct {
	RequestID   string
	Method      string
	Path        string
	StartTime   time.Time
	EndTime     time.Time
	DurationMS  int64
	StatusCode  int
	Error       error
	RequestType string // "exec" or "proxy"
	ExtraData   map[string]interface{}
}

// Config holds the API server configuration
type Config struct {
	ListenAddr  string
	APIToken    string
	AdminToken  string // Optional admin-specific token for privileged operations
	MaxWaitTime time.Duration

	// Exec configuration
	ContainerEnabled bool

	// Sync configuration
	SyncTargetPath string

	// Proxy configuration
	ProxyLocalhostIPv4 string
	ProxyLocalhostIPv6 string

    // Server version string to expose in API responses
    SpriteVersion string
}
