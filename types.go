package sprites

import (
	"time"
)

// SpriteConfig represents sprite configuration options
type SpriteConfig struct {
	RamMB     int    `json:"ram_mb,omitempty"`
	CPUs      int    `json:"cpus,omitempty"`
	Region    string `json:"region,omitempty"`
	StorageGB int    `json:"storage_gb,omitempty"`
}

// SpriteInfo represents sprite information from the API
type SpriteInfo struct {
	ID            string            `json:"id"`
	Name          string            `json:"name"`
	Organization  string            `json:"organization"`
	Status        string            `json:"status"`
	Config        *SpriteConfig     `json:"config,omitempty"`
	Environment   map[string]string `json:"environment,omitempty"`
	CreatedAt     time.Time         `json:"created_at"`
	UpdatedAt     time.Time         `json:"updated_at"`
	BucketName    string            `json:"bucket_name,omitempty"`
	PrimaryRegion string            `json:"primary_region,omitempty"`
}

// CreateSpriteRequest represents the request to create a sprite
type CreateSpriteRequest struct {
	Name        string            `json:"name"`
	Config      *SpriteConfig     `json:"config,omitempty"`
	Environment map[string]string `json:"environment,omitempty"`
}

// CreateSpriteResponse represents the response from sprite creation
type CreateSpriteResponse struct {
	Name string `json:"name"`
}

// ListOptions represents options for listing sprites
type ListOptions struct {
	Prefix            string
	MaxResults        int
	ContinuationToken string
}

// SpriteList represents a paginated list of sprites
type SpriteList struct {
	Sprites               []SpriteInfo `json:"sprites"`
	HasMore               bool         `json:"has_more"`
	NextContinuationToken string       `json:"next_continuation_token,omitempty"`
}

// Session represents an execution session
type Session struct {
	ID             string     `json:"id"`
	Command        string     `json:"command"`
	Created        time.Time  `json:"created"`
	BytesPerSecond float64    `json:"bytes_per_second"`
	IsActive       bool       `json:"is_active"`
	LastActivity   *time.Time `json:"last_activity,omitempty"`
}

// ExecOptions represents options for executing commands
type ExecOptions struct {
	WorkingDir  string
	Environment []string
	TTY         bool
	Detachable  bool
	SessionID   string
	ControlMode bool
	InitialCols int
	InitialRows int
}

// Checkpoint represents a checkpoint
type Checkpoint struct {
	ID         string    `json:"id"`
	CreateTime time.Time `json:"created_at"`
	History    []string  `json:"history,omitempty"`
}

// StreamMessage represents a message in a streaming response
type StreamMessage struct {
	Type  string `json:"type"` // "info", "stdout", "stderr", "error"
	Data  string `json:"data,omitempty"`
	Error string `json:"error,omitempty"`
}

// ProxyInitMessage represents the initial message sent to establish a proxy
type ProxyInitMessage struct {
	Host string `json:"host"`
	Port int    `json:"port"`
}

// ProxyResponseMessage represents the response from establishing a proxy
type ProxyResponseMessage struct {
	Status string `json:"status"`
	Target string `json:"target"`
}

// PortNotificationMessage represents a port event notification
type PortNotificationMessage struct {
	Type    string `json:"type"`    // "port_opened" or "port_closed"
	Port    int    `json:"port"`    // Port number
	Address string `json:"address"` // Address (e.g., "127.0.0.1", "0.0.0.0")
	PID     int    `json:"pid"`     // Process ID
}
