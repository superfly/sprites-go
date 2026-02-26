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

// URLSettings represents URL authentication settings
type URLSettings struct {
	Auth string `json:"auth,omitempty"`
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
	URL           string            `json:"url,omitempty"`
	URLSettings   *URLSettings      `json:"url_settings,omitempty"`
	LastRunningAt *time.Time        `json:"last_running_at,omitempty"`
	LastWarmingAt *time.Time        `json:"last_warming_at,omitempty"`
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

// UpdateURLSettingsRequest represents the request to update URL settings
type UpdateURLSettingsRequest struct {
	URLSettings *URLSettings `json:"url_settings"`
}

// OrgInfo represents aggregate organization stats returned with sprite listings.
type OrgInfo struct {
	Name         string `json:"name"`
	Running      int    `json:"running"`
	Warm         int    `json:"warm"`
	Cold         int    `json:"cold"`
	RunningLimit int    `json:"running_limit"`
	WarmLimit    int    `json:"warm_limit"`
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
	Org                   *OrgInfo     `json:"org,omitempty"`
	HasMore               bool         `json:"has_more"`
	NextContinuationToken string       `json:"next_continuation_token,omitempty"`
}

// Session represents an execution session
type Session struct {
	ID             string     `json:"id"`
	Command        string     `json:"command"`
	Workdir        string     `json:"workdir"`
	Created        time.Time  `json:"created"`
	BytesPerSecond float64    `json:"bytes_per_second"`
	IsActive       bool       `json:"is_active"`
	LastActivity   *time.Time `json:"last_activity,omitempty"`
	TTY            bool       `json:"tty"`
}

// ExecOptions represents options for executing commands
type ExecOptions struct {
	WorkingDir  string
	Environment []string
	TTY         bool
	SessionID   string
	ControlMode bool
	InitialCols int
	InitialRows int
}

// Checkpoint represents a checkpoint
type Checkpoint struct {
	ID         string    `json:"id"`
	CreateTime time.Time `json:"create_time"`
	History    []string  `json:"history,omitempty"`
	Comment    string    `json:"comment,omitempty"`
	IsAuto     bool      `json:"is_auto,omitempty"`
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

// Service represents a service definition
type Service struct {
	Name     string   `json:"name"`
	Cmd      string   `json:"cmd"`
	Args     []string `json:"args"`
	Needs    []string `json:"needs"`
	HTTPPort *int     `json:"http_port,omitempty"`
}

// ServiceState represents the runtime state of a service
type ServiceState struct {
	Name          string    `json:"name"`
	Status        string    `json:"status"` // "stopped", "starting", "running", "stopping", "failed"
	PID           int       `json:"pid,omitempty"`
	StartedAt     time.Time `json:"started_at,omitempty"`
	Error         string    `json:"error,omitempty"`
	RestartCount  int       `json:"restart_count,omitempty"`
	NextRestartAt time.Time `json:"next_restart_at,omitempty"`
}

// ServiceWithState combines service definition with runtime state
type ServiceWithState struct {
	Service
	State *ServiceState `json:"state,omitempty"`
}

// ServiceRequest represents the request body for creating/updating services
type ServiceRequest struct {
	Cmd      string   `json:"cmd"`
	Args     []string `json:"args,omitempty"`
	Needs    []string `json:"needs,omitempty"`
	HTTPPort *int     `json:"http_port,omitempty"`
}

// ServiceLogEvent represents a log event from service start/stop streaming
type ServiceLogEvent struct {
	Type      string            `json:"type"` // "stdout", "stderr", "exit", "error", "complete", "started", "stopping", "stopped"
	Data      string            `json:"data,omitempty"`
	ExitCode  *int              `json:"exit_code,omitempty"`
	Timestamp int64             `json:"timestamp"`
	LogFiles  map[string]string `json:"log_files,omitempty"`
}

// NetworkPolicyRule represents a single network policy rule
type NetworkPolicyRule struct {
	Domain  string `json:"domain,omitempty"`
	Action  string `json:"action,omitempty"` // "allow" or "deny"
	Include string `json:"include,omitempty"`
}

// NetworkPolicy represents the network policy configuration
type NetworkPolicy struct {
	Rules []NetworkPolicyRule `json:"rules"`
}
