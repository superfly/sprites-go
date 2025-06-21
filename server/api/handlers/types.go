package handlers

import (
	"encoding/json"
	"fmt"
	"time"
)

// Command represents commands sent from HTTP server to main loop
type Command struct {
	Type     CommandType
	Response chan<- CommandResponse
	Data     interface{}
}

// CommandType represents the type of command
type CommandType int

const (
	CommandExec CommandType = iota
	CommandCheckpoint
	CommandRestore
	CommandGetStatus
)

// CommandResponse represents responses from main loop to HTTP server
type CommandResponse struct {
	Success bool
	Error   error
	Data    interface{}
}

// RestoreData contains data for restore command
type RestoreData struct {
	CheckpointID string
	StreamCh     chan<- StreamMessage // Channel for streaming progress
}

// CheckpointData contains data for checkpoint command
type CheckpointData struct {
	CheckpointID string
	StreamCh     chan<- StreamMessage // Channel for streaming progress
}

// ExecData contains data for exec command
type ExecData struct {
	Command []string
	Timeout time.Duration
	TTY     bool
}

// ExecRequest represents the request body for exec endpoint
type ExecRequest struct {
	Command []string `json:"command"`
	Timeout Duration `json:"timeout"`
	TTY     bool     `json:"tty"` // Whether to use TTY wrapper
}

// Duration is a wrapper around time.Duration that supports JSON unmarshaling from nanoseconds
type Duration time.Duration

// UnmarshalJSON implements json.Unmarshaler for Duration
func (d *Duration) UnmarshalJSON(b []byte) error {
	var v interface{}
	if err := json.Unmarshal(b, &v); err != nil {
		return err
	}

	switch value := v.(type) {
	case float64:
		// Assume nanoseconds
		*d = Duration(time.Duration(value))
		return nil
	case string:
		// Try to parse as duration string
		duration, err := time.ParseDuration(value)
		if err != nil {
			return err
		}
		*d = Duration(duration)
		return nil
	default:
		return fmt.Errorf("invalid duration type: %T", v)
	}
}

// ExecMessage represents a line of output or the final exit status
type ExecMessage struct {
	Type     string    `json:"type"` // "stdout", "stderr", or "exit"
	Data     string    `json:"data,omitempty"`
	ExitCode int       `json:"exit_code"`
	Error    string    `json:"error,omitempty"`
	Time     time.Time `json:"time"`
}

// StreamMessage represents a streaming message (similar to ExecMessage)
type StreamMessage struct {
	Type  string    `json:"type"` // "info", "stdout", "stderr", "error", "complete"
	Data  string    `json:"data,omitempty"`
	Error string    `json:"error,omitempty"`
	Time  time.Time `json:"time"`
}
