package handlers

import (
	"lib/api"
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
	StreamCh     chan<- api.StreamMessage // Channel for streaming progress
}

// CheckpointData contains data for checkpoint command
type CheckpointData struct {
	CheckpointID string
	StreamCh     chan<- api.StreamMessage // Channel for streaming progress
}

// ExecData contains data for exec command
type ExecData struct {
	Command      []string
	Timeout      time.Duration
	TTY          bool
	DockerStream bool
}

// ExecInstance represents an exec instance in memory
type ExecInstance struct {
	ID          string
	Config      api.DockerExecCreateRequest
	Running     bool
	ExitCode    int
	Pid         int
	StartTime   time.Time
	EndTime     time.Time
	ContainerID string
}
