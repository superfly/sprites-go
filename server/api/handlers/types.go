package handlers

import (
	"lib/api"
	"time"
)

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
