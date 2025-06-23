package api

import (
	"context"
	"io"
	"os"
	"time"
)

// JuiceFS interface defines the methods needed by the API server
type JuiceFS interface {
	Checkpoint(ctx context.Context, checkpointID string) error
	Restore(ctx context.Context, checkpointID string) error
	ListCheckpoints(ctx context.Context) ([]CheckpointInfo, error)
	GetCheckpoint(ctx context.Context, checkpointID string) (*CheckpointInfo, error)
}

// CheckpointInfo contains information about a checkpoint
type CheckpointInfo struct {
	ID         string    `json:"id"`
	CreateTime time.Time `json:"create_time"`
	SourceID   string    `json:"source_id,omitempty"`
}

// Supervisor interface defines the methods needed by the API server
type Supervisor interface {
	Start() (int, error)
	Stop() error
	Signal(sig os.Signal) error
	Wait() error
	Pid() (int, error)
	StdoutPipe() (io.ReadCloser, error)
	StderrPipe() (io.ReadCloser, error)
}
