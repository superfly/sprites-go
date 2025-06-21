package api

import (
	"context"
	"io"
	"os"
)

// JuiceFS interface defines the methods needed by the API server
type JuiceFS interface {
	Checkpoint(ctx context.Context, checkpointID string) error
	Restore(ctx context.Context, checkpointID string) error
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
