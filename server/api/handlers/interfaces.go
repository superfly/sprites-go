package handlers

import (
	"context"
	"io"
	"os"
	"time"

	"github.com/sprite-env/lib/api"
	"github.com/superfly/sprite-env/packages/juicefs"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// SystemManager interface provides methods for managing the system (process + storage)
type SystemManager interface {
	// System lifecycle management
	Boot(ctx context.Context) error
	Shutdown(ctx context.Context) error
	Wait() error

	// Process management
	IsProcessRunning() bool
	WaitForProcessRunning(ctx context.Context) error
	StartProcess() error
	StopProcess() error
	ForwardSignal(sig os.Signal) error

	// Exec process monitoring
	MonitorExecProcess(execID string, execFunc func() error) error
	StartExecProcessTracking(execID string, pid int) error
	StopExecProcessTracking(execID string)

	// Storage management
	HasJuiceFS() bool
	WaitForJuiceFS(ctx context.Context) error
	CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error
	RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error
	ListCheckpoints(ctx context.Context) ([]juicefs.CheckpointInfo, error)
	ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error)
	GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error)

	// Transcript management
	EnableTranscripts(ctx context.Context) error
	DisableTranscripts(ctx context.Context) error
	IsTranscriptsEnabled() bool
	CreateTranscriptCollector(env []string, ty bool) (terminal.TranscriptCollector, error)

	// Reaper integration
	SubscribeToReapEvents() <-chan int
	UnsubscribeFromReapEvents(ch <-chan int)
	WasProcessReaped(pid int) (bool, time.Time)
}

// ProcessManager interface for process operations
type ProcessManager interface {
	GetTranscriptReader() io.ReadSeeker
	GetTranscriptReader2() (func() io.ReadSeeker, func() error)
}
