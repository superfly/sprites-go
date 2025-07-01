package handlers

import (
	"context"
	"os"
	"time"

	"github.com/sprite-env/lib/api"

	"github.com/sprite-env/packages/juicefs"
)

// SystemManager interface provides methods for managing the system (process + storage)
type SystemManager interface {
	// Process management
	IsProcessRunning() bool
	WaitForProcessRunning(ctx context.Context) error
	StartProcess() error
	StopProcess() error
	ForwardSignal(sig os.Signal) error

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

	// Reaper integration
	SubscribeToReapEvents() <-chan int
	UnsubscribeFromReapEvents(ch <-chan int)
	WasProcessReaped(pid int) (bool, time.Time)
}
