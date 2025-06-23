package handlers

import (
	"context"
	"lib/api"
	"os"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
)

// SystemManager interface provides methods for managing the system (process + storage)
type SystemManager interface {
	// Process management
	IsProcessRunning() bool
	StartProcess() error
	StopProcess() error
	ForwardSignal(sig os.Signal) error

	// Storage management
	HasJuiceFS() bool
	CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error
	RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error
	ListCheckpoints(ctx context.Context) ([]juicefs.CheckpointInfo, error)
	GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error)

	// Reaper integration
	SubscribeToReapEvents() <-chan int
	UnsubscribeFromReapEvents(ch <-chan int)
	WasProcessReaped(pid int) (bool, time.Time)
}
