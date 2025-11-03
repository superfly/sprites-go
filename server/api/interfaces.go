package api

import (
	"context"
	"os"
	"time"

	"github.com/superfly/sprite-env/lib/api"
	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// SystemManager interface provides methods for managing the system (process + storage)
type SystemManager interface {
	// System lifecycle management
	Boot(ctx context.Context) error
	Shutdown(ctx context.Context) error
	Wait() error

	// Process management
	IsProcessRunning() bool
	WhenProcessRunning(ctx context.Context) error
	StartProcess() error
	StopProcess() error
	ForwardSignal(sig os.Signal) error

	// Exec process monitoring
	MonitorExecProcess(execID string, execFunc func() error) error
	StartExecProcessTracking(execID string, pid int) error
	StopExecProcessTracking(execID string)

	// Storage management
	WhenStorageReady(ctx context.Context) error
	CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error
	RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error
	ListCheckpoints(ctx context.Context) ([]api.CheckpointInfo, error)
	ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error)
	GetCheckpoint(ctx context.Context, checkpointID string) (*api.CheckpointInfo, error)
	DeleteCheckpoint(ctx context.Context, checkpointID string) error

	// Overlay sync for suspend
	// Returns a function that must be called to unfreeze the filesystem
	SyncOverlay(ctx context.Context) (func() error, error)

	// Reaper integration
	SubscribeToReapEvents() <-chan int
	UnsubscribeFromReapEvents(ch <-chan int)
	WasProcessReaped(pid int) (bool, time.Time)

	// Services management
	GetServicesManager() *services.Manager
	GetLogDir() string

	// Terminal management
	GetTMUXManager() *tmux.Manager

	// Sprite environment management
	// Takes a sprite info struct (JSON-compatible), returns a response struct (JSON-compatible)
	// Uses interface{} to avoid import cycles between server/api and server/system
	SetSpriteEnvironment(ctx context.Context, info interface{}) (interface{}, error)

    // Policy manager readiness and configuration
    WhenPolicyRunning(ctx context.Context) error
    GetPolicyConfigDir() string
}

// ProcessManager interface for process operations
type ProcessManager interface {
}
