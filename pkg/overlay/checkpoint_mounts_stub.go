//go:build !linux

package overlay

import (
	"context"
	"fmt"
)

// MountCheckpoints is not supported on non-Linux platforms
func (m *Manager) MountCheckpoints(ctx context.Context) error {
	return fmt.Errorf("checkpoint mounting not supported on this platform")
}

// UnmountCheckpoints is not supported on non-Linux platforms
func (m *Manager) UnmountCheckpoints(ctx context.Context) error {
	return nil // No-op on non-Linux
}

// RefreshCheckpointMounts is not supported on non-Linux platforms
func (m *Manager) RefreshCheckpointMounts(ctx context.Context) error {
	return nil // No-op on non-Linux
}

// SetupCheckpointMountBase is not supported on non-Linux platforms
func (m *Manager) SetupCheckpointMountBase(ctx context.Context) error {
	return fmt.Errorf("checkpoint mount base setup not supported on this platform")
}

// listCheckpoints returns an empty list on non-Linux platforms
func (m *Manager) listCheckpoints() ([]string, error) {
	return nil, nil
}

// isCheckpointMounted always returns false on non-Linux platforms
func (m *Manager) isCheckpointMounted(cpName string) bool {
	return false
}

// doMountSingleCheckpoint is not supported on non-Linux platforms
func (m *Manager) doMountSingleCheckpoint(ctx context.Context, cpName string) (string, string, error) {
	return "", "", fmt.Errorf("checkpoint mounting not supported on this platform")
}

// mountActiveCheckpoint is not supported on non-Linux platforms
func (m *Manager) mountActiveCheckpoint(ctx context.Context) error {
	return nil // No-op on non-Linux
}

// unmountActiveCheckpoint is not supported on non-Linux platforms
func (m *Manager) unmountActiveCheckpoint(ctx context.Context) error {
	return nil // No-op on non-Linux
}

// unmountCheckpointBase is not supported on non-Linux platforms
func (m *Manager) unmountCheckpointBase(ctx context.Context) error {
	return nil // No-op on non-Linux
}

// OnCheckpointCreated is not supported on non-Linux platforms
func (m *Manager) OnCheckpointCreated(ctx context.Context) error {
	return nil // No-op on non-Linux
}
