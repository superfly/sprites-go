//go:build !linux
// +build !linux

package overlay

import (
	"testing"
)

// CleanupTestOverlays is a no-op on non-Linux systems
func CleanupTestOverlays(t *testing.T, m *Manager) {
	t.Helper()
	// No-op on non-Linux
}

// VerifyNoTestOverlays is a no-op on non-Linux systems
func VerifyNoTestOverlays(t *testing.T, m *Manager) {
	t.Helper()
	// No-op on non-Linux
}
