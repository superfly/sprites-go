//go:build !linux
// +build !linux

package overlay

import (
	"testing"
)

// VerifyNoTestOverlays is a no-op on non-Linux systems
func VerifyNoTestOverlays(t *testing.T, m *Manager) {
	t.Helper()
	// No-op on non-Linux
}
