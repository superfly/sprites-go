//go:build !linux
// +build !linux

package portwatcher

import (
	"testing"
)

// TestNamespaceCreation is skipped on non-Linux systems
func TestNamespaceCreation(t *testing.T) {
	t.Skip("Namespace tests are only supported on Linux")
}

// TestMultipleNamespaces is skipped on non-Linux systems
func TestMultipleNamespaces(t *testing.T) {
	t.Skip("Namespace tests are only supported on Linux")
}

// TestNamespaceIsolation is skipped on non-Linux systems
func TestNamespaceIsolation(t *testing.T) {
	t.Skip("Namespace tests are only supported on Linux")
}

// TestHostNetworkNamespace is skipped on non-Linux systems
func TestHostNetworkNamespace(t *testing.T) {
	t.Skip("Namespace tests are only supported on Linux")
} 