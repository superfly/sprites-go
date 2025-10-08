//go:build !linux

package system

import (
	"context"
)

// ResourceMonitor is a stub for non-Linux platforms
type ResourceMonitor struct{}

// NewResourceMonitor returns a no-op resource monitor on non-Linux platforms
func NewResourceMonitor(ctx context.Context, metricsCallback func(interface{})) (*ResourceMonitor, error) {
	// Return a no-op resource monitor instead of nil to prevent nil pointer dereferences
	// This ensures all ResourceMonitor methods can be called safely
	return &ResourceMonitor{}, nil
}

// PreSuspend is a no-op on non-Linux platforms
func (crm *ResourceMonitor) PreSuspend() {}

// PostResume is a no-op on non-Linux platforms
func (crm *ResourceMonitor) PostResume() {}

// Flush is a no-op on non-Linux platforms
func (crm *ResourceMonitor) Flush() {}

// Stop is a no-op on non-Linux platforms
func (crm *ResourceMonitor) Stop() {}
