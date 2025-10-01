//go:build !linux

package system

import (
	"context"
)

// ResourceMonitor is a no-op implementation for non-Linux platforms.
type ResourceMonitor struct{}

func NewResourceMonitor(ctx context.Context) *ResourceMonitor { return &ResourceMonitor{} }
func (rm *ResourceMonitor) Start(ctx context.Context)         {}
