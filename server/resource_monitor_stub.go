//go:build !linux

package main

import (
	"context"
	"log/slog"
)

// ResourceMonitor is a no-op implementation for non-Linux platforms.
type ResourceMonitor struct{}

func NewResourceMonitor(logger *slog.Logger) *ResourceMonitor { return &ResourceMonitor{} }
func (rm *ResourceMonitor) Start(ctx context.Context)         {}

