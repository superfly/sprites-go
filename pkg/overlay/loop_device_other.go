//go:build !linux
// +build !linux

package overlay

import (
	"context"
	"fmt"
	"runtime"
	"time"
)

// attachLoopDevice is not supported on non-Linux platforms
func attachLoopDevice(backingFile string) (string, error) {
	return "", fmt.Errorf("loop device operations are not supported on %s", runtime.GOOS)
}

// probeFileReadiness is not supported on non-Linux platforms
func probeFileReadiness(ctx context.Context, path string, timeout time.Duration) error {
	return fmt.Errorf("loop device operations are not supported on %s", runtime.GOOS)
}

// probeLoopDeviceReadiness is not supported on non-Linux platforms
func probeLoopDeviceReadiness(ctx context.Context, loopPath string, timeout time.Duration) error {
	return fmt.Errorf("loop device operations are not supported on %s", runtime.GOOS)
}

// detachLoopDevice is not supported on non-Linux platforms
func detachLoopDevice(loopPath string) error {
	return fmt.Errorf("loop device operations are not supported on %s", runtime.GOOS)
}
