//go:build !linux
// +build !linux

package overlay

import (
	"fmt"
	"runtime"
)

// attachLoopDevice is not supported on non-Linux platforms
func attachLoopDevice(backingFile string) (string, error) {
	return "", fmt.Errorf("loop device operations are not supported on %s", runtime.GOOS)
}

// detachLoopDevice is not supported on non-Linux platforms
func detachLoopDevice(loopPath string) error {
	return fmt.Errorf("loop device operations are not supported on %s", runtime.GOOS)
}
