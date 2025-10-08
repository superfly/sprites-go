//go:build !linux

package overlay

import "fmt"

// mountTmpfsShared is not supported on non-Linux platforms
func mountTmpfsShared(target string) error {
	return fmt.Errorf("tmpfs mounting with shared propagation not supported on this platform")
}

// mountOverlayFS is not supported on non-Linux platforms
func mountOverlayFS(target, lowerdir, upperdir, workdir string) error {
	return fmt.Errorf("overlayfs mounting not supported on this platform")
}

// unmount is not supported on non-Linux platforms
func unmount(target string) error {
	return fmt.Errorf("unmounting not supported on this platform")
}

// isTmpfsMounted is not supported on non-Linux platforms
func isTmpfsMounted(path string) (bool, error) {
	return false, fmt.Errorf("filesystem type checking not supported on this platform")
}

// isOverlayFSMounted is not supported on non-Linux platforms
func isOverlayFSMounted(path string) (bool, error) {
	return false, fmt.Errorf("filesystem type checking not supported on this platform")
}
