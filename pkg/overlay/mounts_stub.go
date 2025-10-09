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

// mountExt4 is not supported on non-Linux platforms
func mountExt4(device, target, options string) error {
	return fmt.Errorf("ext4 mounting not supported on this platform")
}

// mountBind is not supported on non-Linux platforms
func mountBind(source, target string) error {
	return fmt.Errorf("bind mounting not supported on this platform")
}

// remountReadonly is not supported on non-Linux platforms
func remountReadonly(target string) error {
	return fmt.Errorf("remount not supported on this platform")
}

// isMounted is not supported on non-Linux platforms
func isMounted(path string) (bool, error) {
	return false, fmt.Errorf("mount checking not supported on this platform")
}
