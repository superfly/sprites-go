//go:build !linux

package juicefs

import "errors"

// syncFilesystemByFD is not supported on non-Linux platforms.
// The caller should fall back to alternate sync mechanisms.
func syncFilesystemByFD(mountPath string) error {
    return errors.New("syncfs not supported")
}


