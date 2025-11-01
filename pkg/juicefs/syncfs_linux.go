//go:build linux

package juicefs

import (
    "os"
    "golang.org/x/sys/unix"
)

// syncFilesystemByFD attempts to call syncfs(2) on the filesystem that
// contains mountPath. Returns nil on success, or an error to indicate
// the caller should fall back to other sync methods.
func syncFilesystemByFD(mountPath string) error {
    f, err := os.Open(mountPath)
    if err != nil {
        return err
    }
    defer f.Close()
    return unix.Syncfs(int(f.Fd()))
}


