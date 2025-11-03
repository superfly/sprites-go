//go:build linux

package overlay

import (
    "os"
    "golang.org/x/sys/unix"
)

// syncFilesystemByFD attempts to call syncfs(2) on the filesystem containing mountPath.
func syncFilesystemByFD(mountPath string) error {
    f, err := os.Open(mountPath)
    if err != nil {
        return err
    }
    defer f.Close()
    return unix.Syncfs(int(f.Fd()))
}


