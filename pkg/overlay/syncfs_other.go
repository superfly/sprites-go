//go:build !linux

package overlay

import "errors"

func syncFilesystemByFD(mountPath string) error {
    return errors.New("syncfs not supported")
}


