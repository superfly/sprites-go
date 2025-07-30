//go:build !darwin && !dragonfly && !freebsd && !linux && !netbsd && !openbsd && !solaris
// +build !darwin,!dragonfly,!freebsd,!linux,!netbsd,!openbsd,!solaris

package terminal

import "os"

// disablePTYEcho is a no-op on non-Unix platforms
func disablePTYEcho(pty *os.File) error {
	return nil
}
