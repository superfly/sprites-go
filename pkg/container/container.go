package container

import (
	"os"
	"time"
)

// TTY creates a new TTY manager with a unique socket path
// This is the primary entry point for most use cases
func TTY() (*Tty, error) {
	return New()
}

// AcquirePty is a convenience function that creates a TTY manager,
// returns the socket path, and provides a function to get the PTY
func AcquirePty() (socketPath string, getPty func() (*os.File, error), cleanup func() error, err error) {
	tty, err := New()
	if err != nil {
		return "", nil, nil, err
	}

	return tty.SocketPath(), tty.Get, tty.Close, nil
}

// AcquirePtyWithTimeout is like AcquirePty but with a custom timeout
func AcquirePtyWithTimeout(timeout time.Duration) (socketPath string, getPty func() (*os.File, error), cleanup func() error, err error) {
	tty, err := New()
	if err != nil {
		return "", nil, nil, err
	}

	getPtyFunc := func() (*os.File, error) {
		return tty.GetWithTimeout(timeout)
	}

	return tty.SocketPath(), getPtyFunc, tty.Close, nil
}