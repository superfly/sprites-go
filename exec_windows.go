//go:build windows

package sprites

import "syscall"

// Sys returns the system-specific exit information.
// On Windows, this returns a syscall.WaitStatus with the exit code.
func (e *ExitError) Sys() interface{} {
	// On Windows, WaitStatus is a struct with ExitCode field
	return syscall.WaitStatus{
		ExitCode: uint32(e.Code),
	}
}
