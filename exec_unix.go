//go:build unix

package sprites

import "syscall"

// Sys returns the system-specific exit information.
// On Unix, this is a syscall.WaitStatus.
func (e *ExitError) Sys() interface{} {
	// Create a WaitStatus that indicates the process exited with e.Code
	return syscall.WaitStatus(e.Code << 8)
}
