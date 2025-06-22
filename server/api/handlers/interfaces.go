package handlers

import "time"

// ProcessManager interface for managing process lifecycle through channels
type ProcessManager interface {
	// SendCommand sends a command to the process manager and waits for response
	SendCommand(cmd Command) CommandResponse
	// IsProcessRunning returns whether the process is currently running
	IsProcessRunning() bool
	// SubscribeToReapEvents creates a channel that receives PIDs when processes are reaped
	SubscribeToReapEvents() <-chan int
	// UnsubscribeFromReapEvents removes a reap event listener
	UnsubscribeFromReapEvents(ch <-chan int)
	// WasProcessReaped checks if a process with the given PID was reaped
	WasProcessReaped(pid int) (bool, time.Time)
}
