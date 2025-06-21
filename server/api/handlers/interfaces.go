package handlers

// ProcessManager interface for managing process lifecycle through channels
type ProcessManager interface {
	// SendCommand sends a command to the process manager and waits for response
	SendCommand(cmd Command) CommandResponse
	// IsProcessRunning returns whether the process is currently running
	IsProcessRunning() bool
}
