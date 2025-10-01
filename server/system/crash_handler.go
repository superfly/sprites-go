package system

import (
	"fmt"
	"os"
	"time"
)

// CrashHandler provides basic crash logging functionality
type CrashHandler struct {
	crashLogFile *os.File
}

// NewCrashHandler creates a new crash handler
func NewCrashHandler() (*CrashHandler, error) {
	// Create crash log file for debugging
	crashLogFile, err := os.OpenFile("/tmp/sprite-env-crash.log", os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, fmt.Errorf("could not create crash log file: %w", err)
	}

	return &CrashHandler{
		crashLogFile: crashLogFile,
	}, nil
}

// SetSystem is a no-op for compatibility
func (ch *CrashHandler) SetSystem(sys *System) {
	// No longer used - kept for compatibility
}

// Close closes the crash log file
func (ch *CrashHandler) Close() {
	if ch.crashLogFile != nil {
		ch.crashLogFile.Close()
	}
}

// LogStartup logs application startup
func (ch *CrashHandler) LogStartup() {
	startupMsg := fmt.Sprintf("Starting sprite-env at %s\n", time.Now().Format(time.RFC3339))
	fmt.Printf("%s", startupMsg)
	if ch.crashLogFile != nil {
		ch.crashLogFile.WriteString(startupMsg)
		ch.crashLogFile.Sync()
	}
}

// LogError logs an error to both stderr and crash log
func (ch *CrashHandler) LogError(format string, args ...interface{}) {
	errMsg := fmt.Sprintf(format+"\n", args...)
	fmt.Fprintf(os.Stderr, "%s", errMsg)
	if ch.crashLogFile != nil {
		ch.crashLogFile.WriteString(errMsg)
		ch.crashLogFile.Sync()
	}
}

// LogInfo logs an info message to crash log
func (ch *CrashHandler) LogInfo(format string, args ...interface{}) {
	msg := fmt.Sprintf(format+"\n", args...)
	if ch.crashLogFile != nil {
		ch.crashLogFile.WriteString(msg)
		ch.crashLogFile.Sync()
	}
}
