package system

import (
	"errors"
)

// Common errors
var (
	ErrSystemNotInitialized = errors.New("system not initialized")
	ErrSystemAlreadyRunning = errors.New("system already running")
	ErrStartupTimeout       = errors.New("startup timed out")
	ErrShutdownTimeout      = errors.New("shutdown timed out")
)
