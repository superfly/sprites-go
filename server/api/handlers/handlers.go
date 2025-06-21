package handlers

import (
	"log/slog"
	"time"
)

// Handlers contains all HTTP handlers
type Handlers struct {
	logger         *slog.Logger
	commandCh      chan<- Command
	processManager ProcessManager

	// Config fields
	maxWaitTime           time.Duration
	execWrapperCommand    []string
	execTTYWrapperCommand []string
}

// Config holds handler configuration
type Config struct {
	MaxWaitTime           time.Duration
	ExecWrapperCommand    []string
	ExecTTYWrapperCommand []string
}

// NewHandlers creates a new Handlers instance
func NewHandlers(logger *slog.Logger, commandCh chan<- Command, config Config, processManager ProcessManager) *Handlers {
	return &Handlers{
		logger:                logger,
		commandCh:             commandCh,
		processManager:        processManager,
		maxWaitTime:           config.MaxWaitTime,
		execWrapperCommand:    config.ExecWrapperCommand,
		execTTYWrapperCommand: config.ExecTTYWrapperCommand,
	}
}
