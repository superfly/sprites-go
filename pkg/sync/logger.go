package sync

import (
	"log/slog"
)

// SlogLogger wraps slog.Logger to implement the Logger interface
type SlogLogger struct {
	logger *slog.Logger
}

// NewSlogLogger creates a new SlogLogger
func NewSlogLogger(logger *slog.Logger) *SlogLogger {
	return &SlogLogger{logger: logger}
}

// Info logs an info message
func (l *SlogLogger) Info(msg string, args ...interface{}) {
	l.logger.Info(msg, args...)
}

// Error logs an error message
func (l *SlogLogger) Error(msg string, args ...interface{}) {
	l.logger.Error(msg, args...)
}

// Debug logs a debug message
func (l *SlogLogger) Debug(msg string, args ...interface{}) {
	l.logger.Debug(msg, args...)
}
