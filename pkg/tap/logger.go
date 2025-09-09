// Package tap provides centralized logging functionality for the sprite-env application.
package tap

import (
	"context"
	"io"
	"log/slog"
	"os"
	"strings"
)

// contextKey is used for storing the logger in context
type contextKey struct{}

var (
	// defaultLogger is the fallback logger when none is found in context
	defaultLogger *slog.Logger
)

func init() {
	// Initialize default logger from environment
	InitLogger()
}

// InitLogger initializes the default logger based on LOG_LEVEL environment variable
func InitLogger() {
	level := slog.LevelInfo

	if envLevel := os.Getenv("LOG_LEVEL"); envLevel != "" {
		switch strings.ToLower(envLevel) {
		case "debug":
			level = slog.LevelDebug
		case "info":
			level = slog.LevelInfo
		case "warn", "warning":
			level = slog.LevelWarn
		case "error":
			level = slog.LevelError
		}
	}

	// Check if we should use JSON output
	jsonOutput := os.Getenv("LOG_JSON") == "true"

	var handler slog.Handler
	if jsonOutput {
		handler = slog.NewJSONHandler(os.Stdout, &slog.HandlerOptions{
			Level: level,
		})
	} else {
		handler = slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
			Level: level,
		})
	}

	defaultLogger = slog.New(handler)
}

// Logger returns a logger from the context, or the global singleton logger if none is found.
// This function always returns a valid logger instance - it will never return nil.
// If no logger is set in the context, it returns the global singleton logger that was
// initialized based on LOG_LEVEL and LOG_JSON environment variables.
func Logger(ctx context.Context) *slog.Logger {
	if ctx != nil {
		if logger, ok := ctx.Value(contextKey{}).(*slog.Logger); ok && logger != nil {
			return logger
		}
	}
	// Return the global singleton logger when:
	// - ctx is nil
	// - no logger is found in context
	// - logger in context is nil
	return defaultLogger
}

// WithLogger returns a new context with the given logger attached
func WithLogger(ctx context.Context, logger *slog.Logger) context.Context {
	if logger == nil {
		logger = defaultLogger
	}
	return context.WithValue(ctx, contextKey{}, logger)
}

// Default returns the global singleton logger instance.
// This is the same logger that Logger(ctx) returns when no logger is found in context.
func Default() *slog.Logger {
	return defaultLogger
}

// SetDefault sets the default logger instance
func SetDefault(logger *slog.Logger) {
	if logger != nil {
		defaultLogger = logger
	}
}

// NewLogger creates a new logger with the given options
func NewLogger(level slog.Level, jsonOutput bool, output io.Writer) *slog.Logger {
	if output == nil {
		output = os.Stdout
	}

	var handler slog.Handler
	if jsonOutput {
		handler = slog.NewJSONHandler(output, &slog.HandlerOptions{
			Level: level,
		})
	} else {
		handler = slog.NewTextHandler(output, &slog.HandlerOptions{
			Level: level,
		})
	}

	return slog.New(handler)
}

// NewDiscardLogger creates a logger that discards all output
func NewDiscardLogger() *slog.Logger {
	return slog.New(slog.NewTextHandler(io.Discard, nil))
}
