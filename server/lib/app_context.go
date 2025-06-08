package lib

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"strings"
	"time"
)

// AppConfig holds runtime configuration for the application
type AppConfig struct {
	LogLevel slog.Level // Debug, Info, Warn, Error
	LogJSON  bool       // JSON vs text output
	TLATrace bool       // Enable TLA+ specification tracing
	Debug    bool       // Legacy debug flag for compatibility
}

// DefaultConfig returns sensible default configuration
func DefaultConfig() *AppConfig {
	return &AppConfig{
		LogLevel: slog.LevelInfo,
		LogJSON:  false,
		TLATrace: false,
		Debug:    false,
	}
}

// AppContext provides structured logging and configuration throughout the application
type AppContext struct {
	context.Context
	Logger    *slog.Logger
	Config    *AppConfig
	TLATracer *TLATracer
}

// NewAppContext creates a new application context with logging and configuration
func NewAppContext(config *AppConfig) *AppContext {
	if config == nil {
		config = DefaultConfig()
	}

	// Configure handler based on config
	var handler slog.Handler

	if config.LogJSON {
		opts := &slog.HandlerOptions{
			Level: config.LogLevel,
		}
		handler = slog.NewJSONHandler(os.Stderr, opts)
	} else {
		// Simple text format: [LEVEL] message
		handler = NewSimpleHandler(os.Stderr, config.LogLevel)
	}

	logger := slog.New(handler)

	// Create TLA tracer
	tlaTracer := NewTLATracer(config.TLATrace, config.LogLevel <= slog.LevelDebug)

	return &AppContext{
		Context:   context.Background(),
		Logger:    logger,
		Config:    config,
		TLATracer: tlaTracer,
	}
}

// WithContext creates a new AppContext with the given context
func (ac *AppContext) WithContext(ctx context.Context) *AppContext {
	return &AppContext{
		Context:   ctx,
		Logger:    ac.Logger,
		Config:    ac.Config,
		TLATracer: ac.TLATracer,
	}
}

// Debug logs a debug message with optional key-value pairs
func (ac *AppContext) Debug(msg string, args ...any) {
	ac.Logger.DebugContext(ac.Context, msg, args...)
}

// Info logs an info message with optional key-value pairs
func (ac *AppContext) Info(msg string, args ...any) {
	ac.Logger.InfoContext(ac.Context, msg, args...)
}

// Warn logs a warning message with optional key-value pairs
func (ac *AppContext) Warn(msg string, args ...any) {
	ac.Logger.WarnContext(ac.Context, msg, args...)
}

// Error logs an error message with optional key-value pairs
func (ac *AppContext) Error(msg string, err error, args ...any) {
	allArgs := append([]any{"error", err}, args...)
	ac.Logger.ErrorContext(ac.Context, msg, allArgs...)
}

// WithComponent returns a new logger with component context
func (ac *AppContext) WithComponent(component string) *AppContext {
	logger := ac.Logger.With("component", component)
	return &AppContext{
		Context:   ac.Context,
		Logger:    logger,
		Config:    ac.Config,
		TLATracer: ac.TLATracer,
	}
}

// WithOperation returns a new logger with operation context
func (ac *AppContext) WithOperation(operation string) *AppContext {
	logger := ac.Logger.With("operation", operation)
	return &AppContext{
		Context:   ac.Context,
		Logger:    logger,
		Config:    ac.Config,
		TLATracer: ac.TLATracer,
	}
}

// IsDebugEnabled returns true if debug logging is enabled
func (ac *AppContext) IsDebugEnabled() bool {
	return ac.Config.LogLevel <= slog.LevelDebug
}

// SimpleHandler implements a simple logging format: [LEVEL] message
type SimpleHandler struct {
	writer    io.Writer
	level     slog.Level
	startTime time.Time
}

// NewSimpleHandler creates a new simple handler
func NewSimpleHandler(writer io.Writer, level slog.Level) *SimpleHandler {
	return &SimpleHandler{
		writer:    writer,
		level:     level,
		startTime: time.Now(),
	}
}

// Enabled returns true if the handler should process this level
func (h *SimpleHandler) Enabled(ctx context.Context, level slog.Level) bool {
	return level >= h.level
}

// Handle formats and writes the log record
func (h *SimpleHandler) Handle(ctx context.Context, record slog.Record) error {
	levelName := strings.ToUpper(record.Level.String())
	elapsed := time.Since(h.startTime).Seconds()

	// Start with [elapsed LEVEL] message
	output := fmt.Sprintf("[%6.3fs %s] %s", elapsed, levelName, record.Message)

	// Add any attributes (like component, error, etc.) in a simple format
	record.Attrs(func(attr slog.Attr) bool {
		if attr.Key == "component" {
			output = fmt.Sprintf("[%6.3fs %s:%s] %s", elapsed, levelName, attr.Value.String(), record.Message)
			return false // Stop processing other attrs for component - we want it in the prefix
		} else if attr.Key == "error" {
			output = fmt.Sprintf("%s: %s", output, attr.Value.String())
		} else {
			output = fmt.Sprintf("%s %s=%s", output, attr.Key, attr.Value.String())
		}
		return true
	})

	output += "\n"
	_, err := h.writer.Write([]byte(output))
	return err
}

// WithAttrs returns a new handler with additional attributes
func (h *SimpleHandler) WithAttrs(attrs []slog.Attr) slog.Handler {
	// For simplicity, just return the same handler
	// In a more complete implementation, we'd store the attributes
	return h
}

// WithGroup returns a new handler with a group
func (h *SimpleHandler) WithGroup(name string) slog.Handler {
	// For simplicity, just return the same handler
	return h
}
