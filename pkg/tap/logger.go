// Package tap provides centralized logging functionality for the sprite-env application.
package tap

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"os"
	"runtime/debug"
	"strings"
)

// contextKey is used for storing the logger in context
type contextKey struct{}

var (
	// defaultLogger is the fallback logger when none is found in context
	defaultLogger *slog.Logger
	// globalLogBuffer stores recent logs for retrieval (10k entries)
	globalLogBuffer *LogBuffer
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

	// stdout handler
	var stdoutHandler slog.Handler
	if jsonOutput {
		stdoutHandler = slog.NewJSONHandler(os.Stdout, &slog.HandlerOptions{
			Level: level,
		})
	} else {
		stdoutHandler = slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
			Level: level,
			ReplaceAttr: func(_ []string, a slog.Attr) slog.Attr {
				if a.Key == slog.TimeKey && a.Value.Kind() == slog.KindTime {
					t := a.Value.Time()
					a.Value = slog.StringValue(t.Format("15:04:05.000"))
				}
				return a
			},
		})
	}

	// initialize global buffer and fan-out
	globalLogBuffer = newLogBuffer(10000)
	bufHandler := newBufferHandler(globalLogBuffer)
	handler := newMultiHandler(stdoutHandler, bufHandler)

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

	var outHandler slog.Handler
	if jsonOutput {
		outHandler = slog.NewJSONHandler(output, &slog.HandlerOptions{
			Level: level,
		})
	} else {
		outHandler = slog.NewTextHandler(output, &slog.HandlerOptions{
			Level: level,
			ReplaceAttr: func(_ []string, a slog.Attr) slog.Attr {
				if a.Key == slog.TimeKey && a.Value.Kind() == slog.KindTime {
					t := a.Value.Time()
					a.Value = slog.StringValue(t.Format("15:04:05.000"))
				}
				return a
			},
		})
	}

	// ensure global buffer exists
	if globalLogBuffer == nil {
		globalLogBuffer = newLogBuffer(10000)
	}
	bufHandler := newBufferHandler(globalLogBuffer)
	return slog.New(newMultiHandler(outHandler, bufHandler))
}

// NewDiscardLogger creates a logger that discards all output
func NewDiscardLogger() *slog.Logger {
	if globalLogBuffer == nil {
		globalLogBuffer = newLogBuffer(10000)
	}
	bufHandler := newBufferHandler(globalLogBuffer)
	return slog.New(newMultiHandler(slog.NewTextHandler(io.Discard, nil), bufHandler))
}

// GetLogBuffer returns the global in-memory log buffer
func GetLogBuffer() *LogBuffer {
	return globalLogBuffer
}

// WithStructuredLogger returns an io.Writer that accepts JSON log lines and forwards
// them to slog using the level specified in the JSON. Intended for subprocess stdout/stderr.
//
// Expected JSON shape (extra fields are passed through as attributes):
// { "level": "debug|info|warn|error", "msg": "message", "time": "...", ... }
// "message" is accepted as an alias for "msg" and "severity" for "level".
func WithStructuredLogger(ctx context.Context) io.Writer {
	logger := Logger(ctx)

	w := &structuredWriter{
		logger: logger,
		ch:     make(chan []byte, 128),
	}

	// Aggregator goroutine: preserves write boundaries without locks, splits by lines
	go func() {
		var buf bytes.Buffer
		for p := range w.ch {
			buf.Write(p)
			for {
				b := buf.Bytes()
				idx := bytes.IndexByte(b, '\n')
				if idx < 0 {
					break
				}
				line := make([]byte, idx)
				copy(line, b[:idx])
				// consume line + newline
				buf.Next(idx + 1)
				processStructuredLine(logger, line)
			}
		}
		// flush any remaining data as one line
		if buf.Len() > 0 {
			processStructuredLine(logger, buf.Bytes())
		}
	}()

	return w
}

type structuredWriter struct {
	logger *slog.Logger
	ch     chan []byte
}

func (w *structuredWriter) Write(p []byte) (int, error) {
	// copy to avoid data races if caller reuses p
	c := make([]byte, len(p))
	copy(c, p)
	w.ch <- c
	return len(p), nil
}

// Close stops the aggregator goroutine by closing the channel.
func (w *structuredWriter) Close() error {
	select {
	case <-w.ch:
		// Already closed
	default:
		close(w.ch)
	}
	return nil
}

// processStructuredLine parses one JSON line and logs it to slog
func processStructuredLine(logger *slog.Logger, line []byte) {
	line = bytes.TrimSpace(line)
	if len(line) == 0 {
		return
	}

	var obj map[string]any
	if err := json.Unmarshal(line, &obj); err != nil {
		// Fallback: raw text
		logger.Info(string(line))
		return
	}

	var levelStr string
	if v, ok := obj["level"].(string); ok {
		levelStr = v
	} else if v, ok := obj["severity"].(string); ok {
		levelStr = v
	}

	var msg string
	if v, ok := obj["msg"].(string); ok {
		msg = v
		delete(obj, "msg")
	} else if v, ok := obj["message"].(string); ok {
		msg = v
		delete(obj, "message")
	}

	delete(obj, "level")
	delete(obj, "severity")

	attrs := make([]any, 0, len(obj)*2)
	for k, v := range obj {
		attrs = append(attrs, k, v)
	}

	switch strings.ToLower(levelStr) {
	case "debug":
		logger.Debug(msg, attrs...)
	case "warn", "warning":
		logger.Warn(msg, attrs...)
	case "error", "err":
		logger.Error(msg, attrs...)
	default:
		logger.Info(msg, attrs...)
	}
}

// Go runs a function in a goroutine with panic recovery
// If a panic occurs, it logs the panic with stack trace and sends the error to errCh
func Go(logger *slog.Logger, errCh chan<- error, fn func()) {
	go func() {
		defer func() {
			if r := recover(); r != nil {
				stack := debug.Stack()
				err := fmt.Errorf("goroutine panicked: %v", r)
				logger.Error("Goroutine panic", "panic", r, "stack", string(stack))
				select {
				case errCh <- err:
				default:
					logger.Error("Failed to send panic to error channel")
				}
			}
		}()
		fn()
	}()
}
