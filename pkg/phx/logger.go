package phx

import (
	"fmt"
	"log"
)

type LoggerLevel int

const (
	LogDebug   LoggerLevel = 0
	LogInfo                = 1
	LogWarning             = 2
	LogError               = 3
)

func (level LoggerLevel) String() string {
	switch level {
	case LogDebug:
		return "DEBUG"
	case LogInfo:
		return "INFO"
	case LogWarning:
		return "WARNING"
	case LogError:
		return "ERROR"
	}
	return "UNKNOWN"
}

type Logger interface {
	Print(level LoggerLevel, kind string, v ...any)
	Println(level LoggerLevel, kind string, v ...any)
	Printf(level LoggerLevel, kind string, format string, v ...any)
}

// NoopLogger is a logger that does nothing
type NoopLogger int

func NewNoopLogger() *NoopLogger {
	return new(NoopLogger)
}

func (l *NoopLogger) Print(_ LoggerLevel, _ string, _ ...any)            {}
func (l *NoopLogger) Println(_ LoggerLevel, _ string, _ ...any)          {}
func (l *NoopLogger) Printf(_ LoggerLevel, _ string, _ string, _ ...any) {}

// CustomLogger is a logger that logs to the given log.Logger if the message is >= logLevel
type CustomLogger struct {
	logLevel LoggerLevel
	logger   *log.Logger
}

func NewCustomLogger(level LoggerLevel, logger *log.Logger) *CustomLogger {
	return &CustomLogger{
		logLevel: level,
		logger:   logger,
	}
}

func (l *CustomLogger) formatKind(kind string) string {
	return fmt.Sprintf("<%s>", kind)
}

func (l *CustomLogger) formatLevel(level LoggerLevel) string {
	return fmt.Sprintf("[%s]", level)
}

func (l *CustomLogger) Print(level LoggerLevel, kind string, v ...any) {
	if level >= l.logLevel {
		l.logger.Print(append([]any{l.formatLevel(level), l.formatKind(kind)}, v...)...)
	}
}

func (l *CustomLogger) Println(level LoggerLevel, kind string, v ...any) {
	if level >= l.logLevel {
		l.logger.Println(append([]any{l.formatLevel(level), l.formatKind(kind)}, v...)...)
	}
}

func (l *CustomLogger) Printf(level LoggerLevel, kind string, format string, v ...any) {
	if level >= l.logLevel {
		l.logger.Printf(fmt.Sprintf("%s %s %s", l.formatLevel(level), l.formatKind(kind), format), v...)
	}
}

// NewSimpleLogger returns a CustomLogger that uses the 'log' package's DefaultLogger to log messages above the given logLevel
func NewSimpleLogger(logLevel LoggerLevel) *CustomLogger {
	return &CustomLogger{
		logLevel: logLevel,
		logger:   log.Default(),
	}
}
