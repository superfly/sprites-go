package api

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// Handlers contains all HTTP handlers
type Handlers struct {
	logger *slog.Logger
	system SystemManager

	// Config fields
	maxWaitTime        time.Duration
	execWrapperCommand []string
	proxyLocalhostIPv4 string
	proxyLocalhostIPv6 string

	// TMUX manager for detachable sessions
	tmuxManager *terminal.TMUXManager
}

// HandlerConfig holds handler configuration
type HandlerConfig struct {
	MaxWaitTime        time.Duration
	ExecWrapperCommand []string
	ProxyLocalhostIPv4 string
	ProxyLocalhostIPv6 string
	TMUXManager        *terminal.TMUXManager // Optional - can be set later via SetTMUXManager
}

// NewHandlers creates a new Handlers instance
func NewHandlers(ctx context.Context, system SystemManager, config HandlerConfig) *Handlers {
	logger := tap.Logger(ctx)

	// TMUXManager is optional - it may be set later
	tmuxManager := config.TMUXManager
	if tmuxManager == nil {
		logger.Warn("NewHandlers called without TMUXManager - terminal operations will be unavailable until set")
	}

	return &Handlers{
		logger:             logger,
		system:             system,
		maxWaitTime:        config.MaxWaitTime,
		execWrapperCommand: config.ExecWrapperCommand,
		proxyLocalhostIPv4: config.ProxyLocalhostIPv4,
		proxyLocalhostIPv6: config.ProxyLocalhostIPv6,
		tmuxManager:        tmuxManager,
	}
}

// SetTMUXManager sets the TMUX manager (can be called after handlers are created)
func (h *Handlers) SetTMUXManager(tmuxManager *terminal.TMUXManager) {
	h.tmuxManager = tmuxManager
	if tmuxManager != nil {
		h.logger.Info("TMUXManager set on handlers")
	}
}

// this implementation is stupid; it's a placeholder and this code should be
// removed in a future iteration. We don't actually expect to log to files and
// if we did we wouldn't wrap that in a slog.Logger.
type lineWriter struct {
	logger *slog.Logger
	stream string
	mu     sync.Mutex
	buf    bytes.Buffer
}

func newLineWriter(name string, l *slog.Logger) *lineWriter {
	return &lineWriter{logger: l, stream: name}
}

// dubious about the concurrency requirements here b/c we create a new one of
// these for every session, but w/ev for now
func (l *lineWriter) Write(p []byte) (int, error) {
	if l == nil {
		return len(p), nil
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	n := len(p)
	l.buf.Write(p)
	for {
		line, err := l.buf.ReadString('\n')
		if err != nil {
			break
		}
		line = strings.TrimSuffix(line, "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	return n, nil
}

func (l *lineWriter) Close() {
	if l == nil {
		return
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	if l.logger != nil && l.buf.Len() > 0 {
		line := strings.TrimRight(l.buf.String(), "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	l.buf.Reset()
}

type fileCollector struct {
	file    *os.File
	logger  *slog.Logger
	streams []*lineWriter
}

func newFileCollector(base string) (*fileCollector, error) {
	ext := filepath.Ext(base)
	name := strings.TrimSuffix(base, ext)
	path := fmt.Sprintf("%s-%d%s", name, time.Now().UnixNano(), ext)
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, err
	}
	return &fileCollector{
		file:   f,
		logger: slog.New(slog.NewTextHandler(f, nil)),
	}, nil
}

func (f *fileCollector) Stream(name string) io.Writer {
	ll := newLineWriter(name, f.logger)
	f.streams = append(f.streams, ll)
	return ll
}

func (f *fileCollector) Close() error {
	var err error
	for _, s := range f.streams {
		s.Close()
	}
	if f.file != nil {
		err = f.file.Close()
	}
	return err
}

// getContextEnricher retrieves the context enricher from the request context
func (h *Handlers) getContextEnricher(ctx context.Context) ContextEnricher {
	if val := ctx.Value(contextEnricherKey{}); val != nil {
		return val.(ContextEnricher)
	}
	return nil
}

// GetTMUXManager returns the TMUX manager instance
func (h *Handlers) GetTMUXManager() *terminal.TMUXManager {
	return h.tmuxManager
}
