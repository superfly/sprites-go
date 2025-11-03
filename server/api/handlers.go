package api

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// Handlers contains all HTTP handlers
type Handlers struct {
	logger *slog.Logger
	system SystemManager

	// Config fields
	maxWaitTime        time.Duration
	containerEnabled   bool
	proxyLocalhostIPv4 string
	proxyLocalhostIPv6 string

	// System will supply tmux manager on demand
	// (no stored reference to avoid lifecycle/dup problems)
}

// HandlerConfig holds handler configuration
type HandlerConfig struct {
	MaxWaitTime        time.Duration
	ContainerEnabled   bool
	ProxyLocalhostIPv4 string
	ProxyLocalhostIPv6 string
}

// NewHandlers creates a new Handlers instance
func NewHandlers(ctx context.Context, system SystemManager, config HandlerConfig) *Handlers {
	logger := tap.Logger(ctx)

	return &Handlers{
		logger:             logger,
		system:             system,
		maxWaitTime:        config.MaxWaitTime,
		containerEnabled:   config.ContainerEnabled,
		proxyLocalhostIPv4: config.ProxyLocalhostIPv4,
		proxyLocalhostIPv6: config.ProxyLocalhostIPv6,
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

// HandleLogs serves recent logs from the in-memory buffer with optional filtering
// Query params:
// - limit: int (default 100, max 10000)
// - level: debug|info|warn|error (min level). If debug=true, treated as level=debug
// - debug: true|false (shorthand for level=debug)
// - tags: comma-separated list; matches any
func (h *Handlers) HandleLogs(w http.ResponseWriter, r *http.Request) {
	buf := tap.GetLogBuffer()
	if buf == nil {
		http.Error(w, "log buffer unavailable", http.StatusServiceUnavailable)
		return
	}

	q := r.URL.Query()

	// limit
	limit := 100
	if s := q.Get("limit"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			if v > 10000 {
				v = 10000
			}
			limit = v
		}
	}

	// level / debug
	minLevel := slog.LevelInfo
	if q.Get("debug") == "true" {
		minLevel = slog.LevelDebug
	}
	if lv := strings.ToLower(q.Get("level")); lv != "" {
		switch lv {
		case "debug":
			minLevel = slog.LevelDebug
		case "info":
			minLevel = slog.LevelInfo
		case "warn", "warning":
			minLevel = slog.LevelWarn
		case "error":
			minLevel = slog.LevelError
		}
	}

	// tags
	var tags []string
	if t := q.Get("tags"); t != "" {
		parts := strings.Split(t, ",")
		for _, p := range parts {
			if s := strings.TrimSpace(p); s != "" {
				tags = append(tags, s)
			}
		}
	}

	entries := buf.Snapshot(limit, minLevel, tags)
	// Response shape: as captured
	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(entries); err != nil {
		h.logger.Error("Failed to encode logs response", "error", err)
	}
}
