package tap

import (
	"context"
	"log/slog"
	"sort"
	"strings"
	"sync"
	"time"
)

// LogEntry represents a captured log entry for in-memory retrieval
type LogEntry struct {
	Time     time.Time      `json:"time"`
	Level    slog.Level     `json:"-"`
	LevelStr string         `json:"level"`
	Message  string         `json:"msg"`
	Tags     []string       `json:"tags,omitempty"`
	Attrs    map[string]any `json:"attrs,omitempty"`
}

// LogBuffer is a fixed-size ring buffer storing recent LogEntry items
type LogBuffer struct {
	mu       sync.RWMutex
	entries  []LogEntry
	capacity int
	size     int
	head     int // next write index
}

func newLogBuffer(capacity int) *LogBuffer {
	if capacity <= 0 {
		capacity = 10000
	}
	return &LogBuffer{
		entries:  make([]LogEntry, capacity),
		capacity: capacity,
		size:     0,
		head:     0,
	}
}

func (b *LogBuffer) append(e LogEntry) {
	b.mu.Lock()
	b.entries[b.head] = e
	b.head = (b.head + 1) % b.capacity
	if b.size < b.capacity {
		b.size++
	}
	b.mu.Unlock()
}

// Snapshot returns up to limit latest entries filtered by minLevel and any matching tag.
// If tags is empty, no tag filtering is applied. Newest entries are returned first.
func (b *LogBuffer) Snapshot(limit int, minLevel slog.Level, tags []string) []LogEntry {
	if b == nil {
		return nil
	}
	if limit <= 0 {
		limit = 100
	}
	if limit > b.capacity {
		limit = b.capacity
	}

	// Build a fast lookup for tags if provided
	var tagSet map[string]struct{}
	if len(tags) > 0 {
		tagSet = make(map[string]struct{}, len(tags))
		for _, t := range tags {
			t = strings.TrimSpace(t)
			if t == "" {
				continue
			}
			tagSet[strings.ToLower(t)] = struct{}{}
		}
	}

	b.mu.RLock()
	defer b.mu.RUnlock()

	// Iterate from newest to oldest
	result := make([]LogEntry, 0, limit)
	for i := 0; i < b.size && len(result) < limit; i++ {
		idx := (b.head - 1 - i + b.capacity) % b.capacity
		e := b.entries[idx]
		if e.Level < minLevel {
			continue
		}
		if tagSet != nil {
			matched := false
			for _, tg := range e.Tags {
				if _, ok := tagSet[strings.ToLower(tg)]; ok {
					matched = true
					break
				}
			}
			if !matched {
				continue
			}
		}
		result = append(result, e)
	}

	return result
}

// bufferHandler is an slog.Handler that writes records into a LogBuffer
type bufferHandler struct {
	buffer      *LogBuffer
	attrs       []slog.Attr
	groupPrefix string
}

func newBufferHandler(buf *LogBuffer) *bufferHandler {
	return &bufferHandler{buffer: buf}
}

func (h *bufferHandler) Enabled(_ context.Context, _ slog.Level) bool {
	// Capture all levels; filtering is applied at read time
	return true
}

func (h *bufferHandler) Handle(ctx context.Context, r slog.Record) error {
	// Merge base attrs with record attrs
	attrs := make(map[string]any)
	// Apply base attrs
	for _, a := range h.attrs {
		addAttr(attrs, h.groupPrefix, a)
	}
	// Apply record attrs
	r.Attrs(func(a slog.Attr) bool {
		addAttr(attrs, h.groupPrefix, a)
		return true
	})

	// Extract tags from attrs: either "tag" string or "tags" slice
	var tags []string
	if v, ok := attrs["tag"]; ok {
		if s, ok2 := v.(string); ok2 && s != "" {
			tags = append(tags, s)
		}
	}
	if v, ok := attrs["tags"]; ok {
		switch tv := v.(type) {
		case []string:
			tags = append(tags, tv...)
		case []any:
			for _, it := range tv {
				if s, ok := it.(string); ok {
					tags = append(tags, s)
				}
			}
		}
	}
	// Remove tag fields from attrs to avoid duplication in output
	delete(attrs, "tag")
	delete(attrs, "tags")

	// Normalize order of tags for stable output
	if len(tags) > 1 {
		sort.Strings(tags)
	}

	h.buffer.append(LogEntry{
		Time:     r.Time,
		Level:    r.Level,
		LevelStr: r.Level.String(),
		Message:  r.Message,
		Tags:     tags,
		Attrs:    attrs,
	})
	return nil
}

func (h *bufferHandler) WithAttrs(attrs []slog.Attr) slog.Handler {
	// Copy existing
	nh := &bufferHandler{
		buffer:      h.buffer,
		attrs:       make([]slog.Attr, len(h.attrs)+len(attrs)),
		groupPrefix: h.groupPrefix,
	}
	copy(nh.attrs, h.attrs)
	copy(nh.attrs[len(h.attrs):], attrs)
	return nh
}

func (h *bufferHandler) WithGroup(name string) slog.Handler {
	if name == "" {
		return h
	}
	nh := &bufferHandler{
		buffer:      h.buffer,
		attrs:       append([]slog.Attr(nil), h.attrs...),
		groupPrefix: joinGroup(h.groupPrefix, name),
	}
	return nh
}

func addAttr(dst map[string]any, prefix string, a slog.Attr) {
	// Resolve value first (handles lazy attrs)
	a.Value = a.Value.Resolve()
	key := a.Key
	if prefix != "" {
		key = prefix + "." + key
	}
	switch a.Value.Kind() {
	case slog.KindGroup:
		g := a.Value.Group()
		for _, ga := range g {
			addAttr(dst, key, ga)
		}
	default:
		dst[key] = a.Value.Any()
	}
}

func joinGroup(prefix, name string) string {
	if prefix == "" {
		return name
	}
	return prefix + "." + name
}
