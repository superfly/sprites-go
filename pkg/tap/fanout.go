package tap

import (
	"context"
	"log/slog"
)

// multiHandler fans out records to multiple child handlers
type multiHandler struct {
	children []slog.Handler
}

func newMultiHandler(children ...slog.Handler) slog.Handler {
	// Flatten any nested multiHandlers
	flat := make([]slog.Handler, 0, len(children))
	for _, ch := range children {
		if mh, ok := ch.(*multiHandler); ok {
			flat = append(flat, mh.children...)
		} else {
			flat = append(flat, ch)
		}
	}
	return &multiHandler{children: flat}
}

func (h *multiHandler) Enabled(ctx context.Context, level slog.Level) bool {
	for _, ch := range h.children {
		if ch.Enabled(ctx, level) {
			return true
		}
	}
	return false
}

func (h *multiHandler) Handle(ctx context.Context, r slog.Record) error {
	var firstErr error
	for _, ch := range h.children {
		// Respect each child's level filter via Enabled
		if !ch.Enabled(ctx, r.Level) {
			continue
		}
		if err := ch.Handle(ctx, r); err != nil && firstErr == nil {
			firstErr = err
		}
	}
	return firstErr
}

func (h *multiHandler) WithAttrs(attrs []slog.Attr) slog.Handler {
	next := make([]slog.Handler, len(h.children))
	for i, ch := range h.children {
		next[i] = ch.WithAttrs(attrs)
	}
	return &multiHandler{children: next}
}

func (h *multiHandler) WithGroup(name string) slog.Handler {
	next := make([]slog.Handler, len(h.children))
	for i, ch := range h.children {
		next[i] = ch.WithGroup(name)
	}
	return &multiHandler{children: next}
}
