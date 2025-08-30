package handlers

import (
	"context"
	"time"
)

// RequestInfo contains information about a request
type RequestInfo struct {
	RequestID   string
	Method      string
	Path        string
	StartTime   time.Time
	EndTime     time.Time
	DurationMS  int64
	StatusCode  int
	Error       error
	RequestType string // "exec" or "proxy"
	ExtraData   map[string]interface{}
}

// ContextEnricher is an interface for enriching request context
type ContextEnricher interface {
	EnrichContext(ctx context.Context) context.Context
	RequestEnd(ctx context.Context, info interface{})
}

// contextEnricherKey is the key for storing the enricher in context
type contextEnricherKey struct{}
