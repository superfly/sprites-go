package api

import (
	"context"
)

// ContextEnricher is an interface for enriching request context
// The RequestEnd method accepts an interface{} to avoid import cycles
// Implementations should cast to the appropriate type
type ContextEnricher interface {
	EnrichContext(ctx context.Context) context.Context
	RequestEnd(ctx context.Context, info interface{})
}
