package wss

import (
	"context"
	"net/url"
	"sync"
)

// OperationHandler is the function signature for a control operation.
// The handler is responsible for running the operation and returning when it is complete.
// While running, the handler has exclusive ownership of non-control websocket frames
// via the provided OpConn.
type OperationHandler func(ctx context.Context, c OpConn, args url.Values) error

// Router maintains the mapping of operation names to handlers.
type Router struct {
	mu       sync.RWMutex
	handlers map[string]OperationHandler
}

// NewRouter creates a new empty Router.
func NewRouter() *Router {
	return &Router{handlers: make(map[string]OperationHandler)}
}

// Handle registers a handler for the given operation name.
func (r *Router) Handle(op string, h OperationHandler) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.handlers[op] = h
}

// get returns the handler for the given operation name, or nil if not found.
func (r *Router) get(op string) OperationHandler {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.handlers[op]
}
