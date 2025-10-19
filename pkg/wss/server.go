package wss

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"strings"
	"sync"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// Server manages a control websocket with a single active operation at a time.
type Server struct {
	Router   *Router
	Upgrader gorillaws.Upgrader
	Logger   *slog.Logger
}

// Handle upgrades the request to a websocket and runs the control loop.
func (s *Server) Handle(w http.ResponseWriter, r *http.Request) {
	up := s.Upgrader
	if up.CheckOrigin == nil {
		up.CheckOrigin = func(r *http.Request) bool { return true }
	}
	conn, err := up.Upgrade(w, r, nil)
	if err != nil {
		if s.Logger != nil {
			s.Logger.Error("control: upgrade failed", "error", err)
		}
		http.Error(w, "websocket upgrade failed", http.StatusBadRequest)
		return
	}
	defer conn.Close()

	// Build controller and start read pump (single-threaded dispatcher)
	ctl := newController(s.Logger, conn, s.Router)
	go ctl.readPump(r.Context())

	// Optional URL param auto-start: enqueue as a control event
	q := r.URL.Query()
	if op := q.Get("op"); op != "" {
		args := cloneArgsExcluding(q, "op")
		// Enqueue synchronously via controller helper (non-blocking internal send)
		ctl.EnqueueOp("op.start", op, args)
	}

	// Wait for controller to finish (when connection closes)
	ctl.wait()
}

// controller coordinates control messages, single-op lifecycle, and buffering.
type controller struct {
	logger *slog.Logger
	conn   *gorillaws.Conn
	router *Router

	mu        sync.Mutex
	busy      bool
	events    chan controlEnvelope
	closeCh   chan struct{}
	activeBuf chan inboundMsg
	writeMu   sync.Mutex
}

type inboundMsg struct {
	msgType int
	data    []byte
}

func newController(logger *slog.Logger, conn *gorillaws.Conn, router *Router) *controller {
	if router == nil {
		router = NewRouter()
	}
	return &controller{
		logger:   logger,
		conn:     conn,
		router:   router,
		events:   make(chan controlEnvelope, 8),
		closeCh:  make(chan struct{}),
		// Bounded buffers: backpressure via readPump blocking when full
		activeBuf: make(chan inboundMsg, 256),
	}
}

// enqueue allows external goroutines to push a control envelope into the pump.
func (c *controller) enqueue(ev controlEnvelope) {
	select {
	case c.events <- ev:
	default:
		// best-effort; if full, drop rather than block
		if c.logger != nil {
			c.logger.Warn("control: dropping event due to full queue", "type", ev.Type)
		}
	}
}

// EnqueueOp converts URL args to a control envelope and enqueues it.
func (c *controller) EnqueueOp(msgType, op string, args url.Values) {
	m := map[string]any{}
	for k, vs := range args {
		if len(vs) == 1 {
			m[k] = vs[0]
		} else if len(vs) > 1 {
			a := make([]any, 0, len(vs))
			for _, v := range vs {
				a = append(a, v)
			}
			m[k] = a
		}
	}
	c.enqueue(controlEnvelope{Type: msgType, Op: op, Args: m})
}

// opConn adapts controller buffers to a gorilla-like connection for handlers.
type opConn struct {
	ctl *controller
}

func (c *opConn) ReadMessage() (int, []byte, error) {
	msg, ok := <-c.ctl.activeBuf
	if !ok {
		return 0, nil, errors.New("connection closed")
	}
	return msg.msgType, msg.data, nil
}

func (c *opConn) NextReader() (int, io.Reader, error) {
	mt, data, err := c.ReadMessage()
	if err != nil {
		return 0, nil, err
	}
	return mt, &sliceReader{b: data}, nil
}

func (c *opConn) WriteMessage(mt int, data []byte) error {
	c.ctl.writeMu.Lock()
	defer c.ctl.writeMu.Unlock()
	return c.ctl.conn.WriteMessage(mt, data)
}

func (c *opConn) WriteJSON(v any) error {
	c.ctl.writeMu.Lock()
	defer c.ctl.writeMu.Unlock()
	return c.ctl.conn.WriteJSON(v)
}

func (c *opConn) Close() error {
	return c.ctl.conn.Close()
}

type sliceReader struct{ b []byte }

func (r *sliceReader) Read(p []byte) (int, error) {
	if len(r.b) == 0 {
		return 0, errors.New("EOF")
	}
	n := copy(p, r.b)
	r.b = r.b[n:]
	return n, nil
}

// readPump continuously reads frames, extracting control messages and queuing others.
func (c *controller) readPump(ctx context.Context) {
	defer close(c.closeCh)

	for {
		// Drain any pending internal control events first
		for {
			select {
			case ev := <-c.events:
				c.handleControl(ctx, ev)
				continue
			default:
			}
			break
		}

		// Set a short read deadline so we can wake to process events
		_ = c.conn.SetReadDeadline(time.Now().Add(100 * time.Millisecond))
		mt, data, err := c.conn.ReadMessage()
		if err != nil {
			if ne, ok := err.(net.Error); ok && ne.Timeout() {
				// Timeout: loop to process events and try reading again
				continue
			}
			// Signal close by closing buffers
			close(c.activeBuf)
			return
		}

		// Only text frames can be control messages
		if mt == gorillaws.TextMessage && isControlFrame(data) {
			var msg controlEnvelope
			if err := json.Unmarshal(data[len("control:"):], &msg); err == nil {
				c.handleControl(ctx, msg)
				continue
			}
			// fallthrough on decode error
		}

		c.mu.Lock()
		busy := c.busy
		c.mu.Unlock()
		if busy {
			c.activeBuf <- inboundMsg{msgType: mt, data: data}
		} else {
			// No active operation: reject non-control frames
			_ = c.sendControl(controlEnvelope{Type: "op.error", Args: map[string]any{"code": "op.not_active", "message": "no operation active; send control:op.start"}})
		}
	}
}

func isControlFrame(data []byte) bool {
	return len(data) >= len("control:") && strings.HasPrefix(string(data), "control:")
}

type controlEnvelope struct {
	Type string         `json:"type"`
	ID   string         `json:"id"`
	Op   string         `json:"op,omitempty"`
	Args map[string]any `json:"args,omitempty"`
}

func (c *controller) handleControl(ctx context.Context, msg controlEnvelope) {
	switch msg.Type {
	case "op.start":
		args := url.Values{}
		for k, v := range msg.Args {
			switch vv := v.(type) {
			case string:
				args.Add(k, vv)
			case []any:
				for _, item := range vv {
					if s, ok := item.(string); ok {
						args.Add(k, s)
					}
				}
			}
		}
		_ = c.startOperation(ctx, msg.Op, args, msg.ID)
	default:
		// Unknown control message types can be ignored for now
	}
}

func (c *controller) startOperation(ctx context.Context, op string, args url.Values, cid string) error {
	if op == "" {
		return nil
	}
	h := c.router.get(op)
	if h == nil {
		_ = c.sendControl(controlEnvelope{Type: "op.error", ID: cid, Op: op, Args: map[string]any{"code": "op.not_found", "message": "unknown operation"}})
		return nil
	}

	c.mu.Lock()
	if c.busy {
		c.mu.Unlock()
		_ = c.sendControl(controlEnvelope{Type: "op.error", ID: cid, Op: op, Args: map[string]any{"code": "op.busy", "message": "operation already running"}})
		return nil
	}
	c.busy = true
	c.mu.Unlock()

	_ = c.sendControl(controlEnvelope{Type: "op.ack", ID: cid})

	// Build op context and opConn
	opCtx, cancel := context.WithCancel(ctx)
	oc := &opConn{ctl: c}

	// Run handler
	go func() {
		defer cancel()
		err := h(opCtx, oc, args)
		if err != nil {
			_ = c.sendControl(controlEnvelope{Type: "op.complete", ID: cid, Args: map[string]any{"ok": false, "error": err.Error()}})
		} else {
			_ = c.sendControl(controlEnvelope{Type: "op.complete", ID: cid, Args: map[string]any{"ok": true}})
		}
		// Mark idle
		c.mu.Lock()
		c.busy = false
		c.mu.Unlock()
	}()
	return nil
}

func (c *controller) sendControl(env controlEnvelope) error {
	c.writeMu.Lock()
	defer c.writeMu.Unlock()
	b, _ := json.Marshal(env)
	payload := append([]byte("control:"), b...)
	return c.conn.WriteMessage(gorillaws.TextMessage, payload)
}

func (c *controller) wait() {
	// Block until the underlying conn closes (readPump returns)
	<-c.closeCh
}

func cloneArgsExcluding(q url.Values, keys ...string) url.Values {
	out := url.Values{}
	skip := map[string]struct{}{}
	for _, k := range keys {
		skip[k] = struct{}{}
	}
	for k, vs := range q {
		if _, ok := skip[k]; ok {
			continue
		}
		for _, v := range vs {
			out.Add(k, v)
		}
	}
	return out
}
