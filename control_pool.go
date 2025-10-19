package sprites

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"net/http"
	"net/url"
	"sync"
	"time"

	"github.com/gorilla/websocket"
)

const (
	maxPoolSize     = 10
	dialTimeout     = 5 * time.Second
	keepAliveWindow = 30 * time.Second
)

// controlPool manages a pool of control WebSocket connections for a sprite
type controlPool struct {
	client     *Client
	spriteName string
	mu         sync.Mutex
	conns      []*controlConn
	closed     bool
}

// controlConn represents a control WebSocket connection
type controlConn struct {
	ws        *websocket.Conn
	mu        sync.Mutex
	busy      bool
	lastUsed  time.Time
	ctx       context.Context
	cancel    context.CancelFunc
	readCh    chan controlMessage
	closedCh  chan struct{}
	closeOnce sync.Once
}

// controlMessage represents a message on the control connection
type controlMessage struct {
	MessageType int    // WebSocket message type (binary or text)
	Data        []byte // Raw message data
}

// newControlPool creates a new control connection pool for a sprite
func newControlPool(client *Client, spriteName string) *controlPool {
	return &controlPool{
		client:     client,
		spriteName: spriteName,
		conns:      make([]*controlConn, 0, maxPoolSize),
	}
}

// checkout gets an idle connection from the pool, or creates a new one if needed
func (p *controlPool) checkout(ctx context.Context) (*controlConn, error) {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.closed {
		return nil, fmt.Errorf("pool is closed")
	}

	// Try to find an idle connection
	for i, conn := range p.conns {
		conn.mu.Lock()
		if !conn.busy {
			// Check if connection is still alive
			select {
			case <-conn.closedCh:
				// Connection is closed, remove it
				conn.mu.Unlock()
				p.conns = append(p.conns[:i], p.conns[i+1:]...)
				dbg("sprites: removed closed control conn", "sprite", p.spriteName, "pool", len(p.conns))
				continue
			default:
			}

			conn.busy = true
			conn.mu.Unlock()
			dbg("sprites: checkout control conn", "sprite", p.spriteName, "pool", len(p.conns))
			return conn, nil
		}
		conn.mu.Unlock()
	}

	// No idle connections, create a new one if under limit
	if len(p.conns) < maxPoolSize {
		conn, err := p.dial(ctx)
		if err != nil {
			return nil, err
		}
		conn.busy = true
		p.conns = append(p.conns, conn)
		dbg("sprites: dialed new control conn", "sprite", p.spriteName, "pool", len(p.conns))
		return conn, nil
	}

	return nil, fmt.Errorf("no available connections in pool")
}

// checkin returns a connection to the pool
func (p *controlPool) checkin(conn *controlConn) {
	if conn == nil {
		return
	}

	conn.mu.Lock()
	defer conn.mu.Unlock()

	conn.busy = false
	conn.lastUsed = time.Now()
	dbg("sprites: checkin control conn", "sprite", p.spriteName, "idle_at", conn.lastUsed.Unix())
}

// dial creates a new control WebSocket connection
func (p *controlPool) dial(ctx context.Context) (*controlConn, error) {
	wsURL, err := p.buildControlURL()
	if err != nil {
		return nil, err
	}

	// Set up WebSocket dialer
	dialer := &websocket.Dialer{
		ReadBufferSize:   1024 * 1024, // 1MB
		WriteBufferSize:  1024 * 1024, // 1MB
		HandshakeTimeout: dialTimeout,
	}

	// Add TLS config if needed
	if wsURL.Scheme == "wss" {
		dialer.TLSClientConfig = &tls.Config{
			InsecureSkipVerify: false,
		}
	}

	// Set headers including auth and feature flag
	header := http.Header{}
	header.Set("Authorization", fmt.Sprintf("Bearer %s", p.client.token))
	header.Set("User-Agent", "sprites-go-sdk/1.0")

    // Connect to WebSocket
    ws, resp, err := dialer.DialContext(ctx, wsURL.String(), header)
    if err != nil {
        // Enrich error with HTTP status/body when available
        if resp != nil {
            body, _ := io.ReadAll(resp.Body)
            _ = resp.Body.Close()
            return nil, fmt.Errorf("failed to dial control connection: %v (HTTP %d: %s)", err, resp.StatusCode, string(body))
        }
        return nil, fmt.Errorf("failed to dial control connection: %v", err)
    }

	connCtx, cancel := context.WithCancel(context.Background())

	conn := &controlConn{
		ws:       ws,
		lastUsed: time.Now(),
		ctx:      connCtx,
		cancel:   cancel,
		readCh:   make(chan controlMessage, 1000), // Large buffer to prevent blocking
		closedCh: make(chan struct{}),
	}

	// Start read loop
	go conn.readLoop()

	dbg("sprites: created control conn", "sprite", p.spriteName, "pool_size", len(p.conns)+1)

	return conn, nil
}

// buildControlURL builds the WebSocket URL for the control endpoint
func (p *controlPool) buildControlURL() (*url.URL, error) {
	baseURL := p.client.baseURL

	// Convert HTTP(S) to WS(S)
	if len(baseURL) >= 4 && baseURL[:4] == "http" {
		baseURL = "ws" + baseURL[4:]
	}

	// Parse base URL
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("invalid base URL: %w", err)
	}

	// Build path (no keep_alive in URL - that's in operation params)
	u.Path = fmt.Sprintf("/v1/sprites/%s/control", p.spriteName)

	return u, nil
}

// close closes all connections in the pool
func (p *controlPool) close() {
	p.mu.Lock()
	defer p.mu.Unlock()

	p.closed = true
	for _, conn := range p.conns {
		conn.close()
	}
	p.conns = nil
}

// readLoop continuously reads messages from the control connection
func (c *controlConn) readLoop() {
	defer func() {
		c.closeOnce.Do(func() {
			close(c.closedCh)
		})
	}()

	for {
		select {
		case <-c.ctx.Done():
			return
		default:
		}

		// Read next message (could be JSON or binary)
		messageType, data, err := c.ws.ReadMessage()
		if err != nil {
			// Connection closed or error
			return
		}

		// Create message wrapper
		msg := controlMessage{
			MessageType: messageType,
			Data:        data,
		}

		// Check if connection is busy (in use by an operation)
		c.mu.Lock()
		busy := c.busy
		c.mu.Unlock()

		if busy {
			// Connection is busy - forward message to operation
			select {
			case c.readCh <- msg:
			case <-c.ctx.Done():
				return
			}
		} else {
			// Connection is idle - handle control messages
			if messageType == websocket.TextMessage {
				// Try to parse as control message
				var ctrlMsg struct {
					Type string `json:"type"`
				}
				if json.Unmarshal(data, &ctrlMsg) == nil {
					switch ctrlMsg.Type {
					case "dial":
						// Server is requesting a new connection - ignore in SDK
					case "keepalive":
						// Keepalive message - stay alive
					default:
						// Unknown message type
					}
				}
			}
			// Binary messages while idle are unexpected, ignore
		}
	}
}

// close closes the control connection
func (c *controlConn) close() {
	c.closeOnce.Do(func() {
		c.cancel()
		if c.ws != nil {
			c.ws.Close()
		}
		close(c.closedCh)
	})
}

// sendRelease sends a release message to return the connection to the pool
func (c *controlConn) sendRelease() error {
	c.mu.Lock()
	defer c.mu.Unlock()

	msg := map[string]interface{}{
		"type": "release",
	}

	return c.ws.WriteJSON(msg)
}
