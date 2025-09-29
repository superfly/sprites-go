package sprites

import (
	"context"
	"crypto/tls"
	"fmt"
	"net"
	"net/http"
	"net/url"
	"sync"

	"github.com/gorilla/websocket"
)

// ProxySession represents an active port proxy session
type ProxySession struct {
	LocalPort  int
	RemotePort int

	listener  net.Listener
	conn      *websocket.Conn
	ctx       context.Context
	cancel    context.CancelFunc
	closeOnce sync.Once
	closed    chan struct{}

	client     *Client
	spriteName string
}

// PortMapping represents a local to remote port mapping
type PortMapping struct {
	LocalPort  int
	RemotePort int
}

// ProxyPort creates a proxy session for a single port
func (c *Client) ProxyPort(ctx context.Context, spriteName string, localPort, remotePort int) (*ProxySession, error) {
	mapping := PortMapping{
		LocalPort:  localPort,
		RemotePort: remotePort,
	}

	sessions, err := c.ProxyPorts(ctx, spriteName, []PortMapping{mapping})
	if err != nil {
		return nil, err
	}

	if len(sessions) != 1 {
		return nil, fmt.Errorf("unexpected number of proxy sessions created")
	}

	return sessions[0], nil
}

// ProxyPorts creates proxy sessions for multiple port mappings
func (c *Client) ProxyPorts(ctx context.Context, spriteName string, mappings []PortMapping) ([]*ProxySession, error) {
	var sessions []*ProxySession

	for _, mapping := range mappings {
		session, err := c.createProxySession(ctx, spriteName, mapping)
		if err != nil {
			// Clean up any sessions we already created
			for _, s := range sessions {
				s.Close()
			}
			return nil, fmt.Errorf("failed to create proxy for port %d: %w", mapping.LocalPort, err)
		}
		sessions = append(sessions, session)
	}

	return sessions, nil
}

// createProxySession creates a single proxy session
func (c *Client) createProxySession(ctx context.Context, spriteName string, mapping PortMapping) (*ProxySession, error) {
	// Start local listener
	listener, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", mapping.LocalPort))
	if err != nil {
		return nil, fmt.Errorf("failed to listen on port %d: %w", mapping.LocalPort, err)
	}

	sessionCtx, cancel := context.WithCancel(ctx)

	session := &ProxySession{
		LocalPort:  mapping.LocalPort,
		RemotePort: mapping.RemotePort,
		listener:   listener,
		ctx:        sessionCtx,
		cancel:     cancel,
		closed:     make(chan struct{}),
		client:     c,
		spriteName: spriteName,
	}

	// Start accepting connections
	go session.acceptLoop()

	return session, nil
}

// ProxyPort creates a proxy session for a single port on this sprite
func (s *Sprite) ProxyPort(ctx context.Context, localPort, remotePort int) (*ProxySession, error) {
	return s.client.ProxyPort(ctx, s.name, localPort, remotePort)
}

// ProxyPorts creates proxy sessions for multiple port mappings on this sprite
func (s *Sprite) ProxyPorts(ctx context.Context, mappings []PortMapping) ([]*ProxySession, error) {
	return s.client.ProxyPorts(ctx, s.name, mappings)
}

// acceptLoop accepts incoming connections and handles them
func (ps *ProxySession) acceptLoop() {
	defer ps.Close()

	for {
		select {
		case <-ps.ctx.Done():
			return
		case <-ps.closed:
			return
		default:
		}

		conn, err := ps.listener.Accept()
		if err != nil {
			select {
			case <-ps.ctx.Done():
				return
			case <-ps.closed:
				return
			default:
				// Log error but continue accepting
				continue
			}
		}

		// Handle connection in goroutine
		go ps.handleConnection(conn)
	}
}

// handleConnection handles a single proxy connection
func (ps *ProxySession) handleConnection(localConn net.Conn) {
	defer localConn.Close()

	// Build WebSocket URL for proxy
	wsURL, err := ps.buildProxyURL()
	if err != nil {
		return
	}

	// Set up WebSocket dialer
	dialer := &websocket.Dialer{
		ReadBufferSize:  1024 * 1024, // 1MB
		WriteBufferSize: 1024 * 1024, // 1MB
	}

	// Add TLS config if needed
	if wsURL.Scheme == "wss" {
		dialer.TLSClientConfig = &tls.Config{
			InsecureSkipVerify: false,
		}
	}

	// Set headers including auth
	header := http.Header{}
	header.Set("Authorization", fmt.Sprintf("Bearer %s", ps.client.token))
	header.Set("User-Agent", "sprites-go-sdk/1.0")

	// Connect to WebSocket
	wsConn, _, err := dialer.DialContext(ps.ctx, wsURL.String(), header)
	if err != nil {
		return
	}
	defer wsConn.Close()

	// Send initialization message
	initMsg := ProxyInitMessage{
		Host: "localhost",
		Port: ps.RemotePort,
	}

	if err := wsConn.WriteJSON(&initMsg); err != nil {
		return
	}

	// Read response
	var response ProxyResponseMessage
	if err := wsConn.ReadJSON(&response); err != nil {
		return
	}

	if response.Status != "connected" {
		return
	}

	// Start bidirectional copy
	var wg sync.WaitGroup
	wg.Add(2)

	// Copy from local to WebSocket
	go func() {
		defer wg.Done()
		defer wsConn.Close()

		buffer := make([]byte, 32*1024) // 32KB buffer
		for {
			n, err := localConn.Read(buffer)
			if err != nil {
				return
			}

			if err := wsConn.WriteMessage(websocket.BinaryMessage, buffer[:n]); err != nil {
				return
			}
		}
	}()

	// Copy from WebSocket to local
	go func() {
		defer wg.Done()
		defer localConn.Close()

		for {
			messageType, data, err := wsConn.ReadMessage()
			if err != nil {
				return
			}

			// Only forward binary messages
			if messageType == websocket.BinaryMessage {
				if _, err := localConn.Write(data); err != nil {
					return
				}
			}
		}
	}()

	wg.Wait()
}

// buildProxyURL builds the WebSocket URL for the proxy endpoint
func (ps *ProxySession) buildProxyURL() (*url.URL, error) {
	baseURL := ps.client.baseURL

	// Convert HTTP(S) to WS(S)
	if baseURL[:4] == "http" {
		baseURL = "ws" + baseURL[4:]
	}

	// Parse base URL
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("invalid base URL: %w", err)
	}

	// Build path
	u.Path = fmt.Sprintf("/v1/sprites/%s/proxy", ps.spriteName)

	return u, nil
}

// Close closes the proxy session
func (ps *ProxySession) Close() error {
	ps.closeOnce.Do(func() {
		close(ps.closed)
		ps.cancel()

		if ps.listener != nil {
			ps.listener.Close()
		}

		if ps.conn != nil {
			ps.conn.Close()
		}
	})

	return nil
}

// LocalAddr returns the local address of the proxy listener
func (ps *ProxySession) LocalAddr() net.Addr {
	if ps.listener != nil {
		return ps.listener.Addr()
	}
	return nil
}

// Wait waits for the proxy session to close
func (ps *ProxySession) Wait() {
	<-ps.closed
}

// ProxyManager manages multiple proxy sessions
type ProxyManager struct {
	sessions []*ProxySession
	mu       sync.Mutex
}

// NewProxyManager creates a new proxy manager
func NewProxyManager() *ProxyManager {
	return &ProxyManager{
		sessions: make([]*ProxySession, 0),
	}
}

// AddSession adds a session to the manager
func (pm *ProxyManager) AddSession(session *ProxySession) {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.sessions = append(pm.sessions, session)
}

// CloseAll closes all managed proxy sessions
func (pm *ProxyManager) CloseAll() {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	for _, session := range pm.sessions {
		session.Close()
	}

	pm.sessions = pm.sessions[:0]
}

// WaitAll waits for all proxy sessions to close
func (pm *ProxyManager) WaitAll() {
	pm.mu.Lock()
	sessions := make([]*ProxySession, len(pm.sessions))
	copy(sessions, pm.sessions)
	pm.mu.Unlock()

	for _, session := range sessions {
		session.Wait()
	}
}
