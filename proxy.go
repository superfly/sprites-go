package sprites

import (
	"context"
	"crypto/tls"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"os"
	"sync"
	"time"

	"github.com/gorilla/websocket"
)

// ProxySession represents an active port proxy session
type ProxySession struct {
	LocalPort  int
	RemotePort int
	RemoteHost string // Optional: specific host to connect to (e.g., "10.0.0.1", "fdf::1"). Defaults to "localhost" if empty.

	listener  net.Listener
	conn      *websocket.Conn
	ctx       context.Context
	cancel    context.CancelFunc
	closeOnce sync.Once
	closed    chan struct{}

	client     *Client
	spriteName string

	// fatalErr is set when a fatal error occurs (e.g., 404, 401, 403)
	fatalErr   error
	fatalErrMu sync.Mutex
}

// PortMapping represents a local to remote port mapping
type PortMapping struct {
	LocalPort  int
	RemotePort int
	RemoteHost string // Optional: specific host to connect to (e.g., "10.0.0.1", "fdf::1"). Defaults to "localhost" if empty.
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

// checkSpriteAccessible verifies the sprite is reachable before starting a proxy.
// This catches wrong org, wrong sprite name, and auth issues early.
func (c *Client) checkSpriteAccessible(ctx context.Context, spriteName string) error {
	url := fmt.Sprintf("%s/v1/sprites/%s/exec", c.baseURL, spriteName)

	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(req)
	if err != nil {
		return fmt.Errorf("failed to reach sprite: %w", err)
	}
	defer resp.Body.Close()

	switch resp.StatusCode {
	case http.StatusOK:
		return nil
	case http.StatusUnauthorized:
		return fmt.Errorf("unauthorized - check your API token")
	case http.StatusForbidden:
		return fmt.Errorf("forbidden - you don't have access to this sprite")
	case http.StatusNotFound:
		return fmt.Errorf("sprite %q not found - check sprite name and organization", spriteName)
	default:
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("unexpected status %d: %s", resp.StatusCode, string(body))
	}
}

// createProxySession creates a single proxy session
func (c *Client) createProxySession(ctx context.Context, spriteName string, mapping PortMapping) (*ProxySession, error) {
	// Preflight check: verify sprite is accessible before starting local listener
	// This catches wrong org, wrong sprite name, auth issues early
	if err := c.checkSpriteAccessible(ctx, spriteName); err != nil {
		return nil, fmt.Errorf("sprite not accessible: %w", err)
	}

	// Start local listener
	listener, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", mapping.LocalPort))
	if err != nil {
		return nil, fmt.Errorf("failed to listen on port %d: %w", mapping.LocalPort, err)
	}

	sessionCtx, cancel := context.WithCancel(ctx)

	session := &ProxySession{
		LocalPort:  mapping.LocalPort,
		RemotePort: mapping.RemotePort,
		RemoteHost: mapping.RemoteHost,
		listener:   listener,
		ctx:        sessionCtx,
		cancel:     cancel,
		closed:     make(chan struct{}),
		client:     c,
		spriteName: spriteName,
	}

	// Log start of proxy listening
	slog.Default().Debug("Starting proxy listener",
		"sprite", spriteName,
		"local", fmt.Sprintf("localhost:%d", session.LocalPort),
		"remote_host", func() string {
			if session.RemoteHost != "" {
				return session.RemoteHost
			}
			return "localhost"
		}(),
		"remote_port", session.RemotePort,
	)

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

		// Handle connection synchronously to detect fatal errors on first connection
		fatalErr := ps.handleConnection(conn)
		if fatalErr != nil {
			ps.setFatalError(fatalErr)
			slog.Default().Error("Fatal proxy error, closing session", "error", fatalErr)
			return
		}
	}
}

// setFatalError records a fatal error
func (ps *ProxySession) setFatalError(err error) {
	ps.fatalErrMu.Lock()
	defer ps.fatalErrMu.Unlock()
	if ps.fatalErr == nil {
		ps.fatalErr = err
	}
}

// Err returns the fatal error if one occurred
func (ps *ProxySession) Err() error {
	ps.fatalErrMu.Lock()
	defer ps.fatalErrMu.Unlock()
	return ps.fatalErr
}

// resetConnection closes a connection with TCP RST to simulate connection refused
func resetConnection(conn net.Conn) {
	if tcpConn, ok := conn.(*net.TCPConn); ok {
		tcpConn.SetLinger(0) // Send RST on close
	}
	conn.Close()
}

// handleConnection handles a single proxy connection.
// Returns a non-nil error for fatal errors (e.g., 404, 401, 403) that should close the session.
func (ps *ProxySession) handleConnection(localConn net.Conn) error {
	// Don't defer close here - we'll handle it explicitly to choose between clean close and RST

	slog.Default().Debug("Handling new proxy connection",
		"sprite", ps.spriteName,
		"remote_port", ps.RemotePort,
	)

	// Build WebSocket URL for proxy
	wsURL, err := ps.buildProxyURL()
	if err != nil {
		slog.Default().Debug("Failed to build proxy URL", "error", err)
		resetConnection(localConn)
		return nil // Not a fatal error
	}

	slog.Default().Debug("Dialing WebSocket", "url", wsURL.String())

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
	wsConn, resp, err := dialer.DialContext(ps.ctx, wsURL.String(), header)
	if err != nil {
		if resp != nil {
			slog.Default().Debug("WebSocket dial failed", "error", err, "status", resp.StatusCode)
			// Fatal errors: 401 (unauthorized), 403 (forbidden), 404 (not found)
			if resp.StatusCode == 401 || resp.StatusCode == 403 || resp.StatusCode == 404 {
				resetConnection(localConn)
				return fmt.Errorf("proxy connection failed: HTTP %d - %s", resp.StatusCode, http.StatusText(resp.StatusCode))
			}
		} else {
			slog.Default().Debug("WebSocket dial failed", "error", err)
		}
		resetConnection(localConn)
		return nil // Transient error, keep listening
	}
	defer wsConn.Close()

	slog.Default().Debug("WebSocket connected, sending init message")

	// Send initialization message
	// Use specified RemoteHost if provided, otherwise default to "localhost"
	host := ps.RemoteHost
	if host == "" {
		host = "localhost"
	}
	initMsg := ProxyInitMessage{
		Host: host,
		Port: ps.RemotePort,
	}

	if err := wsConn.WriteJSON(&initMsg); err != nil {
		slog.Default().Debug("Failed to send init message", "error", err)
		resetConnection(localConn)
		return nil
	}

	slog.Default().Debug("Init message sent, reading response")

	// Read response
	var response ProxyResponseMessage
	if err := wsConn.ReadJSON(&response); err != nil {
		slog.Default().Debug("Failed to read response", "error", err)
		// User-friendly warning with color (yellow) and timestamp
		timestamp := time.Now().Format("15:04:05")
		fmt.Fprintf(os.Stderr, "[%s] \033[33mWarning:\033[0m Connection to port %d failed: %v\n", timestamp, ps.RemotePort, err)
		resetConnection(localConn)
		return nil
	}

	slog.Default().Debug("Got proxy response", "status", response.Status, "target", response.Target)

	if response.Status != "connected" {
		slog.Default().Debug("Proxy not connected", "status", response.Status)
		timestamp := time.Now().Format("15:04:05")
		fmt.Fprintf(os.Stderr, "[%s] \033[33mWarning:\033[0m Connection to port %d failed: %s\n", timestamp, ps.RemotePort, response.Status)
		resetConnection(localConn)
		return nil
	}

	// Log established proxy connection with resolved target
	slog.Default().Debug("Proxy connection established",
		"sprite", ps.spriteName,
		"local", localConn.LocalAddr().String(),
		"remote_host", host,
		"remote_port", ps.RemotePort,
		"target", response.Target,
	)

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
	return nil // Connection handled successfully
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
