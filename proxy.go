package sprites

import (
	"context"
	"crypto/tls"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"strconv"
	"sync"
	"time"

	"github.com/gorilla/websocket"
)

const (
	// TODO: should this be configurable?
	proxyCloseDeadline = 1 * time.Second
)

// proxyConn wraps a WebSocket connection and implements [net.Conn].
type proxyConn struct {
	conn       *websocket.Conn
	remoteAddr *proxyAddr
	closeOnce  sync.Once

	readReader io.Reader // current message reader
	readMu     sync.Mutex
	writeMu    sync.Mutex
}

// proxyAddr implements [net.Addr].
type proxyAddr struct {
	network string
	address string
}

func (a *proxyAddr) Network() string {
	return a.network
}

func (a *proxyAddr) String() string {
	return a.address
}

func (conn *proxyConn) Read(p []byte) (n int, err error) {
	conn.readMu.Lock()
	defer conn.readMu.Unlock()

	for {
		// if we have a reader, read from it
		if conn.readReader != nil {
			n, err = conn.readReader.Read(p)
			if errors.Is(err, io.EOF) {
				// the current reader is empty, fetch the next frame
				conn.readReader = nil
				continue
			}
			return n, err
		}

		messageType, reader, err := conn.conn.NextReader()
		if err != nil {
			if websocket.IsCloseError(err, websocket.CloseNormalClosure, websocket.CloseGoingAway) {
				return 0, io.EOF
			}
			return 0, err
		}
		// only handle binary messages
		if messageType != websocket.BinaryMessage {
			continue
		}

		conn.readReader = reader
	}
}

func (conn *proxyConn) Write(p []byte) (n int, err error) {
	conn.writeMu.Lock()
	defer conn.writeMu.Unlock()

	err = conn.conn.WriteMessage(websocket.BinaryMessage, p)
	if err != nil {
		return 0, err
	}

	return len(p), nil
}

func (conn *proxyConn) Close() error {
	var closeErr error
	conn.closeOnce.Do(func() {
		// send close message with deadline
		deadline := time.Now().Add(proxyCloseDeadline)
		conn.conn.SetWriteDeadline(deadline)
		conn.conn.WriteControl(
			websocket.CloseMessage,
			websocket.FormatCloseMessage(websocket.CloseNormalClosure, ""),
			deadline,
		)
		closeErr = conn.conn.Close()
	})
	return closeErr
}

func (conn *proxyConn) LocalAddr() net.Addr {
	// there is no local address, return nil
	return nil
}
func (conn *proxyConn) RemoteAddr() net.Addr {
	return conn.remoteAddr
}

func (conn *proxyConn) SetDeadline(t time.Time) error {
	if err := conn.SetReadDeadline(t); err != nil {
		return err
	}
	return conn.SetWriteDeadline(t)
}
func (conn *proxyConn) SetReadDeadline(t time.Time) error {
	return conn.conn.SetReadDeadline(t)
}
func (conn *proxyConn) SetWriteDeadline(t time.Time) error {
	return conn.conn.SetWriteDeadline(t)
}

// controlProxyConn wraps a WebSocket connection and implements [net.Conn].
//
// It is identical to [proxyConn], except [controlProxyConn.Close] returns the
// WebSocket to the pool instead of closing it.
type controlProxyConn struct {
	*proxyConn
	control *controlConn
	pool    *controlPool
}

func (c *controlProxyConn) Close() error {
	c.closeOnce.Do(func() {
		// keep the socket open, but return it to the pool
		c.control.sendRelease()
		c.pool.checkin(c.control)
	})
	return nil
}

// ProxySocket establishes a proxied connection to a port on a sprite.
//
// The only known network is "tcp".
func (c *Client) ProxySocket(ctx context.Context, network, spriteName, addr string) (net.Conn, error) {
	switch network {
	case "tcp":
		wsConn, err := c.dialProxyWebSocket(ctx, spriteName)
		if err != nil {
			return nil, err
		}
		return initSocketTCP(ctx, wsConn, addr)
	default:
		return nil, fmt.Errorf("unsupported network type %q", network)
	}
}

// parseProxyAddr parses a proxy address into host and port components.
// Returns host (defaults to "localhost" if empty) and port (1-65535).
func parseProxyAddr(addr string) (host string, port int, err error) {
	host, portStr, err := net.SplitHostPort(addr)
	if err != nil {
		return "", 0, fmt.Errorf("invalid address %q: %w", addr, err)
	}

	portUint, err := strconv.ParseUint(portStr, 10, 16)
	if err != nil || portUint < 1 {
		return "", 0, fmt.Errorf("invalid port in address %q: must be 1-65535", addr)
	}

	if host == "" {
		host = "localhost"
	}

	return host, int(portUint), nil
}

// wsProxyHandshake sends a proxy initialization message and waits for a
// response. On successful connection, it returns the wrapped proxy.
func wsProxyHandshake(
	ctx context.Context, wsConn *websocket.Conn, initMsg any,
) (*proxyConn, error) {
	var response ProxyResponseMessage
	errChan := make(chan error, 1)

	// Race with ctx.Done in a goroutine
	go func() {
		var err error
		if err := wsConn.WriteJSON(initMsg); err != nil {
			err = fmt.Errorf("failed to send init message: %w", err)
		} else {
			// Read response
			if err := wsConn.ReadJSON(&response); err != nil {
				err = fmt.Errorf("failed to read response: %w", err)
			} else if response.Status != "connected" {
				err = fmt.Errorf("unexpected status: %s", response.Status)
			}
		}
		errChan <- err
	}()

	select {
	case <-ctx.Done():
		return nil, ctx.Err()
	case err := <-errChan:
		if err != nil {
			return nil, err
		}

		return &proxyConn{
			remoteAddr: &proxyAddr{
				network: "tcp",
				address: response.Target,
			},
			conn:       wsConn,
			readReader: nil,
		}, nil
	}
}

// initSocketTCP initializes a TCP proxy session over a WebSocket.
func initSocketTCP(ctx context.Context, wsConn *websocket.Conn, addr string) (net.Conn, error) {
	host, port, err := parseProxyAddr(addr)
	if err != nil {
		return nil, err
	}

	initMsg := &ProxyInitMessage{
		Host: host,
		Port: int(port),
	}
	return wsProxyHandshake(ctx, wsConn, initMsg)
}

// initControlSocketTCP initializes a TCP proxy session over a pooled control
// WebSocket.
func initControlSocketTCP(
	ctx context.Context,
	wsConn *websocket.Conn,
	addr string,
	control *controlConn,
	pool *controlPool,
) (net.Conn, error) {
	host, port, err := parseProxyAddr(addr)
	if err != nil {
		return nil, err
	}

	initMsg := map[string]any{
		"type":      "start",
		"operation": "proxy",
		"params": map[string]any{
			"host":       host,
			"port":       port,
			"keep_alive": true,
		},
	}
	proxyConn, err := wsProxyHandshake(ctx, wsConn, initMsg)
	if err != nil {
		return nil, err
	}

	return &controlProxyConn{
		proxyConn: proxyConn,
		control:   control,
		pool:      pool,
	}, nil
}

func (c *Client) dialProxyWebSocket(ctx context.Context, spriteName string) (*websocket.Conn, error) {
	// Build WebSocket URL for proxy
	wsURL, err := c.buildProxyURL(spriteName)
	if err != nil {
		return nil, err
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
	header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	header.Set("User-Agent", "sprites-go-sdk/1.0")
	header.Set("Sprite-Client-Features", "control")

	// Connect to WebSocket
	wsConn, _, err := dialer.DialContext(ctx, wsURL.String(), header)
	if err != nil {
		return nil, fmt.Errorf("failed to connect: %w", err)
	}

	return wsConn, nil
}

// ProxySession represents an active port proxy session
type ProxySession struct {
	LocalPort  int
	RemotePort int
	RemoteHost string // Optional: specific host to connect to (e.g., "10.0.0.1", "fdf::1"). Defaults to "localhost" if empty.

	listener  net.Listener
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

// ProxySocket establishes a proxied connection to a port on this sprite
func (s *Sprite) ProxySocket(ctx context.Context, network, addr string) (net.Conn, error) {
	return s.client.ProxySocket(ctx, network, s.name, addr)
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

	// Check if sprite supports control connections (lazy check on first use)
	sprite := ps.client.Sprite(ps.spriteName)
	sprite.ensureControlSupport(ps.ctx)

	var remoteConn net.Conn
	var err error
	addr := fmt.Sprintf("%s:%d", ps.RemoteHost, ps.RemotePort)

	if sprite.supportsControl {
		// Try to use control connection
		pool := ps.client.getOrCreatePool(ps.spriteName)
		controlConn, checkoutErr := pool.checkout(ps.ctx)

		if checkoutErr == nil && controlConn != nil {
			// Successfully got a control connection
			remoteConn, err = initControlSocketTCP(ps.ctx, controlConn.ws, addr, controlConn, pool)
			if err != nil {
				slog.Default().Debug("Pooled proxy initialization failed",
					"sprite", ps.spriteName,
					"error", err,
				)
				controlConn.sendRelease()
				pool.checkin(controlConn)
				return
			}
		}
	}

	if remoteConn == nil {
		// Fall back to direct WebSocket connection (legacy path or control unavailable)
		wsConn, dialErr := ps.client.dialProxyWebSocket(ps.ctx, ps.spriteName)
		if dialErr != nil {
			slog.Default().Debug("Proxy connection failed",
				"sprite", ps.spriteName,
				"error", dialErr,
			)
			return
		}

		remoteConn, err = initSocketTCP(ps.ctx, wsConn, addr)
		if err != nil {
			slog.Default().Debug("Proxy initialization failed",
				"sprite", ps.spriteName,
				"error", err,
			)
			wsConn.Close()
			return
		}
	}

	// Log established proxy connection with resolved target
	slog.Default().Debug("Proxy connection established",
		"sprite", ps.spriteName,
		"local", localConn.LocalAddr().String(),
		"remote_host", ps.RemoteHost,
		"remote_port", ps.RemotePort,
		"target", remoteConn.RemoteAddr(),
	)

	// Start bidirectional copy
	var wg sync.WaitGroup
	wg.Add(2)

	// Copy from local to remote
	go func() {
		defer wg.Done()
		defer remoteConn.Close()
		io.Copy(remoteConn, localConn)
	}()

	// Copy from remote to local
	go func() {
		defer wg.Done()
		defer localConn.Close()
		io.Copy(localConn, remoteConn)
	}()

	wg.Wait()
}

// buildProxyURL builds the WebSocket URL for the proxy endpoint
func (c *Client) buildProxyURL(spriteName string) (*url.URL, error) {
	baseURL := c.baseURL

	// Convert HTTP(S) to WS(S)
	if len(baseURL) >= 4 && baseURL[:4] == "http" {
		baseURL = "ws" + baseURL[4:]
	}

	// Parse base URL
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("invalid base URL: %w", err)
	}

	// Build path
	u.Path = fmt.Sprintf("/v1/sprites/%s/proxy", spriteName)

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
