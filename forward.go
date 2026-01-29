package sprites

import (
	"context"
	"crypto/tls"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"sync"
	"sync/atomic"

	"github.com/gorilla/websocket"
)

// ForwardMapping describes a socket/port forwarding from sprite to local.
// When a process in the sprite connects to the remote socket/port,
// the connection is tunneled to the local socket/port.
type ForwardMapping struct {
	// LocalSocket is the local Unix socket path to connect to.
	// Either LocalSocket or LocalPort must be set.
	LocalSocket string

	// LocalPort is the local TCP port to connect to.
	// Either LocalSocket or LocalPort must be set.
	LocalPort int

	// RemoteSocket is the Unix socket path to create in the sprite.
	// Processes in the sprite connect to this socket.
	// Either RemoteSocket or RemotePort must be set.
	RemoteSocket string

	// RemotePort is the TCP port to listen on in the sprite.
	// Processes in the sprite connect to this port.
	// Either RemoteSocket or RemotePort must be set.
	RemotePort int

	// RemoteHost is the host to listen on in the sprite (for TCP only).
	// Defaults to "localhost".
	RemoteHost string
}

// ForwardSession manages forwarding from sprite to local.
// When processes in the sprite connect to the remote socket/port,
// those connections are tunneled to the local socket/port.
type ForwardSession struct {
	client     *Client
	spriteName string
	conn       *websocket.Conn

	mu       sync.Mutex
	forwards map[uint64]*activeForward  // forwardID -> forward info
	channels map[uint64]*forwardChannel // channelID -> channel

	ctx       context.Context
	cancel    context.CancelFunc
	closeOnce sync.Once
	closed    chan struct{}
	wg        sync.WaitGroup
}

type activeForward struct {
	id          uint64
	mapping     ForwardMapping
	socketPath  string
	listenAddr  string
}

// ForwardInfo describes an established forward.
type ForwardInfo struct {
	ForwardID  uint64
	Mapping    ForwardMapping
	SocketPath string // actual path inside the sprite
	ListenAddr string // TCP address if relay is active (e.g., "localhost:25002")
}

// Forwards returns info about all established forwards.
func (fs *ForwardSession) Forwards() []ForwardInfo {
	fs.mu.Lock()
	defer fs.mu.Unlock()

	result := make([]ForwardInfo, 0, len(fs.forwards))
	for _, fwd := range fs.forwards {
		result = append(result, ForwardInfo{
			ForwardID:  fwd.id,
			Mapping:    fwd.mapping,
			SocketPath: fwd.socketPath,
			ListenAddr: fwd.listenAddr,
		})
	}
	return result
}

type forwardChannel struct {
	id       uint64
	conn     net.Conn
	session  *ForwardSession
	closed   atomic.Bool
}

// ForwardInitMessage is sent to create a forward.
type ForwardInitMessage struct {
	Type       string `json:"type"`
	SocketType string `json:"socket_type"`
	SocketPath string `json:"socket_path,omitempty"`
	Host       string `json:"host,omitempty"`
	Port       int    `json:"port,omitempty"`
}

// ForwardInitResponse is the response to a forward init.
type ForwardInitResponse struct {
	Type       string `json:"type"`
	Success    bool   `json:"success"`
	ForwardID  uint64 `json:"forward_id"`
	SocketPath string `json:"socket_path"`
	ListenAddr string `json:"listen_addr,omitempty"`
	Error      string `json:"error,omitempty"`
}

// ForwardConnectMessage is sent when a connection is made to a forwarded socket.
type ForwardConnectMessage struct {
	Type      string `json:"type"`
	ChannelID uint64 `json:"channel_id"`
	ForwardID uint64 `json:"forward_id"`
	PeerPID   int    `json:"peer_pid,omitempty"`
}

// ForwardCloseMessage is sent when a channel closes.
type ForwardCloseMessage struct {
	Type      string `json:"type"`
	ChannelID uint64 `json:"channel_id"`
}

// Forward creates a new forward session for the given mappings.
func (c *Client) Forward(ctx context.Context, spriteName string, mappings []ForwardMapping) (*ForwardSession, error) {
	// Build WebSocket URL
	wsURL, err := buildForwardURL(c.baseURL, spriteName)
	if err != nil {
		return nil, err
	}

	slog.Default().Debug("Forward connecting", "url", wsURL.String(), "base_url", c.baseURL, "sprite", spriteName)

	// Set up WebSocket dialer
	dialer := &websocket.Dialer{
		ReadBufferSize:  1024 * 1024,
		WriteBufferSize: 1024 * 1024,
	}
	if wsURL.Scheme == "wss" {
		dialer.TLSClientConfig = &tls.Config{
			InsecureSkipVerify: false,
		}
	}

	// Set headers
	header := http.Header{}
	header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	header.Set("User-Agent", "sprites-go-sdk/1.0")

	// Connect
	wsConn, resp, err := dialer.DialContext(ctx, wsURL.String(), header)
	if err != nil {
		if resp != nil {
			slog.Default().Debug("Forward connection failed", "status", resp.StatusCode, "error", err)
		}
		return nil, fmt.Errorf("connecting to forward endpoint: %w", err)
	}

	sessionCtx, cancel := context.WithCancel(ctx)

	session := &ForwardSession{
		client:     c,
		spriteName: spriteName,
		conn:       wsConn,
		forwards:   make(map[uint64]*activeForward),
		channels:   make(map[uint64]*forwardChannel),
		ctx:        sessionCtx,
		cancel:     cancel,
		closed:     make(chan struct{}),
	}

	// Create forwards for each mapping.
	// This must happen before starting the readLoop because createForward
	// uses ReadJSON to get the init response synchronously.
	for _, mapping := range mappings {
		if err := session.createForward(mapping); err != nil {
			session.Close()
			return nil, err
		}
	}

	// Start reading messages after all forwards are established.
	// The readLoop handles forward_connect, forward_close, and binary data.
	session.wg.Add(1)
	go session.readLoop()

	return session, nil
}

// Forward creates a forward session on this sprite.
func (s *Sprite) Forward(ctx context.Context, mappings []ForwardMapping) (*ForwardSession, error) {
	return s.client.Forward(ctx, s.name, mappings)
}

func (fs *ForwardSession) createForward(mapping ForwardMapping) error {
	// Determine socket type and send init message
	var initMsg ForwardInitMessage
	initMsg.Type = "forward_init"

	if mapping.RemoteSocket != "" {
		initMsg.SocketType = "unix"
		initMsg.SocketPath = mapping.RemoteSocket
	} else if mapping.RemotePort > 0 {
		initMsg.SocketType = "tcp"
		initMsg.Host = mapping.RemoteHost
		if initMsg.Host == "" {
			initMsg.Host = "localhost"
		}
		initMsg.Port = mapping.RemotePort
	} else {
		return fmt.Errorf("mapping must specify RemoteSocket or RemotePort")
	}

	// Send init message
	slog.Default().Debug("Sending forward_init", "type", initMsg.SocketType, "path", initMsg.SocketPath, "port", initMsg.Port)
	if err := fs.conn.WriteJSON(initMsg); err != nil {
		return fmt.Errorf("sending forward_init: %w", err)
	}

	// Read response
	slog.Default().Debug("Waiting for forward_init_response")
	var resp ForwardInitResponse
	if err := fs.conn.ReadJSON(&resp); err != nil {
		return fmt.Errorf("reading forward_init_response: %w", err)
	}

	slog.Default().Debug("Got forward_init_response", "success", resp.Success, "forward_id", resp.ForwardID, "socket_path", resp.SocketPath, "error", resp.Error)

	if !resp.Success {
		return fmt.Errorf("forward failed: %s", resp.Error)
	}

	// Store forward info - when sprite-side connections come in,
	// handleRemoteConnect will use this mapping to connect locally
	fs.mu.Lock()
	fs.forwards[resp.ForwardID] = &activeForward{
		id:         resp.ForwardID,
		mapping:    mapping,
		socketPath: resp.SocketPath,
		listenAddr: resp.ListenAddr,
	}
	fs.mu.Unlock()

	// Log what we're forwarding
	var localTarget string
	if mapping.LocalSocket != "" {
		localTarget = mapping.LocalSocket
	} else {
		localTarget = fmt.Sprintf("localhost:%d", mapping.LocalPort)
	}

	slog.Default().Debug("Forward established",
		"sprite", fs.spriteName,
		"remote", resp.SocketPath,
		"local", localTarget,
	)

	return nil
}

func (ch *forwardChannel) readLoop() {
	defer ch.session.wg.Done()
	defer ch.close()

	buf := make([]byte, 32*1024)
	for {
		n, err := ch.conn.Read(buf)
		if err != nil {
			return
		}

		if n > 0 {
			// Send to sprite: [0x05][channelID:4 bytes BE][data]
			msg := make([]byte, 5+n)
			msg[0] = 0x05
			binary.BigEndian.PutUint32(msg[1:5], uint32(ch.id))
			copy(msg[5:], buf[:n])

			ch.session.mu.Lock()
			err := ch.session.conn.WriteMessage(websocket.BinaryMessage, msg)
			ch.session.mu.Unlock()

			if err != nil {
				return
			}
		}
	}
}

func (ch *forwardChannel) write(data []byte) error {
	if ch.closed.Load() {
		return fmt.Errorf("channel closed")
	}
	_, err := ch.conn.Write(data)
	return err
}

func (ch *forwardChannel) close() {
	if !ch.closed.CompareAndSwap(false, true) {
		return
	}

	ch.conn.Close()

	// Remove from session
	ch.session.mu.Lock()
	delete(ch.session.channels, ch.id)
	ch.session.mu.Unlock()

	// Notify sprite
	closeMsg := ForwardCloseMessage{
		Type:      "forward_close",
		ChannelID: ch.id,
	}
	ch.session.mu.Lock()
	_ = ch.session.conn.WriteJSON(closeMsg)
	ch.session.mu.Unlock()
}

func (fs *ForwardSession) readLoop() {
	defer fs.wg.Done()

	for {
		messageType, data, err := fs.conn.ReadMessage()
		if err != nil {
			select {
			case <-fs.ctx.Done():
			case <-fs.closed:
			default:
				slog.Default().Debug("Forward read error", "error", err)
			}
			return
		}

		switch messageType {
		case websocket.TextMessage:
			fs.handleTextMessage(data)

		case websocket.BinaryMessage:
			// Data from sprite: [0x05][channelID:4 bytes BE][data]
			if len(data) < 5 || data[0] != 0x05 {
				continue
			}
			channelID := uint64(binary.BigEndian.Uint32(data[1:5]))
			payload := data[5:]

			fs.mu.Lock()
			ch, exists := fs.channels[channelID]
			fs.mu.Unlock()

			if exists {
				if err := ch.write(payload); err != nil {
					ch.close()
				}
			}
		}
	}
}

func (fs *ForwardSession) handleTextMessage(data []byte) {
	var baseMsg struct {
		Type string `json:"type"`
	}
	if err := json.Unmarshal(data, &baseMsg); err != nil {
		return
	}

	switch baseMsg.Type {
	case "forward_connect":
		var msg ForwardConnectMessage
		if err := json.Unmarshal(data, &msg); err != nil {
			return
		}
		// This is a connection TO the sprite's socket.
		// We need to connect to our local socket/port and bridge them.
		fs.handleRemoteConnect(msg)

	case "forward_close":
		var msg ForwardCloseMessage
		if err := json.Unmarshal(data, &msg); err != nil {
			return
		}
		fs.mu.Lock()
		ch, exists := fs.channels[msg.ChannelID]
		fs.mu.Unlock()
		if exists {
			ch.close()
		}
	}
}

func (fs *ForwardSession) handleRemoteConnect(msg ForwardConnectMessage) {
	// Find the forward
	fs.mu.Lock()
	fwd, exists := fs.forwards[msg.ForwardID]
	fs.mu.Unlock()

	if !exists {
		slog.Default().Debug("Unknown forward ID", "forward_id", msg.ForwardID)
		return
	}

	// Connect to local socket/port
	var conn net.Conn
	var err error

	if fwd.mapping.LocalSocket != "" {
		conn, err = net.Dial("unix", fwd.mapping.LocalSocket)
	} else if fwd.mapping.LocalPort > 0 {
		conn, err = net.Dial("tcp", fmt.Sprintf("localhost:%d", fwd.mapping.LocalPort))
	} else {
		slog.Default().Debug("Forward has no local target", "forward_id", msg.ForwardID)
		return
	}

	if err != nil {
		slog.Default().Debug("Failed to connect to local target", "error", err)
		// Send close to sprite
		closeMsg := ForwardCloseMessage{
			Type:      "forward_close",
			ChannelID: msg.ChannelID,
		}
		fs.mu.Lock()
		_ = fs.conn.WriteJSON(closeMsg)
		fs.mu.Unlock()
		return
	}

	// Create channel
	ch := &forwardChannel{
		id:      msg.ChannelID,
		conn:    conn,
		session: fs,
	}

	fs.mu.Lock()
	fs.channels[msg.ChannelID] = ch
	fs.mu.Unlock()

	// Start reading from local connection
	fs.wg.Add(1)
	go ch.readLoop()

	slog.Default().Debug("Bridged remote connection to local",
		"channel_id", msg.ChannelID,
		"peer_pid", msg.PeerPID,
	)
}

// Close closes the forward session.
func (fs *ForwardSession) Close() error {
	fs.closeOnce.Do(func() {
		close(fs.closed)
		fs.cancel()

		// Close all channels
		fs.mu.Lock()
		for _, ch := range fs.channels {
			ch.conn.Close()
		}
		fs.channels = make(map[uint64]*forwardChannel)
		fs.mu.Unlock()

		// Close WebSocket
		if fs.conn != nil {
			fs.conn.Close()
		}
	})

	return nil
}

// Wait waits for the forward session to close.
func (fs *ForwardSession) Wait() {
	<-fs.closed
}

func buildForwardURL(baseURL, spriteName string) (*url.URL, error) {
	// Convert HTTP(S) to WS(S)
	if len(baseURL) >= 4 && baseURL[:4] == "http" {
		baseURL = "ws" + baseURL[4:]
	}

	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("invalid base URL: %w", err)
	}

	u.Path = fmt.Sprintf("/v1/sprites/%s/forward", spriteName)
	return u, nil
}

// ForwardManager manages multiple forward sessions.
type ForwardManager struct {
	sessions []*ForwardSession
	mu       sync.Mutex
}

// NewForwardManager creates a new forward manager.
func NewForwardManager() *ForwardManager {
	return &ForwardManager{
		sessions: make([]*ForwardSession, 0),
	}
}

// AddSession adds a session to the manager.
func (fm *ForwardManager) AddSession(session *ForwardSession) {
	fm.mu.Lock()
	defer fm.mu.Unlock()
	fm.sessions = append(fm.sessions, session)
}

// CloseAll closes all managed forward sessions.
func (fm *ForwardManager) CloseAll() {
	fm.mu.Lock()
	defer fm.mu.Unlock()

	for _, session := range fm.sessions {
		session.Close()
	}
	fm.sessions = fm.sessions[:0]
}

// WaitAll waits for all forward sessions to close.
func (fm *ForwardManager) WaitAll() {
	fm.mu.Lock()
	sessions := make([]*ForwardSession, len(fm.sessions))
	copy(sessions, fm.sessions)
	fm.mu.Unlock()

	for _, session := range sessions {
		session.Wait()
	}
}
