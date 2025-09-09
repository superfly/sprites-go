package phx

import (
	"net/http"
	"net/url"
	"strings"
	"time"
)

// quick toggle while debugging
const startHeartbeat = true

// A Socket represents a connection to the server via the given Transport. Many Channels can be connected over a single
// Socket.
type Socket struct {
	// Endpoint is the URL to connect to. Include parameters here.
	EndPoint *url.URL

	// RequestHeader is an http.Header map to send in the initial connection.
	RequestHeader http.Header

	// Transport is the main transport mechanism to use to connect to the server. Only Websocket is implemented currently.
	Transport Transport

	// Specify a logger for Errors, Warnings, Info and Debug messages. Defaults to phx.NoopLogger.
	Logger Logger

	// Timeout for initial handshake with server.
	ConnectTimeout time.Duration

	// ReconnectAfterFunc is a function that returns the time to delay reconnections based on the given tries
	ReconnectAfterFunc func(tries int) time.Duration

	// HeartbeatInterval is the duration between heartbeats sent to the server to keep the connection alive.
	HeartbeatInterval time.Duration

	// Serializer encodes/decodes messages to/from the server. Must work with a Serializer on the server.
	// Defaults to JSONSerializerV2
	Serializer Serializer

	// miscellaneous private members
	refGenerator     *atomicRef
	openCallbacks    map[Ref]func()
	closeCallbacks   map[Ref]func()
	errorCallbacks   map[Ref]func(error)
	messageCallbacks map[Ref]func(Message)
	channels         map[string]*Channel

	// heartbeat related state
	hbMsg   chan *Message
	hbClose chan any
	hbRef   Ref
}

// NewSocket creates a Socket that connects to the given endPoint using the default websocket Transport.
// After creating the socket, several options can be set, such as Transport, Logger, Serializer and timeouts.
//
// If a custom websocket.Dialer is needed, such as to set up a Proxy, then create a custom WebSocket and assign
// it as the Socket's Transport:
//
// ```go
// socket := phx.NewSocket(endPoint)
// ws := phx.NewWebsocket(socket)
// proxyURL, _ := url.Parse("http://localhost:8888")
// ws.Dialer.Proxy = http.ProxyURL(proxyURL)
// socket.Transport = ws
// ```
func NewSocket(endPoint *url.URL) *Socket {
	socket := &Socket{
		EndPoint:           endPoint,
		Logger:             NewNoopLogger(),
		ConnectTimeout:     defaultConnectTimeout,
		ReconnectAfterFunc: defaultReconnectAfterFunc,
		HeartbeatInterval:  defaultHeartbeatInterval,
		Serializer:         NewJSONSerializerV2(),
		refGenerator:       newAtomicRef(),
		openCallbacks:      make(map[Ref]func()),
		closeCallbacks:     make(map[Ref]func()),
		errorCallbacks:     make(map[Ref]func(error)),
		messageCallbacks:   make(map[Ref]func(Message)),
		channels:           make(map[string]*Channel),
	}
	socket.Transport = NewWebsocket(socket)
	return socket
}

// Connect will start connection attempts with the server until successful or canceled with Disconnect.
func (s *Socket) Connect() error {
	// Add the 'vsn' query parameter to the connection url
	q := s.EndPoint.Query()
	q.Set("vsn", s.Serializer.vsn())
	s.EndPoint.RawQuery = q.Encode()

	s.Logger.Printf(LogInfo, "socket", "connecting to %v\n", s.EndPoint)

	err := s.Transport.Connect(s.EndPoint, s.RequestHeader, s.ConnectTimeout)
	if err != nil {
		s.Logger.Println(LogError, "socket", err)
		return err
	}

	return nil
}

// Disconnect or stop trying to Connect to server.
func (s *Socket) Disconnect() error {
	err := s.Transport.Disconnect()
	if err != nil {
		s.Logger.Println(LogError, "socket", err)
		return err
	}

	return nil
}

// Reconnect with the server.
func (s *Socket) Reconnect() error {
	err := s.Transport.Reconnect()
	if err != nil {
		s.Logger.Println(LogError, "socket", err)
		return err
	}

	return nil
}

func (s *Socket) IsConnected() bool {
	return s.Transport != nil && s.Transport.IsConnected()
}

func (s *Socket) IsConnectedOrConnecting() bool {
	return s.Transport != nil &&
		(s.Transport.ConnectionState() == ConnectionConnecting || s.Transport.ConnectionState() == ConnectionOpen)
}

func (s *Socket) ConnectionState() ConnectionState {
	if s.Transport != nil {
		return s.Transport.ConnectionState()
	} else {
		return ConnectionClosed

	}
}

func (s *Socket) Push(topic string, event string, payload any, joinRef Ref) (Ref, error) {
	ref := s.MakeRef()

	err := s.PushMessage(Message{
		Topic:   topic,
		Event:   event,
		Payload: payload,
		Ref:     ref,
		JoinRef: joinRef,
	})

	return ref, err
}

func (s *Socket) PushMessage(msg Message) error {
	data, err := s.Serializer.encode(&msg)
	if err != nil {
		return err
	}

	err = s.Transport.Send(data)
	if err != nil {
		return err
	}

	s.Logger.Printf(LogDebug, "socket", "Sent message %+v", msg)
	return nil
}

// MakeRef returns a unique Ref for this Socket.
func (s *Socket) MakeRef() Ref {
	return s.refGenerator.nextRef()
}

// OnOpen registers the given callback to be called whenever the Socket is opened successfully.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (s *Socket) OnOpen(callback func()) Ref {
	ref := s.MakeRef()
	s.openCallbacks[ref] = callback
	return ref
}

// OnClose registers the given callback to be called whenever the Socket is closed.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (s *Socket) OnClose(callback func()) Ref {
	ref := s.MakeRef()
	s.closeCallbacks[ref] = callback
	return ref
}

// OnError registers the given callback to be called whenever the Socket has an error.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (s *Socket) OnError(callback func(error)) Ref {
	ref := s.MakeRef()
	s.errorCallbacks[ref] = callback
	return ref
}

// OnMessage registers the given callback to be called whenever the server sends a message.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (s *Socket) OnMessage(callback func(Message)) Ref {
	ref := s.MakeRef()
	s.messageCallbacks[ref] = callback
	return ref
}

// Off cancels the given callback from being called.
func (s *Socket) Off(ref Ref) {
	_, ok := s.openCallbacks[ref]
	if ok {
		delete(s.openCallbacks, ref)
		return
	}

	_, ok = s.closeCallbacks[ref]
	if ok {
		delete(s.closeCallbacks, ref)
		return
	}

	_, ok = s.errorCallbacks[ref]
	if ok {
		delete(s.errorCallbacks, ref)
		return
	}

	_, ok = s.messageCallbacks[ref]
	if ok {
		delete(s.messageCallbacks, ref)
		return
	}
}

// Channel creates a new instance of phx.Channel, or returns an existing instance if it had already been created.
func (s *Socket) Channel(topic string, params map[string]string) *Channel {
	channel, exists := s.channels[topic]
	if exists {
		return channel
	} else {
		channel := NewChannel(topic, params, s)
		return channel
	}
}

func (s *Socket) hasChannel(topic string) bool {
	_, exists := s.channels[topic]
	return exists
}

func (s *Socket) getChannel(topic string) (*Channel, bool) {
	channel, exists := s.channels[topic]
	return channel, exists
}

func (s *Socket) addChannel(channel *Channel) {
	s.channels[channel.topic] = channel
	s.Logger.Printf(LogDebug, "socket", "Added channel '%v'. Open channels: %v", channel.topic, len(s.channels))
}

func (s *Socket) removeChannel(channel *Channel) {
	delete(s.channels, channel.topic)
	s.Logger.Printf(LogDebug, "socket", "Removed channel '%v'. Open channels: %v", channel.topic, len(s.channels))
}

// implements TransportHandler

func (s *Socket) reconnectAfter(tries int) time.Duration {
	return s.ReconnectAfterFunc(tries)
}

func (s *Socket) onConnOpen() {
	s.Logger.Printf(LogInfo, "socket", "Connected to %v", s.EndPoint)
	s.startHeartbeat()
	for _, cb := range s.openCallbacks {
		go cb()
	}
}

func (s *Socket) onConnClose() {
	s.Logger.Printf(LogInfo, "socket", "Disconnected from %v", s.EndPoint)
	s.stopHeartbeat()
	for _, cb := range s.closeCallbacks {
		go cb()
	}
}

func (s *Socket) callErrorCallbacks(err error) {
	for _, cb := range s.errorCallbacks {
		go cb(err)
	}
}

func (s *Socket) onConnError(err error) {
	s.Logger.Printf(LogError, "socket", "Connection error: %s", err)
	s.callErrorCallbacks(err)
}

func (s *Socket) onWriteError(err error) {
	s.Logger.Printf(LogError, "socket", "Write error: %s", err)
	s.callErrorCallbacks(err)
}

func (s *Socket) onReadError(err error) {
	// Don't log errors when the connection was closed
	if !strings.Contains(err.Error(), "use of closed network connection") {
		s.Logger.Printf(LogError, "socket", "Read error: %s", err)
		s.callErrorCallbacks(err)
	}
}

func (s *Socket) onConnMessage(data []byte) {
	msg, err := s.Serializer.decode(data)
	if err != nil {
		s.Logger.Println(LogError, "socket", "could not decode data to Message:", err)
		return
	}

	s.Logger.Printf(LogDebug, "socket", "Received message: %+v", msg)

	if msg.Topic == "phoenix" && msg.Ref == s.hbRef {
		// Send this message to the heartbeat goroutine
		s.hbMsg <- msg
		return
	}

	for _, cb := range s.messageCallbacks {
		go cb(*msg)
	}

	for _, channel := range s.channels {
		channel.process(msg)
	}
}

/*
 * Heartbeat related functionality
 */
func (s *Socket) startHeartbeat() {
	s.hbClose = make(chan any)
	s.hbMsg = make(chan *Message)
	if startHeartbeat {
		go s.heartbeat()
	}
}

func (s *Socket) stopHeartbeat() {
	close(s.hbClose)
	close(s.hbMsg)
}

func (s *Socket) heartbeat() {
	s.Logger.Println(LogDebug, "heartbeat", "heartbeat goroutine started")

	defer func() {
		s.Logger.Println(LogDebug, "heartbeat", "heartbeat goroutine stopped")
	}()

	s.hbRef = 0

	for {
		timer := time.NewTimer(s.HeartbeatInterval)

		select {
		case <-s.hbClose:
			timer.Stop()
			return
		case msg := <-s.hbMsg:
			s.Logger.Println(LogDebug, "heartbeat", "Got heartbeat message", msg)
			timer.Stop()
			s.hbRef = 0
		case <-timer.C:
			if !s.Transport.IsConnected() {
				continue
			}
			if s.hbRef == 0 {
				s.hbRef = s.MakeRef()
				s.Logger.Println(LogDebug, "heartbeat", "Sending heartbeat", s.hbRef)
				err := s.PushMessage(Message{Topic: "phoenix", Event: string(HeartBeatEvent), Payload: nil, Ref: s.hbRef})
				if err != nil {
					s.Logger.Println(LogError, "heartbeat", "Error when sending heartbeat", err)
				}
			} else {
				s.Logger.Println(LogDebug, "heartbeat", "heartbeat timeout")
				_ = s.Transport.Reconnect()
			}
		}
	}
}
