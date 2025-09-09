package phx

import (
	"net/http"
	"net/url"
	"time"
)

// Transport is used by a Socket to actually connect to the server.
type Transport interface {
	Connect(endPoint *url.URL, requestHeader http.Header, connectTimeout time.Duration) error
	Disconnect() error
	Reconnect() error
	IsConnected() bool
	ConnectionState() ConnectionState
	Send([]byte) error
}

// TransportHandler defines the interface that handles the activity of the Transport. This is usually just a Socket,
// but a custom TransportHandler can be implemented to stand in between a Transport and Socket.
type TransportHandler interface {
	onConnOpen()
	onConnClose()
	onConnError(error)
	onWriteError(error)
	onReadError(error)
	onConnMessage([]byte)
	reconnectAfter(int) time.Duration
}
