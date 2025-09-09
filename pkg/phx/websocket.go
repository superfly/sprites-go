package phx

import (
	"errors"
	"fmt"
	"github.com/gorilla/websocket"
	"net/http"
	"net/url"
	"path"
	"sync"
	"time"
)

// Websocket is a Transport that connects to the server via Websockets. It is based on
// [gorilla.Websocket](https://pkg.go.dev/github.com/gorilla/websocket). The Dialer defaults to websocket.DefaultDialer.
type Websocket struct {
	Dialer          *websocket.Dialer
	Handler         TransportHandler
	conn            *websocket.Conn
	endPoint        *url.URL
	requestHeader   http.Header
	connectTimeout  time.Duration
	done            chan any
	close           chan bool
	reconnect       chan bool
	closeMsg        chan bool
	send            chan []byte
	connectionTries int
	mu              sync.RWMutex
	started         bool
	closing         bool
	reconnecting    bool
	waitingForClose bool
}

func NewWebsocket(handler TransportHandler) *Websocket {
	return &Websocket{
		Dialer:  websocket.DefaultDialer,
		Handler: handler,
	}
}

// implements Transport

func (w *Websocket) Connect(endPoint *url.URL, requestHeader http.Header, connectTimeout time.Duration) error {
	if w.isStarted() {
		return errors.New("connect was already called")
	}

	// Copy the passed in endpoint so we can modify it
	newEndpoint := *endPoint

	newEndpoint.Path = path.Join(newEndpoint.Path, "websocket")

	if newEndpoint.Scheme == "" {
		if newEndpoint.Port() == "443" {
			newEndpoint.Scheme = "wss"
		} else {
			newEndpoint.Scheme = "ws"
		}
	} else if newEndpoint.Scheme == "http" {
		newEndpoint.Scheme = "ws"
	} else if newEndpoint.Scheme == "https" {
		newEndpoint.Scheme = "wss"
	}

	if newEndpoint.Scheme != "ws" && newEndpoint.Scheme != "wss" {
		return errors.New("invalid scheme for websocket transport, must be 'ws://' or 'wss://'")
	}

	w.endPoint = &newEndpoint
	w.requestHeader = requestHeader
	w.connectTimeout = connectTimeout

	w.startup()
	return nil
}

func (w *Websocket) Disconnect() error {
	if !w.isStarted() {
		return errors.New("not connected")
	}

	if w.connIsSet() {
		w.sendClose()
	} else {
		w.shutdown()
	}
	return nil
}

func (w *Websocket) Reconnect() error {
	if !w.isStarted() {
		return errors.New("not connected")
	}

	w.sendReconnect()
	return nil
}

func (w *Websocket) IsConnected() bool {
	return w.connIsReady()
}

func (w *Websocket) ConnectionState() ConnectionState {
	if w.connIsReady() {
		return ConnectionOpen
	} else if !w.isStarted() {
		return ConnectionClosed
	} else if w.isClosing() {
		return ConnectionClosing
	} else {
		return ConnectionConnecting
	}
}

func (w *Websocket) Send(msg []byte) error {
	if w.isClosing() {
		return errors.New("cannot Send when closing connection")
	}

	if !w.isStarted() {
		return errors.New("cannot Send when not connected or connecting")
	}

	w.send <- msg
	return nil
}

func (w *Websocket) startup() {
	w.connectionTries = 0

	w.done = make(chan any)
	w.close = make(chan bool)
	w.closeMsg = make(chan bool)
	w.reconnect = make(chan bool)
	w.send = make(chan []byte, messageQueueLength)

	w.setReconnecting(false)
	w.setClosing(false)

	go w.connectionManager()
	go w.connectionWriter()
	go w.connectionReader()

	w.setStarted(true)
}

func (w *Websocket) shutdown() {
	//fmt.Println("shutdown")

	// Tell the goroutines to exit
	close(w.done)
	close(w.close)
	close(w.closeMsg)
	close(w.reconnect)
	close(w.send)

	w.setStarted(false)
	w.setReconnecting(false)
	w.setClosing(false)
}

func (w *Websocket) dial() error {
	w.Dialer.HandshakeTimeout = w.connectTimeout
	conn, _, err := w.Dialer.Dial(w.endPoint.String(), w.requestHeader)
	if err != nil {
		return err
	}
	//w.socket.Logger.Debugf("Connected conn: %+v\n\n", conn)
	//w.socket.Logger.Debugf("Connected resp: %+v\n", resp)

	w.setConn(conn)
	w.setReconnecting(false)
	w.Handler.onConnOpen()

	return nil
}

func (w *Websocket) closeConn() {
	//fmt.Println("closeConn")

	if w.connIsSet() {
		// attempt to gracefully close the connection by sending a close websocket message
		data := websocket.FormatCloseMessage(websocket.CloseNormalClosure, "")
		deadline := time.Now().Add(2 * time.Second)
		w.setWaitingForClose(true)
		err := w.conn.WriteControl(websocket.CloseMessage, data, deadline)
		if err == nil {
			// Wait for a close message to be received by `connectionReader`, or time out after 2 seconds
			w.setWaitingForClose(true)
			select {
			case <-w.closeMsg:
			case <-time.After(2 * time.Second):
			}
		}
		w.setWaitingForClose(false)
	}

	if w.connIsSet() {
		err := w.conn.Close()
		if err != nil {
			w.Handler.onConnError(err)
		}

		w.setConn(nil)
	}

	w.Handler.onConnClose()
	w.setClosing(false)
}

func (w *Websocket) writeToConn(data []byte) error {
	if !w.connIsReady() {
		return errors.New("connection is not open")
	}

	return w.conn.WriteMessage(websocket.TextMessage, data)
}

func (w *Websocket) readFromConn() ([]byte, error) {
	if !w.connIsReady() {
		return nil, errors.New("connection is not open")
	}

	messageType, data, err := w.conn.ReadMessage()
	if err != nil {
		return nil, err
	}
	if messageType != websocket.TextMessage {
		return nil, errors.New(fmt.Sprint("Got unsupported websocket message type", messageType))
	}

	return data, nil
}

func (w *Websocket) connectionManager() {
	//fmt.Println("connectionManager started")
	//defer fmt.Println("connectionManager stopped")

	for {
		// Check if we have been told to finish
		select {
		case <-w.done:
			return
		default:
		}

		if !w.isClosing() && !w.connIsSet() {
			err := w.dial()
			if err != nil {
				w.Handler.onConnError(err)
				w.setReconnecting(true)
				w.connectionTries++
				delay := w.Handler.reconnectAfter(w.connectionTries)
				select {
				case <-w.done:
				case <-time.After(delay):
				}
				continue
			}
		}

		select {
		case <-w.done:
			return
		case <-w.close:
			w.closeConn()
			w.shutdown()
		case <-w.reconnect:
			w.closeConn()
		}
	}
}

func (w *Websocket) connectionWriter() {
	//fmt.Println("connectionWriter started")
	//defer fmt.Println("connectionWriter stopped")

	for {
		// Check if we have been told to finish
		select {
		case <-w.done:
			return
		default:
		}

		if !w.connIsReady() {
			time.Sleep(busyWait)
			continue
		}

		select {
		case <-w.done:
			return
		case data := <-w.send:
			// If there is a message to send, but we're not connected, then wait until we are.
			if !w.connIsReady() {
				time.Sleep(busyWait)
				continue
			}

			// Send the message
			err := w.writeToConn(data)

			// If there were any errors sending, then tell the connectionManager to reconnect
			if err != nil {
				w.Handler.onWriteError(err)
				w.sendReconnect()
				time.Sleep(busyWait)
				continue
			}
		}
	}
}

func (w *Websocket) connectionReader() {
	//fmt.Println("connectionReader started")
	//defer fmt.Println("connectionReader stopped")

	for {
		// Check if we have been told to finish
		select {
		case <-w.done:
			//fmt.Println("connectionReader stopping")
			return
		default:
		}

		// Wait until we're connected
		if !w.connIsReady() {
			time.Sleep(busyWait)
			continue
		}

		// Read the next message from the websocket. This blocks until there is a message or error
		data, err := w.readFromConn()

		// If there were any errors, tell the connectionManager to reconnect
		if err != nil {
			//fmt.Printf("read error %e %v\n", err, err)
			if websocket.IsCloseError(err, 1000) && w.isWaitingForClose() {
				// tell the connectionManager that we got the close message
				w.closeMsg <- true
			} else {
				w.Handler.onReadError(err)
				w.setConn(nil)
				w.sendReconnect()
			}

			time.Sleep(busyWait)
			continue
		}

		w.Handler.onConnMessage(data)
	}
}

func (w *Websocket) setStarted(started bool) {
	w.mu.Lock()
	defer w.mu.Unlock()

	w.started = started
}

func (w *Websocket) isStarted() bool {
	w.mu.RLock()
	defer w.mu.RUnlock()

	return w.started
}

func (w *Websocket) setClosing(closing bool) {
	w.mu.Lock()
	defer w.mu.Unlock()

	w.closing = closing
}

func (w *Websocket) isClosing() bool {
	w.mu.RLock()
	defer w.mu.RUnlock()

	return w.closing
}

func (w *Websocket) sendClose() {
	w.mu.Lock()
	defer w.mu.Unlock()

	if w.closing == true {
		return
	}

	w.closing = true
	w.close <- true
}

func (w *Websocket) setReconnecting(reconnecting bool) {
	w.mu.Lock()
	defer w.mu.Unlock()

	w.reconnecting = reconnecting
}

func (w *Websocket) isReconnecting() bool {
	w.mu.RLock()
	defer w.mu.RUnlock()

	return w.reconnecting
}

func (w *Websocket) sendReconnect() {
	w.mu.Lock()
	defer w.mu.Unlock()

	if w.reconnecting || w.closing {
		return
	}

	w.reconnecting = true
	w.reconnect <- true
}

func (w *Websocket) setConn(conn *websocket.Conn) {
	w.mu.Lock()
	defer w.mu.Unlock()

	w.conn = conn
}

func (w *Websocket) connIsSet() bool {
	w.mu.RLock()
	defer w.mu.RUnlock()

	return w.conn != nil
}

func (w *Websocket) connIsReady() bool {
	w.mu.RLock()
	defer w.mu.RUnlock()

	return w.started && !w.closing && !w.reconnecting && w.conn != nil
}

func (w *Websocket) setWaitingForClose(waitingForClose bool) {
	w.mu.Lock()
	defer w.mu.Unlock()

	w.waitingForClose = waitingForClose
}

func (w *Websocket) isWaitingForClose() bool {
	w.mu.RLock()
	defer w.mu.RUnlock()

	return w.waitingForClose
}
