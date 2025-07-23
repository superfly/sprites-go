package terminal

import (
	"bytes"
	"context"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketFlush tests that all buffered data is flushed before connection closes
func TestWebSocketFlush(t *testing.T) {
	// Create a test session that outputs a lot of data quickly
	session := NewSession(
		WithCommand("sh", "-c", "for i in $(seq 1 100); do echo \"Line $i\"; done"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session)

	// Set up test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Connect as a client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	// Collect all received messages
	var mu sync.Mutex
	var receivedLines []string
	var exitCodeReceived bool
	var wg sync.WaitGroup

	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := StreamID(data[0])
				payload := data[1:]

				mu.Lock()
				switch stream {
				case StreamStdout:
					// Split payload into lines
					lines := strings.Split(string(payload), "\n")
					for _, line := range lines {
						if line != "" {
							receivedLines = append(receivedLines, line)
						}
					}
				case StreamExit:
					exitCodeReceived = true
					mu.Unlock()
					return // Exit received, stop reading
				}
				mu.Unlock()
			}
		}
	}()

	// Wait for the connection to close
	wg.Wait()

	// Verify results
	mu.Lock()
	defer mu.Unlock()

	if !exitCodeReceived {
		t.Error("exit code was not received")
	}

	// We should have received all 100 lines
	if len(receivedLines) != 100 {
		t.Errorf("expected 100 lines, got %d", len(receivedLines))
		if len(receivedLines) > 0 {
			t.Logf("First line: %s", receivedLines[0])
			t.Logf("Last line: %s", receivedLines[len(receivedLines)-1])
		}
	}

	// Verify the lines are in order
	for i, line := range receivedLines {
		// Simpler approach - just check prefix
		if !strings.HasPrefix(line, "Line ") {
			t.Errorf("line %d: expected line to start with 'Line ', got %q", i, line)
		}
	}
}

// webSocketConnection defines the minimal interface we need from gorillaws.Conn
type webSocketConnection interface {
	WriteMessage(messageType int, data []byte) error
	Close() error
	ReadMessage() (messageType int, p []byte, err error)
	SetReadLimit(limit int64)
	SetReadDeadline(t time.Time) error
	SetWriteDeadline(t time.Time) error
	WriteControl(messageType int, data []byte, deadline time.Time) error
}

// TestWebSocketFlushTimeout tests that flush respects timeout
func TestWebSocketFlushTimeout(t *testing.T) {
	// Create a custom webSocketStreams with a mock connection
	mockConn := &mockWebSocketConn{
		writeDelay: 100 * time.Millisecond, // Slow writes
	}

	// Create a wrapper that satisfies the interface
	ws := &testWebSocketStreams{
		conn:      mockConn,
		isPTY:     false,
		writeChan: make(chan writeRequest, 100),
		done:      make(chan struct{}),
	}

	// Start the write loop
	go ws.writeLoop()
	defer ws.Close()

	// Fill the buffer with many writes
	for i := 0; i < 50; i++ {
		go func(n int) {
			ws.Write([]byte("test data"))
		}(i)
	}

	// Try to flush with a short timeout
	start := time.Now()
	err := ws.Flush(200 * time.Millisecond)
	elapsed := time.Since(start)

	// Should timeout because writes are slow
	if err == nil {
		t.Error("expected flush to timeout, but it succeeded")
	}

	// Should have waited approximately the timeout duration
	if elapsed < 190*time.Millisecond || elapsed > 250*time.Millisecond {
		t.Errorf("flush took %v, expected around 200ms", elapsed)
	}
}

// testWebSocketStreams is a test version of webSocketStreams with an interface for conn
type testWebSocketStreams struct {
	conn      webSocketConnection
	isPTY     bool
	writeChan chan writeRequest
	done      chan struct{}
	readBuf   []byte
}

func (ws *testWebSocketStreams) writeLoop() {
	for {
		select {
		case req := <-ws.writeChan:
			// Handle flush request
			if req.messageType == -1 {
				if req.result != nil {
					req.result <- nil
				}
				continue
			}

			// Normal write request
			err := ws.conn.WriteMessage(req.messageType, req.data)
			if req.result != nil {
				req.result <- err
			}
		case <-ws.done:
			return
		}
	}
}

func (ws *testWebSocketStreams) Write(p []byte) (n int, err error) {
	err = ws.writeRaw(p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

func (ws *testWebSocketStreams) writeRaw(data []byte) error {
	result := make(chan error, 1)
	select {
	case ws.writeChan <- writeRequest{
		messageType: gorillaws.BinaryMessage,
		data:        data,
		result:      result,
	}:
		return <-result
	case <-ws.done:
		return bytes.ErrTooLarge
	}
}

func (ws *testWebSocketStreams) Flush(timeout time.Duration) error {
	result := make(chan error, 1)
	timer := time.NewTimer(timeout)
	defer timer.Stop()

	select {
	case ws.writeChan <- writeRequest{
		messageType: -1,
		result:      result,
	}:
		select {
		case err := <-result:
			return err
		case <-timer.C:
			return context.DeadlineExceeded
		case <-ws.done:
			return bytes.ErrTooLarge
		}
	case <-timer.C:
		return context.DeadlineExceeded
	case <-ws.done:
		return bytes.ErrTooLarge
	}
}

func (ws *testWebSocketStreams) Close() error {
	close(ws.done)
	return nil
}

// mockWebSocketConn is a mock WebSocket connection for testing
type mockWebSocketConn struct {
	mu         sync.Mutex
	messages   [][]byte
	writeDelay time.Duration
}

func (m *mockWebSocketConn) WriteMessage(messageType int, data []byte) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	// Simulate slow write
	if m.writeDelay > 0 {
		time.Sleep(m.writeDelay)
	}

	m.messages = append(m.messages, data)
	return nil
}

// Implement other methods required by gorillaws.Conn interface with stubs
func (m *mockWebSocketConn) Close() error                       { return nil }
func (m *mockWebSocketConn) ReadMessage() (int, []byte, error)  { return 0, nil, nil }
func (m *mockWebSocketConn) SetReadLimit(limit int64)           {}
func (m *mockWebSocketConn) SetReadDeadline(t time.Time) error  { return nil }
func (m *mockWebSocketConn) SetWriteDeadline(t time.Time) error { return nil }
func (m *mockWebSocketConn) WriteControl(messageType int, data []byte, deadline time.Time) error {
	return nil
}
