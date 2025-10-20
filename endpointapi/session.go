// Package endpointapi (UNSTABLE) provides low-level access to the legacy /exec endpoint.
// This package is intended for advanced users and is subject to change.
package endpointapi

import (
	"context"
	"errors"
	"io"
	"sync"
	"time"

	"github.com/gorilla/websocket"
	"github.com/superfly/sprites-go/ops"
)

// wsSession implements ops.ExecSession over a single websocket connection.
type wsSession struct {
	conn     *websocket.Conn
	writeMu  sync.Mutex
	closed   bool
	exitOnce sync.Once
	exitCode int
	exitCh   chan struct{}
}

func newWSSession(conn *websocket.Conn, _ bool) *wsSession {
	return &wsSession{conn: conn, exitCh: make(chan struct{})}
}

func (s *wsSession) Write(p []byte) (int, error) {
	s.writeMu.Lock()
	defer s.writeMu.Unlock()
	if s.closed {
		return 0, io.ErrClosedPipe
	}
	if err := s.conn.WriteMessage(websocket.BinaryMessage, append([]byte{byte(ops.StreamStdin)}, p...)); err != nil {
		return 0, err
	}
	return len(p), nil
}

func (s *wsSession) Read(ctx context.Context) (ops.StreamID, []byte, error) {
	type frame struct {
		mt   int
		data []byte
		err  error
	}
	ch := make(chan frame, 1)
	go func() { mt, data, err := s.conn.ReadMessage(); ch <- frame{mt: mt, data: data, err: err}; close(ch) }()
	select {
	case <-ctx.Done():
		return 0, nil, ctx.Err()
	case fr := <-ch:
		if fr.err != nil {
			return 0, nil, fr.err
		}
		if fr.mt == websocket.TextMessage {
			return ops.StreamText, fr.data, nil
		}
		if len(fr.data) == 0 {
			return 0, nil, io.EOF
		}
		sid := ops.StreamID(fr.data[0])
		payload := fr.data[1:]
		if sid == ops.StreamExit {
			if len(payload) > 0 {
				s.exitOnce.Do(func() { s.exitCode = int(payload[0]); close(s.exitCh) })
			} else {
				s.exitOnce.Do(func() { s.exitCode = 0; close(s.exitCh) })
			}
		}
		return sid, payload, nil
	}
}

func (s *wsSession) Resize(ctx context.Context, cols, rows int) error { return nil }
func (s *wsSession) StdinEOF(ctx context.Context) error               { return s.sendStdinEOF() }
func (s *wsSession) sendStdinEOF() error {
	s.writeMu.Lock()
	defer s.writeMu.Unlock()
	if s.closed {
		return io.ErrClosedPipe
	}
	return s.conn.WriteMessage(websocket.BinaryMessage, []byte{byte(ops.StreamStdinEOF)})
}

func (s *wsSession) ExitCode(ctx context.Context) (int, error) {
	select {
	case <-ctx.Done():
		return -1, ctx.Err()
	case <-s.exitCh:
		return s.exitCode, nil
	case <-time.After(24 * time.Hour):
		return -1, errors.New("timeout waiting for exit code")
	}
}

func (s *wsSession) Close() error {
	s.writeMu.Lock()
	s.closed = true
	s.writeMu.Unlock()
	return s.conn.Close()
}
