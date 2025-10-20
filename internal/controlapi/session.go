package controlapi

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"sync"
	"time"

	"github.com/gorilla/websocket"
	"github.com/superfly/sprites-go/ops"
)

type controlSession struct {
	conn    *websocket.Conn
	opID    string
	tty     bool
	writeMu sync.Mutex
	closed  bool

	exitOnce sync.Once
	exitCh   chan struct{}
	exitCode int
}

func newControlSession(conn *websocket.Conn, opID string, tty bool) *controlSession {
	return &controlSession{conn: conn, opID: opID, tty: tty, exitCh: make(chan struct{})}
}

func (s *controlSession) Write(p []byte) (int, error) {
	s.writeMu.Lock()
	defer s.writeMu.Unlock()
	if s.closed {
		return 0, io.ErrClosedPipe
	}
	// In control mode, stdin is a binary frame prefixed with stream id 0
	if err := s.conn.WriteMessage(websocket.BinaryMessage, append([]byte{byte(ops.StreamStdin)}, p...)); err != nil {
		return 0, err
	}
	return len(p), nil
}

func (s *controlSession) Read(ctx context.Context) (ops.StreamID, []byte, error) {
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
		if fr.mt == websocket.TextMessage && isControl(fr.data) {
			// Parse control envelope and capture exit on op.complete
			var env struct {
				Type string         `json:"type"`
				Args map[string]any `json:"args"`
			}
			if len(fr.data) >= len("control:") {
				_ = json.Unmarshal(fr.data[len("control:"):], &env)
			}
			if env.Type == "op.complete" {
				if v, ok := env.Args["ok"].(bool); ok && v {
					// Success without explicit code → 0
					s.exitOnce.Do(func() { s.exitCode = 0; close(s.exitCh) })
				} else {
					// Error path: use exit 1 by default
					s.exitOnce.Do(func() { s.exitCode = 1; close(s.exitCh) })
				}
			}
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

func (s *controlSession) Resize(ctx context.Context, cols, rows int) error {
	s.writeMu.Lock()
	defer s.writeMu.Unlock()
	if s.closed {
		return io.ErrClosedPipe
	}
	m := map[string]any{"type": "control:resize", "cols": cols, "rows": rows}
	// Send as text frame "control:{json}" to match server control detection
	b, _ := json.Marshal(m)
	return s.conn.WriteMessage(websocket.TextMessage, append([]byte("control:"), b...))
}

func isControl(data []byte) bool {
	return len(data) >= len("control:") && string(data[:len("control:")]) == "control:"
}

func (s *controlSession) StdinEOF(ctx context.Context) error { return s.sendStdinEOF() }
func (s *controlSession) sendStdinEOF() error {
	s.writeMu.Lock()
	defer s.writeMu.Unlock()
	if s.closed {
		return io.ErrClosedPipe
	}
	return s.conn.WriteMessage(websocket.BinaryMessage, []byte{byte(ops.StreamStdinEOF)})
}

func (s *controlSession) ExitCode(ctx context.Context) (int, error) {
	select {
	case <-ctx.Done():
		return -1, ctx.Err()
	case <-s.exitCh:
		return s.exitCode, nil
	case <-time.After(24 * time.Hour):
		return -1, errors.New("timeout waiting for exit code")
	}
}

func (s *controlSession) Close() error {
	s.writeMu.Lock()
	s.closed = true
	s.writeMu.Unlock()
	return s.conn.Close()
}
