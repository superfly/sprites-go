//go:build unix && !windows

package runner

import (
	"bufio"
	"context"
	"io"
	"net"
	"os/exec"
	"strings"
	"testing"
	"time"
)

// Non-TTY: bridge stdin/stdout over a TCP connection; ensure round-trip and clean shutdown.
func TestTCPBridge_NonTTY_RoundTrip(t *testing.T) {
	t.Parallel()

	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("listen: %v", err)
	}
	defer ln.Close()

	serverDone := make(chan error, 1)
	go func() {
		conn, err := ln.Accept()
		if err != nil {
			serverDone <- err
			return
		}
		defer conn.Close()
		// Write a line to be echoed by 'cat'
		if _, err := conn.Write([]byte("hello-tcp\n")); err != nil {
			serverDone <- err
			return
		}
		// Half-close write to signal EOF to client stdin loop
		if tcp, ok := conn.(*net.TCPConn); ok {
			_ = tcp.CloseWrite()
		}
		// Read back echo from client stdout
		conn.SetReadDeadline(time.Now().Add(5 * time.Second))
		rd := bufio.NewReader(conn)
		line, err := rd.ReadString('\n')
		if err != nil {
			serverDone <- err
			return
		}
		if strings.TrimSpace(line) != "hello-tcp" {
			serverDone <- io.ErrUnexpectedEOF
			return
		}
		serverDone <- nil
	}()

	r := &Runner{}
	conn, err := net.Dial("tcp", ln.Addr().String())
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	defer conn.Close()

	// Run 'cat' with stdin/stdout bound to the TCP connection; discard stderr
	cmd := exec.Command("cat")
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	code, err := r.RunContext(ctx, cmd,
		WithStdout(conn),
		WithStderr(io.Discard),
		WithStdin(conn),
	)
	if err != nil || code != 0 {
		t.Fatalf("run err=%v code=%d", err, code)
	}
	if serr := <-serverDone; serr != nil {
		t.Fatalf("server err: %v", serr)
	}
}

// TTY: bridge PTY I/O over TCP connection; server sends line, expects transformed reply.
func TestTCPBridge_TTY_RoundTrip(t *testing.T) {
	t.Parallel()

	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("listen: %v", err)
	}
	defer ln.Close()

	serverDone := make(chan error, 1)
	go func() {
		conn, err := ln.Accept()
		if err != nil {
			serverDone <- err
			return
		}
		defer conn.Close()
		// Send input line to TTY stdin
		if _, err := conn.Write([]byte("abc\n")); err != nil {
			serverDone <- err
			return
		}
		if tcp, ok := conn.(*net.TCPConn); ok {
			_ = tcp.CloseWrite()
		}
		// Read merged output (normalize CRLF later in assertion)
		conn.SetReadDeadline(time.Now().Add(5 * time.Second))
		rd := bufio.NewReader(conn)
		gotOK := false
		for i := 0; i < 2; i++ { // PTY may echo input; second line is the processed output
			line, err := rd.ReadString('\n')
			if err != nil {
				serverDone <- err
				return
			}
			norm := strings.TrimSpace(strings.ReplaceAll(line, "\r\n", "\n"))
			if norm == "Xabc" {
				gotOK = true
				break
			}
		}
		if !gotOK {
			serverDone <- io.ErrUnexpectedEOF
			return
		}
		serverDone <- nil
	}()

	r := &Runner{}
	conn, err := net.Dial("tcp", ln.Addr().String())
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	defer conn.Close()

	// Child reads a line and echoes with prefix under a TTY
	cmd := exec.Command("sh", "-c", "read x; echo X$x")
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	code, err := r.RunContext(ctx, cmd,
		WithStdout(conn),
		WithNewTTY(),
		WithStdin(conn),
	)
	if err != nil || code != 0 {
		t.Fatalf("run err=%v code=%d", err, code)
	}
	if serr := <-serverDone; serr != nil {
		t.Fatalf("server err: %v", serr)
	}
}
