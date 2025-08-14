package wsexec

import (
	"context"
	"io"
	"net/http"
	"os"
	"os/exec"

	gorillaws "github.com/gorilla/websocket"
)

// HandlerOption configures a WebSocket handler
type HandlerOption func(*handlerConfig)

type handlerConfig struct {
	cmd      *exec.Cmd
	ptmx     *os.File
	hasStdin bool
}

// WithPTY configures the handler to use a PTY master file
func WithPTY(ptmx *os.File) HandlerOption {
	return func(c *handlerConfig) {
		c.ptmx = ptmx
	}
}

// WithStdin configures the handler to expect stdin input from the client
func WithStdin() HandlerOption {
	return func(c *handlerConfig) {
		c.hasStdin = true
	}
}

// Handler upgrades HTTP to WebSocket and serves the provided *exec.Cmd over it.
func Handler(cmd *exec.Cmd, opts ...HandlerOption) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		// Apply options
		config := &handlerConfig{cmd: cmd}
		for _, opt := range opts {
			opt(config)
		}

		up := gorillaws.Upgrader{CheckOrigin: func(r *http.Request) bool { return true }}
		conn, err := up.Upgrade(w, r, nil)
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		_ = ServeConnWithOptions(r.Context(), conn, config)
		// Let client close first
	}
}

// ServeConnWithOptions attaches the command to the WebSocket using the provided configuration.
func ServeConnWithOptions(ctx context.Context, conn *gorillaws.Conn, config *handlerConfig) error {
	// Serialize websocket writes
	writeCh := make(chan []byte)
	writerDone := make(chan struct{})
	go func() {
		defer close(writerDone)
		for msg := range writeCh {
			if err := conn.WriteMessage(gorillaws.BinaryMessage, msg); err != nil {
				return
			}
		}
	}()

	if config.ptmx != nil {
		// PTY mode: read from PTY and send as stdout
		return serveConnPTY(ctx, conn, config.cmd, config.ptmx, writeCh, writerDone, config.hasStdin)
	} else {
		// Normal mode: separate stdout/stderr
		return serveConnNormal(ctx, conn, config.cmd, writeCh, writerDone, config.hasStdin)
	}
}

// serveConnNormal handles non-PTY command execution
func serveConnNormal(ctx context.Context, conn *gorillaws.Conn, cmd *exec.Cmd, writeCh chan []byte, writerDone chan struct{}, hasStdin bool) error {
	// Outbound writers that prefix stream ID
	stdoutW := &wsPrefixedWriter{streamID: StreamStdout, ch: writeCh}
	stderrW := &wsPrefixedWriter{streamID: StreamStderr, ch: writeCh}
	cmd.Stdout = stdoutW
	cmd.Stderr = stderrW

	// Handle stdin if requested
	var stdinDone chan struct{}
	if hasStdin {
		// Inbound stdin reader via io.Pipe (synchronous, no buffered channels)
		pr, pw := io.Pipe()
		cmd.Stdin = pr
		stdinDone = make(chan struct{})
		go func() {
			defer close(stdinDone)
			defer pw.Close()
			for {
				mt, data, err := conn.ReadMessage()
				if err != nil {
					// WebSocket closed, signal EOF to command
					return
				}
				if mt != gorillaws.BinaryMessage || len(data) == 0 {
					continue
				}
				// Check for StreamStdinEOF
				if len(data) > 0 && StreamID(data[0]) == StreamStdinEOF {
					// Client signaled EOF, close the pipe
					return
				}
				// Write stdin data (skip stream ID if present)
				stdinData := data
				if len(data) > 0 && StreamID(data[0]) == StreamStdin {
					stdinData = data[1:]
				}
				if _, err := pw.Write(stdinData); err != nil {
					return
				}
			}
		}()
	} else {
		// If not expecting stdin, still need to consume any stdin messages to prevent hanging
		stdinDone = make(chan struct{})
		go func() {
			defer close(stdinDone)
			for {
				mt, _, err := conn.ReadMessage()
				if err != nil {
					return
				}
				// Only consume binary messages (stdin data), ignore other message types
				if mt != gorillaws.BinaryMessage {
					continue
				}
			}
		}()
	}

	if err := cmd.Start(); err != nil {
		return err
	}

	// Wait for command to finish
	_ = cmd.Wait()

	// Send exit code frame first
	exitCode := -1
	if ps := cmd.ProcessState; ps != nil {
		exitCode = ps.ExitCode()
	}
	exitMsg := []byte{byte(StreamExit), byte(exitCode & 0xFF)}
	writeCh <- exitMsg

	close(writeCh)

	// Wait for all data to be written
	<-writerDone
	<-stdinDone

	// Let client close the connection
	return nil
}

// serveConnPTY handles PTY command execution
func serveConnPTY(ctx context.Context, conn *gorillaws.Conn, cmd *exec.Cmd, ptmx *os.File, writeCh chan []byte, writerDone chan struct{}, hasStdin bool) error {
	// Handle stdin if requested
	var stdinDone chan struct{}
	if hasStdin {
		// For PTY mode, we need to write stdin directly to the PTY
		// The command's stdin should already be set to the PTY slave (tty)
		stdinDone = make(chan struct{})
		go func() {
			defer close(stdinDone)
			for {
				mt, data, err := conn.ReadMessage()
				if err != nil {
					return
				}
				if mt != gorillaws.BinaryMessage || len(data) == 0 {
					continue
				}
				// Check for StreamStdinEOF
				if len(data) > 0 && StreamID(data[0]) == StreamStdinEOF {
					// Client signaled EOF, stop writing to PTY
					return
				}
				// Write stdin data to PTY (skip stream ID if present)
				stdinData := data
				if len(data) > 0 && StreamID(data[0]) == StreamStdin {
					stdinData = data[1:]
				}
				if _, err := ptmx.Write(stdinData); err != nil {
					return
				}
			}
		}()
	} else {
		// If not expecting stdin, still need to consume any stdin messages to prevent hanging
		stdinDone = make(chan struct{})
		go func() {
			defer close(stdinDone)
			for {
				mt, _, err := conn.ReadMessage()
				if err != nil {
					return
				}
				// Only consume binary messages (stdin data), ignore other message types
				if mt != gorillaws.BinaryMessage {
					continue
				}
			}
		}()
	}

	// PTY output reader - read from PTY and send as stdout
	ptmxDone := make(chan struct{})
	go func() {
		defer close(ptmxDone)
		stdoutW := &wsPrefixedWriter{streamID: StreamStdout, ch: writeCh}
		_, err := io.Copy(stdoutW, ptmx)
		if err != nil {
			// PTY closed, which is expected when command exits
		}
	}()

	if err := cmd.Start(); err != nil {
		return err
	}

	// Wait for command to finish
	_ = cmd.Wait()

	// Send exit code frame first
	exitCode := -1
	if ps := cmd.ProcessState; ps != nil {
		exitCode = ps.ExitCode()
	}
	exitMsg := []byte{byte(StreamExit), byte(exitCode & 0xFF)}
	writeCh <- exitMsg

	close(writeCh)

	// Wait for all data to be written
	<-writerDone
	<-stdinDone
	<-ptmxDone

	// Let client close the connection
	return nil
}

type wsPrefixedWriter struct {
	streamID StreamID
	ch       chan []byte
}

func (w *wsPrefixedWriter) Write(p []byte) (int, error) {
	msg := make([]byte, 1+len(p))
	msg[0] = byte(w.streamID)
	copy(msg[1:], p)
	w.ch <- msg
	return len(p), nil
}
