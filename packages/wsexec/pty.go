package wsexec

import (
	"context"
	"fmt"
	"io"
)

// Pty provides PTY-like functionality over WebSocket
var Pty = &ptyImpl{}

// PTY represents a pseudo-terminal master over WebSocket
type PTY interface {
	io.ReadWriteCloser

	// SetSize sets the terminal size
	SetSize(rows, cols uint16) error
}

type ptyImpl struct{}

// Start starts the command with a pseudo-terminal over WebSocket
func (p *ptyImpl) Start(cmd *Cmd) (PTY, error) {
	// Set TTY mode
	cmd.Tty = true

	// Create PTY wrapper first, before starting the command
	wsPty := &wsPTY{
		cmd:       cmd,
		reader:    make(chan []byte, 100),
		closed:    make(chan struct{}),
		errorChan: make(chan error, 1),
	}

	// Set up PTY on command BEFORE starting
	cmd.ptyMaster = wsPty

	// Now start the WebSocket connection
	if err := cmd.Start(); err != nil {
		return nil, err
	}

	// Start PTY I/O handler
	go wsPty.run()

	return wsPty, nil
}

// wsPTY implements PTY interface over WebSocket
type wsPTY struct {
	cmd       *Cmd
	reader    chan []byte
	closed    chan struct{}
	errorChan chan error
	ctx       context.Context
	cancel    context.CancelFunc
}

// run handles the PTY I/O loop
func (p *wsPTY) run() {
	defer close(p.closed)
	defer close(p.reader)
	// Don't cancel context on normal exit - only on errors
	// The context will be managed by the parent

	adapter := p.cmd.getAdapter()
	if adapter == nil {
		select {
		case p.errorChan <- fmt.Errorf("no websocket connection"):
		default:
		}
		// This is an error case, so cancel if we can
		if p.cancel != nil {
			p.cancel()
		}
		return
	}

	// Read from WebSocket and buffer for Read() calls
	for {
		msg, err := adapter.ReadMessage()
		if err != nil {
			select {
			case p.errorChan <- err:
			default:
			}
			// Error reading - cancel context
			if p.cancel != nil {
				p.cancel()
			}
			return
		}

		switch msg.Type {
		case MessageTypeStdout:
			// In TTY mode, all output comes through stdout
			select {
			case p.reader <- msg.Data:
			case <-p.closed:
				return
			}
		case MessageTypeStdinEOF:
			// In PTY mode, stdin EOF doesn't close the PTY
			// The PTY remains open for output until the process exits
			continue
		case MessageTypeExit:
			code, _ := DecodeExit(msg.Data)
			// Send exit code via command's channel
			select {
			case p.cmd.exitChan <- code:
			default:
			}

			// Command completed normally - initiate graceful shutdown
			go p.cmd.Close()

			// Normal completion - just return, don't cancel
			return
		case MessageTypeError:
			err := DecodeError(msg.Data)
			select {
			case p.errorChan <- err:
			default:
			}
			// Error case - cancel context
			if p.cancel != nil {
				p.cancel()
			}
			return
		}
	}
}

// Read reads data from the PTY
func (p *wsPTY) Read(b []byte) (n int, err error) {
	select {
	case data, ok := <-p.reader:
		if !ok {
			// Check for error
			select {
			case err := <-p.errorChan:
				return 0, err
			default:
				return 0, io.EOF
			}
		}
		n = copy(b, data)
		// If we couldn't copy all data, put remainder back
		if n < len(data) {
			// Try to put back, but don't block
			select {
			case p.reader <- data[n:]:
			default:
				// Buffer full, data lost
			}
		}
		return n, nil
	case <-p.closed:
		// Check for error
		select {
		case err := <-p.errorChan:
			return 0, err
		default:
			return 0, io.EOF
		}
	}
}

// Write writes data to the PTY
func (p *wsPTY) Write(b []byte) (n int, err error) {
	adapter := p.cmd.getAdapter()
	if adapter == nil {
		return 0, fmt.Errorf("no websocket connection")
	}

	// In PTY mode, all input goes through stdin
	if err := adapter.WriteStdin(b); err != nil {
		return 0, err
	}
	return len(b), nil
}

// Close closes the PTY
func (p *wsPTY) Close() error {
	select {
	case <-p.closed:
		// Already closed
		return nil
	default:
		// Trigger close
		adapter := p.cmd.getAdapter()
		if adapter != nil {
			adapter.Close()
		}
	}
	return nil
}

// SetSize sets the terminal size
func (p *wsPTY) SetSize(rows, cols uint16) error {
	adapter := p.cmd.getAdapter()
	if adapter == nil {
		return fmt.Errorf("no websocket connection")
	}
	return adapter.WriteResize(rows, cols)
}
