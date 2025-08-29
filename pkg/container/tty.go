package container

import (
	"fmt"
	"net"
	"os"
	"path/filepath"
	"syscall"
	"time"
)

// Tty manages PTY acquisition from a Unix domain socket
type Tty struct {
	socketPath string
	listener   net.Listener
	ptyChan    chan *os.File
	errChan    chan error
}

// New creates a new Tty manager with a unique socket path
func New() (*Tty, error) {
	// Generate unique socket path in tmp
	socketPath := fmt.Sprintf("/tmp/container-tty-%d-%d.sock", os.Getpid(), time.Now().UnixNano())

	return NewWithPath(socketPath)
}

// NewWithPath creates a new Tty manager with a specific socket path
func NewWithPath(socketPath string) (*Tty, error) {
	// Ensure parent directory exists
	dir := filepath.Dir(socketPath)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create socket directory: %w", err)
	}

	// Remove any existing socket
	os.Remove(socketPath)

	// Create Unix domain socket
	listener, err := net.Listen("unix", socketPath)
	if err != nil {
		return nil, fmt.Errorf("failed to create socket: %w", err)
	}

	t := &Tty{
		socketPath: socketPath,
		listener:   listener,
		ptyChan:    make(chan *os.File, 1),
		errChan:    make(chan error, 1),
	}

	// Start listening in background
	go t.listen()

	return t, nil
}

// SocketPath returns the Unix domain socket path to pass to crun --console-socket
func (t *Tty) SocketPath() string {
	return t.socketPath
}

// Get blocks until a PTY is received from the socket or timeout occurs
func (t *Tty) Get() (*os.File, error) {
	return t.GetWithTimeout(5 * time.Second)
}

// GetWithTimeout blocks until a PTY is received from the socket or timeout occurs
func (t *Tty) GetWithTimeout(timeout time.Duration) (*os.File, error) {
	timer := time.NewTimer(timeout)
	defer timer.Stop()

	select {
	case pty := <-t.ptyChan:
		return pty, nil
	case err := <-t.errChan:
		return nil, fmt.Errorf("failed to receive PTY: %w", err)
	case <-timer.C:
		return nil, fmt.Errorf("timeout waiting for PTY after %v on socket %s", timeout, t.socketPath)
	}
}

// Close cleans up the Tty resources
func (t *Tty) Close() error {
	if t.listener != nil {
		t.listener.Close()
	}
	os.Remove(t.socketPath)
	return nil
}

// listen accepts connections and receives file descriptors
func (t *Tty) listen() {
	defer t.listener.Close()

	// Set an accept deadline so we don't block forever
	if ul, ok := t.listener.(*net.UnixListener); ok {
		ul.SetDeadline(time.Now().Add(10 * time.Second))
	}

	// Accept a single connection
	conn, err := t.listener.Accept()
	if err != nil {
		select {
		case t.errChan <- err:
		default:
		}
		return
	}
	defer conn.Close()

	// Get the underlying Unix connection
	unixConn, ok := conn.(*net.UnixConn)
	if !ok {
		t.errChan <- fmt.Errorf("not a Unix connection")
		return
	}

	// Receive the file descriptor
	fd, err := recvFd(unixConn)
	if err != nil {
		t.errChan <- err
		return
	}

	// Convert FD to File
	ptyFile := os.NewFile(uintptr(fd), "pty")

	// Send the PTY to the channel - block until it can be sent
	t.ptyChan <- ptyFile
}

// recvFd receives a file descriptor over a Unix domain socket
func recvFd(conn *net.UnixConn) (int, error) {
	// We need to receive at least 1 byte of data along with the FD
	buf := make([]byte, 1)
	oob := make([]byte, 32)

	// Get the underlying file descriptor
	file, err := conn.File()
	if err != nil {
		return -1, err
	}
	defer file.Close()

	// Receive the message with ancillary data
	n, oobn, _, _, err := syscall.Recvmsg(
		int(file.Fd()),
		buf,
		oob,
		0,
	)
	if err != nil {
		return -1, err
	}

	if n == 0 || oobn == 0 {
		return -1, fmt.Errorf("no data or control message received")
	}

	// Parse the control messages
	msgs, err := syscall.ParseSocketControlMessage(oob[:oobn])
	if err != nil {
		return -1, err
	}

	// Look for the file descriptor
	for _, msg := range msgs {
		if msg.Header.Level == syscall.SOL_SOCKET && msg.Header.Type == syscall.SCM_RIGHTS {
			fds, err := syscall.ParseUnixRights(&msg)
			if err != nil {
				return -1, err
			}
			if len(fds) > 0 {
				return fds[0], nil
			}
		}
	}

	return -1, fmt.Errorf("no file descriptor received")
}
