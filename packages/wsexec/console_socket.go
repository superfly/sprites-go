package wsexec

import (
	"fmt"
	"net"
	"os"
	"path/filepath"
	"syscall"
	"time"
)

// ConsoleSocket handles receiving PTY file descriptors from crun via Unix domain socket
type ConsoleSocket struct {
	path     string
	listener net.Listener
	fdChan   chan int
}

// NewConsoleSocket creates a new console socket at the specified path
func NewConsoleSocket(path string) (*ConsoleSocket, error) {
	// Ensure parent directory exists
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create console socket directory: %w", err)
	}

	// Remove any existing socket
	os.Remove(path)

	// Create Unix domain socket
	listener, err := net.Listen("unix", path)
	if err != nil {
		return nil, fmt.Errorf("failed to create console socket: %w", err)
	}

	return &ConsoleSocket{
		path:     path,
		listener: listener,
		fdChan:   make(chan int, 1),
	}, nil
}

// Path returns the socket path to pass to crun --console-socket
func (cs *ConsoleSocket) Path() string {
	return cs.path
}

// Start begins listening for connections and receiving file descriptors
func (cs *ConsoleSocket) Start() {
	go cs.listen()
}

// listen accepts connections and receives file descriptors
func (cs *ConsoleSocket) listen() {
	defer cs.listener.Close()

	// Accept a single connection
	conn, err := cs.listener.Accept()
	if err != nil {
		return
	}
	defer conn.Close()

	// Get the underlying Unix connection
	unixConn, ok := conn.(*net.UnixConn)
	if !ok {
		return
	}

	// Receive the file descriptor
	fd, err := recvFd(unixConn)
	if err != nil {
		return
	}

	// Send the FD to the channel
	select {
	case cs.fdChan <- fd:
	default:
	}
}

// WaitForPTY waits for crun to send the PTY file descriptor
func (cs *ConsoleSocket) WaitForPTY() (*os.File, error) {
	// Wait up to 5 seconds for crun to send the PTY FD
	select {
	case fd := <-cs.fdChan:
		// Convert FD to File
		return os.NewFile(uintptr(fd), "pty"), nil
	case <-time.After(5 * time.Second):
		return nil, fmt.Errorf("timeout waiting for PTY from console socket")
	}
}

// Close cleans up the console socket
func (cs *ConsoleSocket) Close() error {
	if cs.listener != nil {
		cs.listener.Close()
	}
	os.Remove(cs.path)
	return nil
}

// recvFd receives a file descriptor over a Unix domain socket
func recvFd(conn *net.UnixConn) (int, error) {
	// We need to receive at least 1 byte of data along with the FD
	buf := make([]byte, 1)
	oob := make([]byte, 32) // Space for control messages

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
			// Parse the file descriptor
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
