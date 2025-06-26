package wsexec

import (
	"net"
	"os"
	"syscall"
	"testing"
	"time"

	"github.com/creack/pty"
	"github.com/superfly/sprite-env/packages/container"
)

func TestConsoleSocket(t *testing.T) {
	// Create a temporary socket path
	socketPath := "/tmp/test-console-socket.sock"
	defer os.Remove(socketPath)

	// Create TTY manager
	tty, err := container.NewWithPath(socketPath)
	if err != nil {
		t.Fatalf("Failed to create TTY manager: %v", err)
	}
	defer tty.Close()

	// Create a PTY pair for testing
	master, slave, err := pty.Open()
	if err != nil {
		t.Fatalf("Failed to create PTY: %v", err)
	}
	defer master.Close()
	defer slave.Close()

	// Get the file descriptor of the master
	masterFd := int(master.Fd())

	// Connect to the socket and send the FD
	go func() {
		// Give the listener time to start
		time.Sleep(100 * time.Millisecond)

		// Connect to the socket
		conn, err := net.Dial("unix", socketPath)
		if err != nil {
			t.Errorf("Failed to connect to socket: %v", err)
			return
		}
		defer conn.Close()

		// Get Unix connection
		unixConn, ok := conn.(*net.UnixConn)
		if !ok {
			t.Errorf("Not a Unix connection")
			return
		}

		// Send the file descriptor
		if err := sendFd(unixConn, masterFd); err != nil {
			t.Errorf("Failed to send FD: %v", err)
		}
	}()

	// Wait for PTY
	receivedPty, err := tty.GetWithTimeout(2 * time.Second)
	if err != nil {
		t.Fatalf("Failed to receive PTY: %v", err)
	}
	defer receivedPty.Close()

	// Verify we can write to the PTY
	testData := []byte("Hello from console socket test\n")
	if _, err := receivedPty.Write(testData); err != nil {
		t.Errorf("Failed to write to received PTY: %v", err)
	}

	// Read from the slave side to verify
	buf := make([]byte, len(testData))
	if _, err := slave.Read(buf); err != nil {
		t.Errorf("Failed to read from slave: %v", err)
	}

	if string(buf) != string(testData) {
		t.Errorf("Data mismatch: expected %q, got %q", testData, buf)
	}
}

// sendFd sends a file descriptor over a Unix domain socket
func sendFd(conn *net.UnixConn, fd int) error {
	// We need to send at least 1 byte of data along with the FD
	data := []byte{0}

	// Get the underlying file descriptor
	file, err := conn.File()
	if err != nil {
		return err
	}
	defer file.Close()

	// Create the control message with the FD
	rights := syscall.UnixRights(fd)

	// Send the message with the FD
	return syscall.Sendmsg(
		int(file.Fd()),
		data,
		rights,
		nil,
		0,
	)
}
