package container

import (
	"net"
	"os"
	"syscall"
	"testing"
	"time"
)

func TestTTY(t *testing.T) {
	// Create a new Tty manager
	tty, err := TTY()
	if err != nil {
		t.Fatalf("Failed to create Tty: %v", err)
	}
	defer tty.Close()

	// Verify socket path exists
	if tty.SocketPath() == "" {
		t.Fatal("Socket path is empty")
	}

	// Verify socket file was created
	if _, err := os.Stat(tty.SocketPath()); err != nil {
		t.Fatalf("Socket file not created: %v", err)
	}
}

func TestTTYPtyAcquisition(t *testing.T) {
	// Create a new Tty manager
	tty, err := New()
	if err != nil {
		t.Fatalf("Failed to create Tty: %v", err)
	}
	defer tty.Close()

	// Create a PTY pair for testing
	master, slave, err := os.Pipe()
	if err != nil {
		t.Fatalf("Failed to create pipe: %v", err)
	}
	defer master.Close()
	defer slave.Close()

	// Start a goroutine to send the FD
	errChan := make(chan error, 1)
	go func() {
		// Connect to the socket
		conn, err := net.Dial("unix", tty.SocketPath())
		if err != nil {
			errChan <- err
			return
		}
		defer conn.Close()

		// Get Unix connection
		unixConn, ok := conn.(*net.UnixConn)
		if !ok {
			errChan <- err
			return
		}

		// Send the file descriptor
		err = sendFd(unixConn, int(master.Fd()))
		errChan <- err
	}()

	// Try to get the PTY
	pty, err := tty.GetWithTimeout(2 * time.Second)
	if err != nil {
		t.Fatalf("Failed to get PTY: %v", err)
	}
	defer pty.Close()

	// Check if send succeeded
	if err := <-errChan; err != nil {
		t.Fatalf("Failed to send FD: %v", err)
	}

	// Verify we got a valid file
	if pty == nil {
		t.Fatal("Got nil PTY")
	}
}

func TestTTYTimeout(t *testing.T) {
	// Create a new Tty manager
	tty, err := New()
	if err != nil {
		t.Fatalf("Failed to create Tty: %v", err)
	}
	defer tty.Close()

	// Try to get PTY without anyone connecting - should timeout
	start := time.Now()
	_, err = tty.GetWithTimeout(100 * time.Millisecond)
	duration := time.Since(start)

	if err == nil {
		t.Fatal("Expected timeout error")
	}

	if duration < 100*time.Millisecond {
		t.Fatalf("Timeout occurred too quickly: %v", duration)
	}

	if duration > 200*time.Millisecond {
		t.Fatalf("Timeout took too long: %v", duration)
	}
}

func TestAcquirePty(t *testing.T) {
	socketPath, getPty, cleanup, err := AcquirePty()
	if err != nil {
		t.Fatalf("Failed to acquire PTY: %v", err)
	}
	defer cleanup()

	// Verify socket path exists
	if socketPath == "" {
		t.Fatal("Socket path is empty")
	}

	// Verify socket file was created
	if _, err := os.Stat(socketPath); err != nil {
		t.Fatalf("Socket file not created: %v", err)
	}

	// Verify getPty is not nil
	if getPty == nil {
		t.Fatal("getPty function is nil")
	}
}

// sendFd sends a file descriptor over a Unix domain socket
func sendFd(conn *net.UnixConn, fd int) error {
	// Get the underlying file
	file, err := conn.File()
	if err != nil {
		return err
	}
	defer file.Close()

	// Prepare the message
	buf := []byte{0} // At least 1 byte of data
	rights := syscall.UnixRights(fd)

	// Send the message with the file descriptor
	return syscall.Sendmsg(
		int(file.Fd()),
		buf,
		rights,
		nil,
		0,
	)
}