package container_test

import (
	"fmt"
	"log"
	"net"
	"os"
	"syscall"

	"github.com/superfly/sprite-env/pkg/container"
)

func ExampleTTY() {
	// Create a new TTY manager
	tty, err := container.TTY()
	if err != nil {
		log.Fatal(err)
	}
	defer tty.Close()

	// Get the socket path to pass to crun
	socketPath := tty.SocketPath()
	fmt.Printf("Socket path: %s\n", socketPath)

	// In a real scenario, you would start crun with:
	// crun run --console-socket=<socketPath> container-id

	// The container runtime will connect and send the PTY
	// This blocks until received (with 5 second timeout)
	ptyFile, err := tty.Get()
	if err != nil {
		log.Fatal(err)
	}
	defer ptyFile.Close()

	fmt.Printf("Received PTY: %s\n", ptyFile.Name())
}

func ExampleAcquirePty() {
	// One-liner setup for common use cases
	socketPath, getPty, cleanup, err := container.AcquirePty()
	if err != nil {
		log.Fatal(err)
	}
	defer cleanup()

	// Pass socketPath to crun
	fmt.Printf("Socket path: %s\n", socketPath)

	// Later, get the PTY when ready
	ptyFile, err := getPty()
	if err != nil {
		log.Fatal(err)
	}
	defer ptyFile.Close()

	fmt.Printf("Received PTY: %s\n", ptyFile.Name())
}

// Example of manually sending a file descriptor (for testing)
func ExampleTTY_manualSend() {
	tty, err := container.TTY()
	if err != nil {
		log.Fatal(err)
	}
	defer tty.Close()

	// Simulate what crun does
	go func() {
		conn, err := net.Dial("unix", tty.SocketPath())
		if err != nil {
			return
		}
		defer conn.Close()

		// Get Unix connection
		unixConn, ok := conn.(*net.UnixConn)
		if !ok {
			return
		}

		// Create a pipe to simulate PTY
		r, w, _ := os.Pipe()
		defer r.Close()
		defer w.Close()

		// Send the file descriptor
		file, _ := unixConn.File()
		defer file.Close()

		buf := []byte{0} // At least 1 byte of data
		rights := syscall.UnixRights(int(r.Fd()))

		syscall.Sendmsg(
			int(file.Fd()),
			buf,
			rights,
			nil,
			0,
		)
	}()

	// Receive the PTY
	ptyFile, err := tty.Get()
	if err != nil {
		log.Fatal(err)
	}
	defer ptyFile.Close()

	fmt.Printf("Successfully received file descriptor\n")
}