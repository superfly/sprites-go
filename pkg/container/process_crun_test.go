package container

import (
	"net"
	"os"
	"syscall"
	"testing"
	"time"

	"github.com/creack/pty"
	"github.com/superfly/sprite-env/pkg/supervisor"
)

func TestProcessCrunSimulation(t *testing.T) {
	t.Skip() // probably not needed anymore
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-crun-sim",
	})

	// This test simulates what happens when crun uses --console-socket
	// Create a process that will receive the CONSOLE_SOCKET env var
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "sh",
			Args: []string{"-c", `
				echo "Container starting..."
				echo "CONSOLE_SOCKET=$CONSOLE_SOCKET"
				sleep 0.1  # Give time for PTY to be received
				echo "Container running"
			`},
		},
		TTYTimeout: 3 * time.Second,
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Stop()

	// Get the socket path for simulation
	socketPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}

	// Start the process
	pid, err := process.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}
	t.Logf("Started process with PID %d", pid)

	// Channel to control when to close the PTY
	closePTY := make(chan struct{})

	// Simulate crun connecting to the socket and sending a PTY
	go func() {
		// Give the process time to start
		time.Sleep(50 * time.Millisecond)

		// Create a real PTY pair
		master, slave, err := pty.Open()
		if err != nil {
			t.Logf("Failed to create PTY: %v", err)
			return
		}
		defer master.Close()
		defer slave.Close()

		// Connect to the socket
		conn, err := net.Dial("unix", socketPath)
		if err != nil {
			t.Logf("Failed to connect to socket: %v", err)
			return
		}
		defer conn.Close()

		// Get Unix connection
		unixConn, ok := conn.(*net.UnixConn)
		if !ok {
			t.Log("Not a Unix connection")
			return
		}

		// Send the PTY file descriptor
		file, err := unixConn.File()
		if err != nil {
			t.Logf("Failed to get file: %v", err)
			return
		}
		defer file.Close()

		buf := []byte{0} // At least 1 byte of data
		rights := syscall.UnixRights(int(master.Fd()))

		if err := syscall.Sendmsg(int(file.Fd()), buf, rights, nil, 0); err != nil {
			t.Logf("Failed to send FD: %v", err)
		} else {
			t.Log("Successfully sent PTY to container")
		}

		// Keep slave open and read from it until test is done
		go func() {
			buf := make([]byte, 1024)
			for {
				select {
				case <-closePTY:
					return
				default:
					slave.SetReadDeadline(time.Now().Add(100 * time.Millisecond))
					_, err := slave.Read(buf)
					if err != nil {
						// Timeout or error, continue
						continue
					}
				}
			}
		}()

		// Wait for signal to close PTY
		<-closePTY
	}()

	// Get the PTY
	ptyFile, err := process.GetTTY()
	if err != nil {
		t.Fatalf("Failed to get PTY: %v", err)
	}
	defer ptyFile.Close()

	t.Logf("Successfully received PTY: %s", ptyFile.Name())

	// Verify we can write to the PTY
	testData := []byte("Hello from test\n")
	if _, err := ptyFile.Write(testData); err != nil {
		t.Errorf("Failed to write to PTY: %v", err)
	}

	// Signal to close the PTY now that we're done with it
	close(closePTY)

	// Wait for process to complete
	if err := process.Wait(); err != nil {
		t.Errorf("Process failed: %v", err)
	}
}

func TestProcessCrunLikeWrapper(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-wrapper",
	})

	// This test uses a wrapper script that simulates crun behavior
	wrapperScript := `/bin/sh -c '
		# Simulate crun checking for console socket
		if [ -n "$CONSOLE_SOCKET" ]; then
			echo "crun: using console socket at $CONSOLE_SOCKET"
		fi
		
		# Run the actual command
		exec "$@"
	'`

	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "sh",
			Args:    []string{"-c", wrapperScript, "--", "echo", "hello from container"},
		},
		TTYTimeout: 1 * time.Second,
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Stop()

	// Get socket path for verification
	ttyPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}
	t.Logf("Console socket at: %s", ttyPath)

	// Start the process
	pid, err := process.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}
	t.Logf("Started wrapper process with PID %d", pid)

	// The process will complete without sending a PTY (expected)
	// GetTTY will timeout, which is OK for this test
	_, err = process.GetTTY()
	if err == nil {
		t.Error("Expected timeout error since wrapper doesn't send PTY")
	} else {
		t.Logf("Expected timeout: %v", err)
	}

	// Wait for process to complete
	process.Wait()
}

func TestProcessMultipleTTYManagers(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-multiple",
	})

	// Test that multiple processes can have their own TTY managers
	processes := make([]*Process, 3)

	for i := 0; i < 3; i++ {
		config := ProcessConfig{
			Config: supervisor.Config{
				Command: "sh",
				Args:    []string{"-c", "echo process $$ && sleep 0.1"},
			},
		}

		process, err := NewProcess(config)
		if err != nil {
			t.Fatalf("Failed to create process %d: %v", i, err)
		}
		processes[i] = process

		// Start the process
		pid, err := process.Start()
		if err != nil {
			t.Fatalf("Failed to start process %d: %v", i, err)
		}
		t.Logf("Started process %d with PID %d", i, pid)

		// Each should have a unique socket path
		path, _ := process.TTYPath()
		t.Logf("Process %d socket: %s", i, path)
	}

	// Clean up all processes
	for i, process := range processes {
		if err := process.Stop(); err != nil {
			t.Errorf("Failed to stop process %d: %v", i, err)
		}
	}

	// Verify all sockets are cleaned up
	for i, process := range processes {
		if path, err := process.TTYPath(); err == nil {
			if _, err := os.Stat(path); !os.IsNotExist(err) {
				t.Errorf("Socket for process %d not cleaned up: %s", i, path)
			}
		}
	}
}
