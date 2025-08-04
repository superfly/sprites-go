package terminal

import (
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketDisconnectKillsProcess verifies that when a websocket connection
// is closed, the running process is terminated
func TestWebSocketDisconnectKillsProcess(t *testing.T) {
	// Track process lifecycle
	var processStarted bool
	var processPID int
	var mu sync.Mutex

	// Create a test session that runs a long-lived process
	// Using a process that ignores SIGTERM to ensure it's killed by context cancellation
	session := NewSession(
		WithCommand("sh", "-c", `
			trap '' TERM
			echo "PROCESS_STARTED"
			while true; do 
				echo "STILL_RUNNING"
				sleep 0.5
			done
		`),
		WithTTY(false),
		WithOnProcessStart(func(pid int) {
			mu.Lock()
			processStarted = true
			processPID = pid
			mu.Unlock()
		}),
	)

	handler := NewWebSocketHandler(session)

	// Set up test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Logf("handler error (expected on disconnect): %v", err)
		}
	}))
	defer server.Close()

	// Connect as a client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}

	// Wait for process to start and output some data
	startupComplete := make(chan bool)
	stillRunningCount := 0

	go func() {
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				close(startupComplete)
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 1 {
				streamID := StreamID(data[0])
				if streamID == StreamStdout {
					output := string(data[1:])
					if strings.Contains(output, "PROCESS_STARTED") {
						// Give it a moment to settle
						time.Sleep(100 * time.Millisecond)
					}
					if strings.Contains(output, "STILL_RUNNING") {
						stillRunningCount++
						if stillRunningCount >= 2 {
							// Process is definitely running
							startupComplete <- true
							return
						}
					}
				}
			}
		}
	}()

	// Wait for process to be running
	select {
	case <-startupComplete:
		// Process is running
	case <-time.After(5 * time.Second):
		t.Fatal("timeout waiting for process to start")
	}

	// Verify process is running
	mu.Lock()
	if !processStarted {
		mu.Unlock()
		t.Fatal("process never started")
	}
	pid := processPID
	mu.Unlock()

	// Verify process is alive by sending signal 0
	err = syscall.Kill(pid, 0)
	if err != nil {
		t.Fatalf("process %d is not running before disconnect: %v", pid, err)
	}

	// Now disconnect the websocket
	conn.Close()

	// Give the server time to detect disconnection and kill the process
	time.Sleep(500 * time.Millisecond)

	// Verify process is dead
	err = syscall.Kill(pid, 0)
	if err == nil {
		// Process is still alive - this is the bug we're fixing
		t.Errorf("process %d is still running after websocket disconnect", pid)
		
		// Kill it manually to clean up
		process, _ := os.FindProcess(pid)
		if process != nil {
			process.Kill()
		}
	} else {
		t.Logf("process %d was successfully terminated after websocket disconnect", pid)
	}
}

// TestWebSocketDisconnectDuringStdin verifies that process is killed even
// when websocket disconnects while waiting for stdin
func TestWebSocketDisconnectDuringStdin(t *testing.T) {
	// Track process lifecycle
	var processPID int
	var mu sync.Mutex

	// Create a test session that reads from stdin
	session := NewSession(
		WithCommand("sh", "-c", `
			echo "WAITING_FOR_INPUT"
			read line
			echo "GOT: $line"
		`),
		WithTTY(false),
		WithOnProcessStart(func(pid int) {
			mu.Lock()
			processPID = pid
			mu.Unlock()
		}),
	)

	handler := NewWebSocketHandler(session)

	// Set up test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Logf("handler error (expected on disconnect): %v", err)
		}
	}))
	defer server.Close()

	// Connect as a client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}

	// Wait for process to output initial message
	waitingForInput := make(chan bool)

	go func() {
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 1 {
				streamID := StreamID(data[0])
				if streamID == StreamStdout {
					output := string(data[1:])
					if strings.Contains(output, "WAITING_FOR_INPUT") {
						waitingForInput <- true
						return
					}
				}
			}
		}
	}()

	// Wait for process to be waiting for input
	select {
	case <-waitingForInput:
		// Process is waiting
	case <-time.After(3 * time.Second):
		t.Fatal("timeout waiting for process to be ready")
	}

	// Get the PID
	mu.Lock()
	pid := processPID
	mu.Unlock()

	if pid == 0 {
		t.Fatal("process PID not captured")
	}

	// Verify process is running
	err = syscall.Kill(pid, 0)
	if err != nil {
		t.Fatalf("process %d is not running before disconnect: %v", pid, err)
	}

	// Disconnect while process is waiting for input
	conn.Close()

	// Give time for disconnection to be processed
	time.Sleep(500 * time.Millisecond)

	// Verify process is dead
	err = syscall.Kill(pid, 0)
	if err == nil {
		t.Errorf("process %d is still running after websocket disconnect during stdin wait", pid)
		process, _ := os.FindProcess(pid)
		if process != nil {
			process.Kill()
		}
	} else {
		t.Logf("process %d was successfully terminated after websocket disconnect", pid)
	}
}