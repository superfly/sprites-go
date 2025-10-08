package terminal

import (
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/pkg/tap"
)

// TestWebSocketDisconnectKillsWrapperChild verifies that when using wrapper commands,
// child processes are tracked and killed when the websocket disconnects
func TestWebSocketDisconnectKillsWrapperChild(t *testing.T) {
	// This test always runs in Linux Docker environment with /proc
	// Track process lifecycle
	var wrapperPID int
	var mu sync.Mutex

	// Create a wrapper script that spawns a child process
	wrapperScript := `#!/bin/sh
# Wrapper process
echo "WRAPPER_PID:$$"

# Start a child process and output its PID
sh -c 'echo "CHILD_PID:$$"; trap "" TERM; while true; do sleep 0.5; done' &
CHILD=$!
echo "CHILD_PID:$CHILD"

# Sleep briefly to ensure child is in process table
sleep 0.2

# Wait for the child
wait $CHILD
`

	// Create the wrapper script file
	tmpFile := filepath.Join(t.TempDir(), "test-wrapper.sh")
	if err := os.WriteFile(tmpFile, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("failed to create wrapper script: %v", err)
	}

	logger := tap.NewDiscardLogger()

	session := NewSession(
		WithCommand("dummy"), // This is replaced by the wrapper
		WithTTY(false),
		WithWrapper([]string{tmpFile}), // Use our test wrapper
		WithOnProcessStart(func(pid int) {
			mu.Lock()
			wrapperPID = pid
			mu.Unlock()
		}),
		WithLogger(logger),
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

	// Collect PIDs from output
	var childPID int
	foundChild := make(chan bool)

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
					lines := strings.Split(output, "\n")
					for _, line := range lines {
						line = strings.TrimSpace(line)
						if strings.HasPrefix(line, "CHILD_PID:") {
							parts := strings.Split(line, ":")
							if len(parts) == 2 {
								if pid, err := strconv.Atoi(strings.TrimSpace(parts[1])); err == nil && pid > 0 {
									childPID = pid
									foundChild <- true
									return
								}
							}
						}
					}
				}
			}
		}
	}()

	// Wait for child process to start
	select {
	case <-foundChild:
		t.Logf("Child process started with PID %d", childPID)
	case <-time.After(3 * time.Second):
		t.Fatal("timeout waiting for child process to start")
	}

	// Wait a bit to ensure tracking is complete
	time.Sleep(500 * time.Millisecond)

	// Verify both processes are running
	mu.Lock()
	wPID := wrapperPID
	mu.Unlock()

	if wPID == 0 {
		t.Fatal("wrapper PID not tracked")
	}

	// Check wrapper is alive
	if err := syscall.Kill(wPID, 0); err != nil {
		t.Fatalf("wrapper process %d is not running before disconnect: %v", wPID, err)
	}

	// Check child is alive
	if err := syscall.Kill(childPID, 0); err != nil {
		t.Fatalf("child process %d is not running before disconnect: %v", childPID, err)
	}

	t.Logf("Both processes running - wrapper: %d, child: %d", wPID, childPID)

	// Now disconnect the websocket
	conn.Close()

	// Give time for cleanup
	time.Sleep(500 * time.Millisecond)

	// Verify both processes are dead
	wrapperAlive := syscall.Kill(wPID, 0) == nil
	childAlive := syscall.Kill(childPID, 0) == nil

	if wrapperAlive {
		t.Errorf("wrapper process %d is still running after websocket disconnect", wPID)
		syscall.Kill(wPID, syscall.SIGKILL)
	}

	if childAlive {
		t.Errorf("child process %d is still running after websocket disconnect", childPID)
		syscall.Kill(childPID, syscall.SIGKILL)
	}

	if !wrapperAlive && !childAlive {
		t.Logf("Success: both wrapper (%d) and child (%d) processes were terminated", wPID, childPID)
	}
}
