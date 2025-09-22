package main

import (
	"bytes"
	"context"
	"encoding/json"
	"io"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/services"
)

// Test harness for socket server tests
type testHarness struct {
	socketPath string
	system     *System
	server     *SockServer
	tmpDir     string
	t          *testing.T
}

func setupTestHarness(t *testing.T) *testHarness {
	t.Helper()

	// Create temporary directory
	tmpDir, err := os.MkdirTemp("", "sock-test-*")
	if err != nil {
		t.Fatal(err)
	}

	// Create socket path
	socketPath := filepath.Join(tmpDir, "api.sock")

	// For tests, use tmpDir as the write directory
	writeDir := tmpDir
	logDir := filepath.Join(writeDir, "logs")
	if err := os.MkdirAll(filepath.Join(logDir, "services"), 0755); err != nil {
		os.RemoveAll(tmpDir)
		t.Fatal(err)
	}

	// Set SPRITE_WRITE_DIR for consistency
	os.Setenv("SPRITE_WRITE_DIR", writeDir)

	// Create services manager with logging
	servicesManager, err := services.NewManager(tmpDir, services.WithLogDir(logDir))
	if err != nil {
		os.RemoveAll(tmpDir)
		t.Fatal(err)
	}

	// Start services manager
	if err := servicesManager.Start(); err != nil {
		os.RemoveAll(tmpDir)
		t.Fatal(err)
	}

	// Create system
	system := &System{
		servicesManager: servicesManager,
	}

	// Create and start socket server
	ctx := context.Background()
	server, err := NewSockServer(ctx, system, logDir)
	if err != nil {
		servicesManager.Close()
		os.RemoveAll(tmpDir)
		t.Fatal(err)
	}

	if err := server.Start(socketPath); err != nil {
		servicesManager.Close()
		os.RemoveAll(tmpDir)
		t.Fatal(err)
	}

	// Wait for socket to be ready
	time.Sleep(50 * time.Millisecond)

	return &testHarness{
		socketPath: socketPath,
		system:     system,
		server:     server,
		tmpDir:     tmpDir,
		t:          t,
	}
}

func (h *testHarness) cleanup() {
	h.server.Stop()
	h.system.servicesManager.Close()
	os.RemoveAll(h.tmpDir)
}

func (h *testHarness) makeRequest(method, path string, body interface{}) (*http.Response, error) {
	var bodyReader io.Reader
	if body != nil {
		jsonBody, err := json.Marshal(body)
		if err != nil {
			return nil, err
		}
		bodyReader = bytes.NewReader(jsonBody)
	}

	// Create unix socket client
	client := &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return net.Dial("unix", h.socketPath)
			},
		},
		Timeout: 10 * time.Second,
	}

	req, err := http.NewRequest(method, "http://localhost"+path, bodyReader)
	if err != nil {
		return nil, err
	}

	if body != nil {
		req.Header.Set("Content-Type", "application/json")
	}

	return client.Do(req)
}

// TestQuickExitWithError tests that we properly capture exit codes and stderr
// when a process exits quickly with an error
func TestQuickExitWithError(t *testing.T) {
	h := setupTestHarness(t)
	defer h.cleanup()

	// Create a service that exits immediately with an error
	serviceReq := map[string]interface{}{
		"cmd":   "bash",
		"args":  []string{"-c", "echo 'Error message' >&2; exit 42"},
		"needs": []string{},
	}

	// Create the service
	resp, err := h.makeRequest("PUT", "/v1/services/quick-fail", serviceReq)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		t.Fatalf("Expected status 200, got %d: %s", resp.StatusCode, body)
	}

	// Read the streaming response
	var events []LogEvent
	decoder := json.NewDecoder(resp.Body)

	// Set a timeout for reading events
	done := make(chan bool)
	go func() {
		for {
			var event LogEvent
			if err := decoder.Decode(&event); err != nil {
				if err != io.EOF {
					t.Logf("Decode error: %v", err)
				}
				break
			}
			events = append(events, event)
			t.Logf("Received event: %+v", event)
		}
		done <- true
	}()

	// Wait for events or timeout
	select {
	case <-done:
		// Events finished
	case <-time.After(3 * time.Second):
		t.Log("Timeout waiting for events")
	}

	// Verify we got the expected events
	var gotExit, gotStderr, gotComplete bool
	var exitCode int
	var stderrData string

	for _, event := range events {
		switch event.Type {
		case "exit":
			gotExit = true
			if event.ExitCode != nil {
				exitCode = *event.ExitCode
			}
		case "stderr":
			gotStderr = true
			stderrData += event.Data
		case "complete":
			gotComplete = true
		}
	}

	// Check results
	if !gotExit {
		t.Error("Did not receive exit event")
	}
	if exitCode != 42 {
		t.Errorf("Expected exit code 42, got %d", exitCode)
	}
	if !gotStderr {
		t.Error("Did not receive stderr event")
	}
	if !strings.Contains(stderrData, "Error message") {
		t.Errorf("Expected stderr to contain 'Error message', got: %s", stderrData)
	}
	if !gotComplete {
		t.Error("Did not receive complete event")
	}
}

// TestQuickExitWithStdout tests capturing stdout from a quickly exiting process
func TestQuickExitWithStdout(t *testing.T) {
	h := setupTestHarness(t)
	defer h.cleanup()

	// Create a service that outputs to stdout and exits immediately
	serviceReq := map[string]interface{}{
		"cmd":   "bash",
		"args":  []string{"-c", "echo 'Hello stdout'; echo 'Line 2'; exit 0"},
		"needs": []string{},
	}

	// Create the service
	resp, err := h.makeRequest("PUT", "/v1/services/quick-stdout", serviceReq)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		t.Fatalf("Expected status 200, got %d: %s", resp.StatusCode, body)
	}

	// Read the streaming response
	var events []LogEvent
	decoder := json.NewDecoder(resp.Body)

	done := make(chan bool)
	go func() {
		for {
			var event LogEvent
			if err := decoder.Decode(&event); err != nil {
				break
			}
			events = append(events, event)
			t.Logf("Received event: %+v", event)
		}
		done <- true
	}()

	select {
	case <-done:
	case <-time.After(3 * time.Second):
		t.Log("Timeout waiting for events")
	}

	// Verify we got stdout
	var gotStdout bool
	var stdoutData string

	for _, event := range events {
		if event.Type == "stdout" {
			gotStdout = true
			stdoutData += event.Data
		}
	}

	if !gotStdout {
		t.Error("Did not receive stdout event")
	}
	if !strings.Contains(stdoutData, "Hello stdout") {
		t.Errorf("Expected stdout to contain 'Hello stdout', got: %s", stdoutData)
	}
	if !strings.Contains(stdoutData, "Line 2") {
		t.Errorf("Expected stdout to contain 'Line 2', got: %s", stdoutData)
	}
}

// TestVeryQuickExit tests a process that exits before we can even attach to it
func TestVeryQuickExit(t *testing.T) {
	h := setupTestHarness(t)
	defer h.cleanup()

	// Create a service that exits immediately (true command)
	serviceReq := map[string]interface{}{
		"cmd":   "true",
		"args":  []string{},
		"needs": []string{},
	}

	// Create the service
	resp, err := h.makeRequest("PUT", "/v1/services/instant-exit", serviceReq)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		t.Fatalf("Expected status 200, got %d: %s", resp.StatusCode, body)
	}

	// Read events
	var events []LogEvent
	decoder := json.NewDecoder(resp.Body)

	done := make(chan bool)
	go func() {
		for {
			var event LogEvent
			if err := decoder.Decode(&event); err != nil {
				break
			}
			events = append(events, event)
			t.Logf("Received event: %+v", event)
		}
		done <- true
	}()

	select {
	case <-done:
	case <-time.After(3 * time.Second):
		t.Log("Timeout waiting for events")
	}

	// Should still get exit event with code 0
	var gotExit bool
	var exitCode int = -1

	for _, event := range events {
		if event.Type == "exit" {
			gotExit = true
			if event.ExitCode != nil {
				exitCode = *event.ExitCode
			}
		}
	}

	if !gotExit {
		t.Error("Did not receive exit event for instant-exit process")
	}
	if exitCode != 0 {
		t.Errorf("Expected exit code 0, got %d", exitCode)
	}
}

// TestLongRunningService tests that we properly handle services that run longer
func TestLongRunningService(t *testing.T) {
	h := setupTestHarness(t)
	defer h.cleanup()

	// Create a service that runs for a while
	serviceReq := map[string]interface{}{
		"cmd": "bash",
		"args": []string{"-c", `
			echo "Starting service"
			sleep 0.5
			echo "Still running" >&2
			sleep 0.5
			echo "Finishing up"
			exit 0
		`},
		"needs": []string{},
	}

	// Create the service with a shorter timeout
	resp, err := h.makeRequest("PUT", "/v1/services/long-runner?timeout=2s", serviceReq)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	// Collect all events
	var events []LogEvent
	decoder := json.NewDecoder(resp.Body)

	for {
		var event LogEvent
		if err := decoder.Decode(&event); err != nil {
			break
		}
		events = append(events, event)
		t.Logf("Received event: %+v", event)
	}

	// Verify we got all expected output
	var stdoutCount, stderrCount int
	var gotExit bool

	for _, event := range events {
		switch event.Type {
		case "stdout":
			stdoutCount++
		case "stderr":
			stderrCount++
		case "exit":
			gotExit = true
		}
	}

	if stdoutCount < 2 {
		t.Errorf("Expected at least 2 stdout events, got %d", stdoutCount)
	}
	if stderrCount < 1 {
		t.Errorf("Expected at least 1 stderr event, got %d", stderrCount)
	}
	if !gotExit {
		t.Error("Did not receive exit event")
	}
}

// TestServiceFailsToStart tests handling when a service fails to start
func TestServiceFailsToStart(t *testing.T) {
	h := setupTestHarness(t)
	defer h.cleanup()

	// Create a service with invalid command
	serviceReq := map[string]interface{}{
		"cmd":   "/nonexistent/command",
		"args":  []string{},
		"needs": []string{},
	}

	// Create the service
	resp, err := h.makeRequest("PUT", "/v1/services/fail-start", serviceReq)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	// Collect events
	var events []LogEvent
	decoder := json.NewDecoder(resp.Body)

	done := make(chan bool)
	go func() {
		for {
			var event LogEvent
			if err := decoder.Decode(&event); err != nil {
				break
			}
			events = append(events, event)
			t.Logf("Received event: %+v", event)
		}
		done <- true
	}()

	select {
	case <-done:
	case <-time.After(3 * time.Second):
	}

	// Should get an exit event with non-zero code
	var gotExit bool
	var exitCode int = -1

	for _, event := range events {
		if event.Type == "exit" {
			gotExit = true
			if event.ExitCode != nil {
				exitCode = *event.ExitCode
			}
		}
	}

	if !gotExit {
		t.Error("Did not receive exit event for failed service")
	}
	if exitCode == 0 {
		t.Error("Expected non-zero exit code for failed service")
	}
}

// TestLongRunningServiceWithOutput tests services that run for the full duration and produce output
func TestLongRunningServiceWithOutput(t *testing.T) {
	h := setupTestHarness(t)
	defer h.cleanup()

	// Create a service that continuously outputs
	serviceReq := map[string]interface{}{
		"cmd": "bash",
		"args": []string{"-c", `
			for i in {1..5}; do
				echo "Line $i to stdout"
				echo "Line $i to stderr" >&2
				sleep 0.5
			done
		`},
		"needs": []string{},
	}

	// Create the service with a 2-second timeout (will timeout before completion)
	resp, err := h.makeRequest("PUT", "/v1/services/continuous-output?duration=2s", serviceReq)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	// Collect all events
	var events []LogEvent
	decoder := json.NewDecoder(resp.Body)

	for {
		var event LogEvent
		if err := decoder.Decode(&event); err != nil {
			break
		}
		events = append(events, event)
		t.Logf("Received event: %+v", event)
	}

	// Verify we got started event
	var gotStarted bool
	var gotStdout, gotStderr bool
	var stdoutData, stderrData string

	for _, event := range events {
		switch event.Type {
		case "started":
			gotStarted = true
		case "stdout":
			gotStdout = true
			stdoutData += event.Data
		case "stderr":
			gotStderr = true
			stderrData += event.Data
		}
	}

	if !gotStarted {
		t.Error("Did not receive started event")
	}
	if !gotStdout {
		t.Error("Did not receive stdout event")
	}
	if !gotStderr {
		t.Error("Did not receive stderr event")
	}

	// Should have gotten at least some output before timeout
	if !strings.Contains(stdoutData, "Line 1 to stdout") {
		t.Errorf("Expected stdout to contain 'Line 1 to stdout', got: %s", stdoutData)
	}
	if !strings.Contains(stderrData, "Line 1 to stderr") {
		t.Errorf("Expected stderr to contain 'Line 1 to stderr', got: %s", stderrData)
	}
}
