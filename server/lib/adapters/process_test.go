package adapters

import (
	"context"
	"strings"
	"syscall"
	"testing"
	"time"
)

func TestProcessBasicLifecycle(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"echo", "hello"},
		MaxRetries:              0, // No retries
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx := context.Background()

	events := process.Start(ctx)

	var receivedEvents []EventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == EventStopped || event == EventFailed {
			break
		}
	}

	// Should see: Starting -> Started -> Stopped
	expectedEvents := []EventType{EventStarting, EventStarted, EventStopped}
	if len(receivedEvents) != len(expectedEvents) {
		t.Fatalf("Expected %d events, got %d: %v", len(expectedEvents), len(receivedEvents), receivedEvents)
	}

	for i, expected := range expectedEvents {
		if receivedEvents[i] != expected {
			t.Errorf("Event %d: expected %v, got %v", i, expected, receivedEvents[i])
		}
	}
}

func TestProcessStop(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"sleep", "10"},
		MaxRetries:              0, // No retries
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx := context.Background()

	events := process.Start(ctx)

	// Wait for process to start
	var started bool
	for event := range events {
		if event == EventStarted {
			started = true
			break
		}
		if event == EventFailed {
			t.Fatal("Process failed to start")
		}
	}

	if !started {
		t.Fatal("Process never started")
	}

	// Stop the process
	process.Stop()

	// Continue reading events until stopped
	var receivedEvents []EventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == EventStopped || event == EventFailed {
			break
		}
	}

	// Should see stopping and stopped events
	found := false
	for _, event := range receivedEvents {
		if event == EventStopped {
			found = true
			break
		}
	}

	if !found {
		t.Errorf("Expected EventStopped, got events: %v", receivedEvents)
	}
}

func TestProcessSignal(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"sleep", "10"},
		MaxRetries:              0, // No retries
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx := context.Background()

	events := process.Start(ctx)

	// Wait for process to start
	var started bool
	for event := range events {
		if event == EventStarted {
			started = true
			break
		}
		if event == EventFailed {
			t.Fatal("Process failed to start")
		}
	}

	if !started {
		t.Fatal("Process never started")
	}

	// Send a non-terminating signal first
	process.Signal(syscall.SIGUSR1)

	// Should see a signaled event
	signalReceived := false
	timeout := time.After(time.Second)

readSignalLoop:
	for {
		select {
		case event := <-events:
			if event == EventSignaled {
				signalReceived = true
				break readSignalLoop
			}
			if event == EventStopped || event == EventFailed {
				t.Fatal("Process stopped unexpectedly")
			}
		case <-timeout:
			break readSignalLoop
		}
	}

	if !signalReceived {
		t.Error("Expected EventSignaled after sending SIGUSR1")
	}

	// Now send SIGTERM (terminating signal)
	process.Signal(syscall.SIGTERM)

	// Continue reading events until stopped
	var receivedEvents []EventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == EventStopped || event == EventFailed {
			break
		}
	}

	// Should see stopping and stopped events
	found := false
	for _, event := range receivedEvents {
		if event == EventStopped {
			found = true
			break
		}
	}

	if !found {
		t.Errorf("Expected EventStopped after SIGTERM, got events: %v", receivedEvents)
	}
}

func TestProcessRestart(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"sh", "-c", "echo 'run'; exit 1"}, // Will exit with error
		MaxRetries:              2,                                          // Allow 2 retries
		RestartDelay:            10 * time.Millisecond,                      // Short delay for testing
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx := context.Background()

	events := process.Start(ctx)

	var receivedEvents []EventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == EventFailed || event == EventStopped {
			break
		}
	}

	// Should see multiple restart cycles before failing
	startingCount := 0
	restartingCount := 0
	for _, event := range receivedEvents {
		if event == EventStarting {
			startingCount++
		}
		if event == EventRestarting {
			restartingCount++
		}
	}

	if startingCount < 2 {
		t.Errorf("Expected at least 2 starting events (initial + retries), got %d", startingCount)
	}

	if restartingCount < 1 {
		t.Errorf("Expected at least 1 restarting event, got %d", restartingCount)
	}

	// Final event should be EventFailed since retries are exhausted
	lastEvent := receivedEvents[len(receivedEvents)-1]
	if lastEvent != EventFailed {
		t.Errorf("Expected final event to be EventFailed, got %v", lastEvent)
	}
}

func TestProcessFailedCommand(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"nonexistent-command-that-should-not-exist"},
		MaxRetries:              0,
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx := context.Background()

	events := process.Start(ctx)

	var receivedEvents []EventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == EventFailed || event == EventStopped {
			break
		}
	}

	// Should see: Starting -> Failed
	if len(receivedEvents) < 2 {
		t.Fatalf("Expected at least 2 events, got %d: %v", len(receivedEvents), receivedEvents)
	}

	if receivedEvents[0] != EventStarting {
		t.Errorf("First event should be EventStarting, got %v", receivedEvents[0])
	}

	if receivedEvents[len(receivedEvents)-1] != EventFailed {
		t.Errorf("Last event should be EventFailed, got %v", receivedEvents[len(receivedEvents)-1])
	}
}

func TestProcessPipes(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"echo", "hello world"},
		MaxRetries:              0, // No retries for pipe compatibility
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)

	// Test stdout pipe
	stdout, err := process.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe: %v", err)
	}

	// Test stderr pipe
	stderr, err := process.StderrPipe()
	if err != nil {
		t.Fatalf("Failed to get stderr pipe: %v", err)
	}

	ctx := context.Background()
	events := process.Start(ctx)

	// Read from stdout
	go func() {
		defer stdout.Close()
		buf := make([]byte, 1024)
		n, err := stdout.Read(buf)
		if err != nil && err.Error() != "EOF" {
			t.Errorf("Failed to read from stdout: %v", err)
			return
		}
		output := strings.TrimSpace(string(buf[:n]))
		if output != "hello world" {
			t.Errorf("Expected 'hello world', got '%s'", output)
		}
	}()

	// Close stderr since we're not using it
	stderr.Close()

	// Wait for process to complete
	for event := range events {
		if event == EventStopped || event == EventFailed {
			break
		}
	}
}

func TestProcessPipeIncompatibilityWithRetries(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"echo", "hello"},
		MaxRetries:              1, // Has retries
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)

	// Should fail to get pipes when retries are enabled
	_, err := process.StdoutPipe()
	if err == nil {
		t.Error("Expected error when getting stdout pipe with MaxRetries > 0")
	}

	_, err = process.StderrPipe()
	if err == nil {
		t.Error("Expected error when getting stderr pipe with MaxRetries > 0")
	}

	_, err = process.StdinPipe()
	if err == nil {
		t.Error("Expected error when getting stdin pipe with MaxRetries > 0")
	}
}

func TestProcessContextCancellation(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"sleep", "10"},
		MaxRetries:              0,
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx, cancel := context.WithCancel(context.Background())

	events := process.Start(ctx)

	// Wait for process to start
	var started bool
	for event := range events {
		if event == EventStarted {
			started = true
			break
		}
		if event == EventFailed {
			t.Fatal("Process failed to start")
		}
	}

	if !started {
		t.Fatal("Process never started")
	}

	// Cancel the context
	cancel()

	// Should see the process stop due to context cancellation
	var receivedEvents []EventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == EventStopped || event == EventFailed {
			break
		}
	}

	// Should end with EventStopped
	if len(receivedEvents) == 0 {
		t.Fatal("No events received after context cancellation")
	}

	lastEvent := receivedEvents[len(receivedEvents)-1]
	if lastEvent != EventStopped {
		t.Errorf("Expected EventStopped after context cancellation, got %v", lastEvent)
	}
}
