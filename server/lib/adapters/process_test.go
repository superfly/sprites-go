package adapters

import (
	"context"
	"os"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

// EventCapture helps capture events from Observer pattern for testing
type EventCapture struct {
	mu     sync.Mutex
	events []EventType
	done   chan struct{}
}

func NewEventCapture() *EventCapture {
	return &EventCapture{
		events: make([]EventType, 0),
		done:   make(chan struct{}),
	}
}

func (ec *EventCapture) AddEvent(event EventType) {
	ec.mu.Lock()
	defer ec.mu.Unlock()
	ec.events = append(ec.events, event)
}

func (ec *EventCapture) GetEvents() []EventType {
	ec.mu.Lock()
	defer ec.mu.Unlock()
	return append([]EventType{}, ec.events...) // Return copy
}

func (ec *EventCapture) WaitForEvent(target EventType, timeout time.Duration) bool {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		events := ec.GetEvents()
		for _, event := range events {
			if event == target {
				return true
			}
		}
		time.Sleep(time.Millisecond)
	}
	return false
}

func (ec *EventCapture) WaitForEvents(targets []EventType, timeout time.Duration) bool {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		events := ec.GetEvents()
		if len(events) >= len(targets) {
			match := true
			for i, target := range targets {
				if i >= len(events) || events[i] != target {
					match = false
					break
				}
			}
			if match {
				return true
			}
		}
		time.Sleep(time.Millisecond)
	}
	return false
}

func TestProcessBasicLifecycle(t *testing.T) {
	config := ProcessConfig{
		Command:                 []string{"echo", "hello"},
		MaxRetries:              0, // No retries
		RestartDelay:            0,
		GracefulShutdownTimeout: time.Second,
	}

	process := NewProcess(config)
	ctx := context.Background()

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	err := process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for completion
	if !capture.WaitForEvent(EventStopped, 5*time.Second) && !capture.WaitForEvent(EventFailed, 5*time.Second) {
		t.Fatal("Process never completed")
	}

	events := capture.GetEvents()

	// Should see: Starting -> Started -> Stopped
	expectedEvents := []EventType{EventStarting, EventStarted, EventStopped}
	if len(events) != len(expectedEvents) {
		t.Fatalf("Expected %d events, got %d: %v", len(expectedEvents), len(events), events)
	}

	for i, expected := range expectedEvents {
		if events[i] != expected {
			t.Errorf("Event %d: expected %v, got %v", i, expected, events[i])
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

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	err := process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for process to start
	if !capture.WaitForEvent(EventStarted, 5*time.Second) {
		t.Fatal("Process never started")
	}

	// Stop the process
	process.Stop()

	// Wait for process to stop
	if !capture.WaitForEvent(EventStopped, 5*time.Second) {
		t.Fatal("Process never stopped")
	}

	events := capture.GetEvents()

	// Should see stopped event
	found := false
	for _, event := range events {
		if event == EventStopped {
			found = true
			break
		}
	}

	if !found {
		t.Errorf("Expected EventStopped, got events: %v", events)
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

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	err := process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for process to start
	if !capture.WaitForEvent(EventStarted, 5*time.Second) {
		t.Fatal("Process never started")
	}

	// Send a non-terminating signal first
	process.Signal(syscall.SIGUSR1)

	// Should see a signaled event
	if !capture.WaitForEvent(EventSignaled, 2*time.Second) {
		t.Error("Expected EventSignaled after sending SIGUSR1")
	}

	// Now send SIGTERM (terminating signal)
	process.Signal(syscall.SIGTERM)

	// Should see stopping and stopped events
	if !capture.WaitForEvent(EventStopped, 5*time.Second) {
		t.Error("Expected EventStopped after SIGTERM")
	}

	events := capture.GetEvents()

	// Should see stopped event
	found := false
	for _, event := range events {
		if event == EventStopped {
			found = true
			break
		}
	}

	if !found {
		t.Errorf("Expected EventStopped after SIGTERM, got events: %v", events)
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

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	err := process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for final failure
	if !capture.WaitForEvent(EventFailed, 10*time.Second) {
		t.Fatal("Process never failed")
	}

	events := capture.GetEvents()

	// Should see multiple restart cycles before failing
	startingCount := 0
	restartingCount := 0
	for _, event := range events {
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
	lastEvent := events[len(events)-1]
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

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	err := process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for failure
	if !capture.WaitForEvent(EventFailed, 5*time.Second) {
		t.Fatal("Process never failed")
	}

	events := capture.GetEvents()

	// Should see: Starting -> Failed
	if len(events) < 2 {
		t.Fatalf("Expected at least 2 events, got %d: %v", len(events), events)
	}

	if events[0] != EventStarting {
		t.Errorf("First event should be EventStarting, got %v", events[0])
	}

	if events[len(events)-1] != EventFailed {
		t.Errorf("Last event should be EventFailed, got %v", events[len(events)-1])
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

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	ctx := context.Background()
	err = process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

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
	if !capture.WaitForEvent(EventStopped, 5*time.Second) && !capture.WaitForEvent(EventFailed, 5*time.Second) {
		t.Fatal("Process never completed")
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

	// Set up event capture
	capture := NewEventCapture()
	process.SetEventHandlers(ProcessEventHandlers{
		Starting:   func() { capture.AddEvent(EventStarting) },
		Started:    func() { capture.AddEvent(EventStarted) },
		Stopping:   func() { capture.AddEvent(EventStopping) },
		Stopped:    func() { capture.AddEvent(EventStopped) },
		Restarting: func() { capture.AddEvent(EventRestarting) },
		Signaled:   func(os.Signal) { capture.AddEvent(EventSignaled) },
		Failed:     func(error) { capture.AddEvent(EventFailed) },
	})

	err := process.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for process to start
	if !capture.WaitForEvent(EventStarted, 5*time.Second) {
		t.Fatal("Process never started")
	}

	// Cancel the context
	cancel()

	// Should see the process stop due to context cancellation
	if !capture.WaitForEvent(EventStopped, 5*time.Second) {
		events := capture.GetEvents()
		t.Fatalf("Process never stopped after context cancellation. Events: %v", events)
	}

	events := capture.GetEvents()

	// Should end with EventStopped
	if len(events) == 0 {
		t.Fatal("No events received after context cancellation")
	}

	lastEvent := events[len(events)-1]
	if lastEvent != EventStopped {
		t.Errorf("Expected EventStopped after context cancellation, got %v", lastEvent)
	}
}
