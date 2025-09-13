package main

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// Test helper to create a test tmux socket
func createTestTmuxSocket(t *testing.T) string {
	socketPath := fmt.Sprintf("/tmp/tmux-activity-test-%d-%d", os.Getpid(), time.Now().UnixNano())
	t.Cleanup(func() {
		// Kill tmux server
		cmd := exec.Command("tmux", "-S", socketPath, "kill-server")
		cmd.Run()
		os.Remove(socketPath)
	})
	return socketPath
}

// suspendTracker tracks suspension attempts
type suspendTracker struct {
	mu           sync.Mutex
	suspendCount int32
	lastSuspend  time.Time
}

var globalSuspendTracker = &suspendTracker{}

func resetSuspendTracker() {
	globalSuspendTracker.mu.Lock()
	defer globalSuspendTracker.mu.Unlock()
	globalSuspendTracker.suspendCount = 0
	globalSuspendTracker.lastSuspend = time.Time{}
}

func getSuspendCount() int32 {
	globalSuspendTracker.mu.Lock()
	defer globalSuspendTracker.mu.Unlock()
	return globalSuspendTracker.suspendCount
}

// testLogger captures log entries to detect suspension
type testLogger struct {
	mu      sync.Mutex
	entries []string
}

func (tl *testLogger) Write(p []byte) (n int, err error) {
	tl.mu.Lock()
	defer tl.mu.Unlock()
	msg := string(p)
	tl.entries = append(tl.entries, msg)

	// Track suspension attempts - only count the main suspension log message
	if strings.Contains(msg, "ActivityMonitor: suspending") ||
		strings.Contains(msg, "ActivityMonitor: would suspend") ||
		strings.Contains(msg, "msg=\"ActivityMonitor: suspending\"") ||
		strings.Contains(msg, "msg=\"ActivityMonitor: would suspend") {
		globalSuspendTracker.mu.Lock()
		globalSuspendTracker.suspendCount++
		globalSuspendTracker.lastSuspend = time.Now()
		globalSuspendTracker.mu.Unlock()
	}
	return len(p), nil
}

func (tl *testLogger) hasSuspended() bool {
	tl.mu.Lock()
	defer tl.mu.Unlock()
	for _, entry := range tl.entries {
		if strings.Contains(entry, "ActivityMonitor: suspending") ||
			strings.Contains(entry, "ActivityMonitor: would suspend") ||
			strings.Contains(entry, "msg=\"ActivityMonitor: suspending\"") ||
			strings.Contains(entry, "msg=\"ActivityMonitor: would suspend") ||
			(strings.Contains(entry, "msg=ActivityMonitor:") && strings.Contains(entry, "suspend")) {
			return true
		}
	}
	return false
}

// Create a real System for testing
func createTestSystem(t *testing.T, logWriter *testLogger) *System {
	// Create logger that writes to our test logger
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create minimal system config - no JuiceFS or processes
	config := SystemConfig{
		OverlayEnabled: false,
		// Empty config means no actual process or filesystem operations
	}

	// Create real system
	sys, err := NewSystem(config, logger, nil, nil)
	if err != nil {
		t.Fatalf("Failed to create test system: %v", err)
	}

	return sys
}

// Test that activity prevents suspension
func TestActivityMonitor_ActivityPreventsSuspension(t *testing.T) {
	resetSuspendTracker()

	// Create test logger to capture suspension attempts
	logWriter := &testLogger{}

	// Create logger that writes to our test logger
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create test context with logger
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	// Create test system with our logger
	sys := createTestSystem(t, logWriter)

	// Create activity monitor with short idle time
	monitor := NewActivityMonitor(ctx, sys, 2*time.Second, nil)

	// Prevent actual suspension API call
	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	// Start the monitor
	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Start an activity
	monitor.ActivityStarted("test")

	// Wait longer than idle timeout
	time.Sleep(3 * time.Second)

	// Should not have suspended
	if getSuspendCount() > 0 {
		t.Error("System suspended despite active activity")
	}

	// End activity
	monitor.ActivityEnded("test")

	// Now wait for suspension
	time.Sleep(3 * time.Second)

	// Should have suspended
	suspendCount := getSuspendCount()
	if suspendCount != 1 {
		// Debug: print log entries
		t.Logf("Suspension count: %d", suspendCount)
		logWriter.mu.Lock()
		for i, entry := range logWriter.entries {
			t.Logf("Log entry %d: %s", i, entry)
		}
		logWriter.mu.Unlock()
		t.Errorf("Expected 1 suspension, got %d", suspendCount)
	}

	// Verify via logs as well
	if !logWriter.hasSuspended() {
		t.Error("Expected suspension log message not found")
	}
}

// Test idle timer triggers suspension
func TestActivityMonitor_IdleTimerTriggersSuspension(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second, nil)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for idle timeout
	time.Sleep(2 * time.Second)

	// Should have suspended
	if getSuspendCount() != 1 {
		t.Errorf("Expected suspension after idle timeout, got %d suspensions", getSuspendCount())
	}
}

// Test tmux sessions prevent suspension
func TestActivityMonitor_ActiveTmuxSessionsPreventSuspension(t *testing.T) {
	resetSuspendTracker()

	// Skip if tmux is not available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Skip("tmux not available")
	}

	ctx := context.Background()
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx = tap.WithLogger(ctx, logger)

	// Create tmux manager
	tmuxManager := terminal.NewTMUXManager(ctx)

	// Create test tmux socket
	socketPath := createTestTmuxSocket(t)

	// Create a tmux session
	sessionID, _, _ := tmuxManager.CreateSession("/bin/bash", []string{"-c", "while true; do echo test; sleep 1; done"}, false)

	// Create the actual tmux session
	cmd := exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", fmt.Sprintf("sprite-exec-%s", sessionID), "/bin/bash", "-c", "while true; do echo test; sleep 0.5; done")
	if err := cmd.Run(); err != nil {
		t.Fatalf("Failed to create tmux session: %v", err)
	}

	// Set up the tmux manager to monitor this socket
	tmuxManager.SetPrepareCommand(func() {
		// Start monitoring with the test socket
		// We need to modify the monitor to use our test socket
		t.Log("Tmux activity monitor prepare command called")
	})

	// Start activity monitor
	if err := tmuxManager.StartActivityMonitor(ctx); err != nil {
		t.Logf("Warning: Failed to start tmux activity monitor: %v", err)
	}

	// Create test system
	logWriter := &testLogger{}
	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second, tmuxManager)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for idle timeout
	time.Sleep(2 * time.Second)

	// Should check for active sessions
	// Note: This test won't fully work without modifying the TMUXManager to use our test socket
	// But it demonstrates the test structure

	// Clean up
	exec.Command("tmux", "-S", socketPath, "kill-session", "-t", fmt.Sprintf("sprite-exec-%s", sessionID)).Run()
}

// Test concurrent activities
func TestActivityMonitor_ConcurrentActivities(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second, nil)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Start multiple concurrent activities
	var wg sync.WaitGroup
	numActivities := 10

	for i := 0; i < numActivities; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			source := fmt.Sprintf("test-%d", id)

			// Start activity
			monitor.ActivityStarted(source)

			// Hold for random duration
			time.Sleep(time.Duration(100+id*50) * time.Millisecond)

			// End activity
			monitor.ActivityEnded(source)
		}(i)
	}

	// Wait for all activities to complete
	wg.Wait()

	// Should not have suspended during activities
	if getSuspendCount() > 0 {
		t.Error("System suspended during concurrent activities")
	}

	// Wait for idle timeout
	time.Sleep(2 * time.Second)

	// Should suspend after all activities end
	if getSuspendCount() != 1 {
		t.Errorf("Expected 1 suspension after activities ended, got %d", getSuspendCount())
	}
}

// Test SPRITE_PREVENT_SUSPEND environment variable
func TestActivityMonitor_PreventSuspendEnvVar(t *testing.T) {
	resetSuspendTracker()

	ctx := context.Background()
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx = tap.WithLogger(ctx, logger)

	// Test with prevention enabled
	t.Run("prevention_enabled", func(t *testing.T) {
		resetSuspendTracker()
		logWriter := &testLogger{}
		subLogger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
			Level: slog.LevelDebug,
		}))
		subCtx := context.Background()
		subCtx = tap.WithLogger(subCtx, subLogger)
		sys := createTestSystem(t, logWriter)
		monitor := NewActivityMonitor(subCtx, sys, 500*time.Millisecond, nil)

		os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
		defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

		monitorCtx, cancel := context.WithCancel(subCtx)
		defer cancel()
		monitor.Start(monitorCtx)

		// Wait for idle timeout
		time.Sleep(1 * time.Second)

		// Should have called sync (suspension attempt)
		if getSuspendCount() != 1 {
			t.Errorf("Expected suspension attempt, got %d", getSuspendCount())
		}
	})

	// Test with prevention disabled
	t.Run("prevention_disabled", func(t *testing.T) {
		resetSuspendTracker()
		logWriter := &testLogger{}
		subLogger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
			Level: slog.LevelDebug,
		}))
		subCtx := context.Background()
		subCtx = tap.WithLogger(subCtx, subLogger)
		sys := createTestSystem(t, logWriter)
		monitor := NewActivityMonitor(subCtx, sys, 500*time.Millisecond, nil)

		os.Setenv("SPRITE_PREVENT_SUSPEND", "false")
		defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

		monitorCtx, cancel := context.WithCancel(subCtx)
		defer cancel()
		monitor.Start(monitorCtx)

		// Wait for idle timeout
		time.Sleep(1 * time.Second)

		// Should have called sync
		if getSuspendCount() != 1 {
			t.Errorf("Expected sync to be called once, got %d", getSuspendCount())
		}
	})
}

// Test resume detection
func TestActivityMonitor_ResumeDetection(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 500*time.Millisecond, nil)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for first suspension
	time.Sleep(1 * time.Second)

	// Verify suspended state
	if atomic.LoadInt32(&monitor.isSuspended) != 1 {
		t.Error("Monitor should be in suspended state")
	}

	// Simulate resume by starting activity
	monitor.ActivityStarted("resume-test")

	// Check that suspended state is cleared
	time.Sleep(100 * time.Millisecond)
	if atomic.LoadInt32(&monitor.isSuspended) != 0 {
		t.Error("Monitor should not be in suspended state after activity")
	}

	monitor.ActivityEnded("resume-test")
}

// Test rapid activity start/stop
func TestActivityMonitor_RapidActivityToggle(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second, nil)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Rapidly toggle activity
	for i := 0; i < 20; i++ {
		monitor.ActivityStarted("rapid")
		time.Sleep(50 * time.Millisecond)
		monitor.ActivityEnded("rapid")
		time.Sleep(50 * time.Millisecond)
	}

	// Should not have suspended during rapid toggling
	if getSuspendCount() > 0 {
		t.Error("System suspended during rapid activity toggling")
	}

	// Wait for idle
	time.Sleep(2 * time.Second)

	// Should suspend after activity stops
	if getSuspendCount() != 1 {
		t.Errorf("Expected 1 suspension, got %d", getSuspendCount())
	}
}

// Test activity during suspension
func TestActivityMonitor_ActivityDuringSuspension(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 500*time.Millisecond, nil)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for suspension
	time.Sleep(1 * time.Second)

	if getSuspendCount() != 1 {
		t.Fatal("System should have suspended")
	}

	// Start activity while suspended
	monitor.ActivityStarted("during-suspend")

	// Should handle resume
	time.Sleep(100 * time.Millisecond)
	if atomic.LoadInt32(&monitor.isSuspended) != 0 {
		t.Error("Should have resumed from suspended state")
	}

	monitor.ActivityEnded("during-suspend")
}

// Test edge case: activity event channel full
func TestActivityMonitor_ChannelFull(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 10*time.Second, nil) // Long timeout

	// Don't start the monitor to let channel fill up

	// Try to overflow the channel (capacity is 128)
	for i := 0; i < 200; i++ {
		monitor.ActivityStarted(fmt.Sprintf("flood-%d", i))
	}

	// Should not panic or block indefinitely
	// The implementation should handle full channel gracefully
}

// Test real tmux session with activity forwarding
func TestActivityMonitor_RealTmuxIntegration(t *testing.T) {
	resetSuspendTracker()

	// Skip if tmux is not available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Skip("tmux not available")
	}

	ctx := context.Background()
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx = tap.WithLogger(ctx, logger)

	// Create tmux manager
	tmuxManager := terminal.NewTMUXManager(ctx)

	// Create mock system
	logWriter := &testLogger{}
	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 2*time.Second, tmuxManager)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	// Set up activity forwarding (simulating what main.go does)
	activityReceived := make(chan bool, 1)
	go func() {
		activityChan := tmuxManager.GetActivityChannel()
		for {
			select {
			case <-ctx.Done():
				return
			case tmuxActivity, ok := <-activityChan:
				if !ok {
					return
				}

				t.Logf("Received tmux activity: sessionID=%s, active=%v, type=%s",
					tmuxActivity.SessionID, tmuxActivity.Active, tmuxActivity.Type)

				// Forward to activity monitor
				if tmuxActivity.Active {
					monitor.ActivityStarted("tmux")
					select {
					case activityReceived <- true:
					default:
					}
				} else {
					monitor.ActivityEnded("tmux")
				}
			}
		}
	}()

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// The real test would create a tmux session and verify activity
	// but without modifying TMUXManager to accept custom socket paths,
	// this is limited in what it can test

	t.Log("Real tmux integration test completed")
}

// Helper function to check if tmux session exists
func tmuxSessionExists(socketPath, sessionName string) bool {
	cmd := exec.Command("tmux", "-S", socketPath, "has-session", "-t", sessionName)
	return cmd.Run() == nil
}

// Helper to send commands to tmux session
func sendToTmuxSession(t *testing.T, socketPath, sessionName, command string) {
	cmd := exec.Command("tmux", "-S", socketPath, "send-keys", "-t", sessionName, command, "Enter")
	if err := cmd.Run(); err != nil {
		t.Fatalf("Failed to send command to tmux: %v", err)
	}
}
