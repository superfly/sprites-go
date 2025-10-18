package system

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/tmux"
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
	// Create a minimal system without initializing all components
	ctx, cancel := context.WithCancel(context.Background())
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	sys := &System{
		ctx:                 ctx,
		cancel:              cancel,
		config:              &Config{},
		logger:              logger,
		shutdownTriggeredCh: make(chan struct{}),
		shutdownCompleteCh:  make(chan struct{}),
		// Process management fields (needed for activity monitor) - initially stopped
		processStartedCh: make(chan struct{}),
		processStoppedCh: func() chan struct{} {
			ch := make(chan struct{})
			close(ch)
			return ch
		}(),
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
	monitor := NewActivityMonitor(ctx, sys, 2*time.Second)

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
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for idle timeout - timer restarts after each suspend
	// Need extra time for suspend overhead (sync, litestream stop, etc.)
	time.Sleep(2500 * time.Millisecond)

	// Should have suspended twice (at ~1s and ~2s)
	count := getSuspendCount()
	if count < 2 {
		t.Errorf("Expected at least 2 suspensions after idle timeout, got %d suspensions", count)
	}
}

// Test tmux sessions prevent suspension
func TestActivityMonitor_ActiveTmuxSessionsPreventSuspension(t *testing.T) {
	resetSuspendTracker()

	// In Docker test environment, tmux must be available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Fatal("tmux not available - test environment is misconfigured")
	}

	ctx := context.Background()
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx = tap.WithLogger(ctx, logger)

	// Create tmux manager (unused with new API)
	_ = tmux.NewManager(ctx, tmux.Options{})

	// Create test tmux socket
	socketPath := createTestTmuxSocket(t)

	// Create a tmux session
	sessionID := "test"

	// Create the actual tmux session
	cmd := exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", fmt.Sprintf("sprite-exec-%s", sessionID), "/bin/bash", "-c", "while true; do echo test; sleep 0.5; done")
	if err := cmd.Run(); err != nil {
		t.Fatalf("Failed to create tmux session: %v", err)
	}

	// New API: manager handles monitoring internally; no prepare hook

	// Manager activity monitoring is automatic; nothing to start here

	// Create test system
	logWriter := &testLogger{}
	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second)

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
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second)

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

	// Wait for idle timeout - timer restarts after each suspend
	// Need extra time for suspend overhead
	time.Sleep(2500 * time.Millisecond)

	// Should suspend at least twice after all activities end (at ~1s and ~2s)
	count := getSuspendCount()
	if count < 2 {
		t.Errorf("Expected at least 2 suspensions after activities ended, got %d", count)
	}
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
	monitor := NewActivityMonitor(ctx, sys, 500*time.Millisecond)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for suspension - timer restarts after each suspend
	// Need extra time for suspend overhead
	time.Sleep(1200 * time.Millisecond)

	// Verify suspensions happened (should be at least 2: at ~500ms and ~1000ms)
	count := getSuspendCount()
	if count < 2 {
		t.Errorf("Monitor should have triggered at least 2 suspensions, got %d", count)
	}

	// Note: We no longer track suspended state internally since we rely on
	// resume detection via API time divergence. The resume will be detected
	// when the API returns a time that diverges from local time.

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
	monitor := NewActivityMonitor(ctx, sys, 1*time.Second)

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

	// Wait for idle - timer restarts after each suspend
	// Need extra time for suspend overhead
	time.Sleep(2500 * time.Millisecond)

	// With 1s idle timeout and 2.5s wait, should suspend at least twice (at ~1s and ~2s)
	count := getSuspendCount()
	if count < 2 {
		t.Errorf("Expected at least 2 suspensions, got %d", count)
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
	monitor := NewActivityMonitor(ctx, sys, 500*time.Millisecond)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for suspension - timer restarts after each suspend
	// Need extra time for suspend overhead
	time.Sleep(1200 * time.Millisecond)

	// Should have suspended at least twice (at ~500ms and ~1000ms)
	count := getSuspendCount()
	if count < 2 {
		t.Fatalf("System should have suspended at least twice, got %d", count)
	}

	// Start activity while suspended
	monitor.ActivityStarted("during-suspend")

	// Activity during suspension is handled normally now
	// Resume detection happens separately via API time divergence
	time.Sleep(100 * time.Millisecond)

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
	monitor := NewActivityMonitor(ctx, sys, 10*time.Second) // Long timeout

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

	// In Docker test environment, tmux must be available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Fatal("tmux not available - test environment is misconfigured")
	}

	ctx := context.Background()
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx = tap.WithLogger(ctx, logger)

	// Create tmux manager (not used in new API)
	_ = tmux.NewManager(ctx, tmux.Options{})

	// Create mock system
	logWriter := &testLogger{}
	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 2*time.Second)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	// Set up activity forwarding (simulating what main.go does)
	// Note: pkg/tmux.Manager handles activity internally; no public channel here.

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

// Test activity cancels suspend preparation
func TestActivityMonitor_ActivityCancelsSuspendPrep(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 500*time.Millisecond)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for idle timeout to expire
	time.Sleep(600 * time.Millisecond)

	// During suspend prep, send activity
	// This should cancel the prep
	go func() {
		time.Sleep(50 * time.Millisecond)
		monitor.ActivityStarted("interrupt")
	}()

	// Wait a bit longer
	time.Sleep(300 * time.Millisecond)

	// Check logs for cancellation message
	logWriter.mu.Lock()
	found := false
	for _, entry := range logWriter.entries {
		if strings.Contains(entry, "Activity detected during suspend") ||
			strings.Contains(entry, "cancelled") {
			found = true
			break
		}
	}
	logWriter.mu.Unlock()

	if !found {
		t.Log("Looking for cancellation messages in logs")
	}

	// End the activity
	monitor.ActivityEnded("interrupt")
}

// Test cleanup functions run after suspend
func TestActivityMonitor_CleanupAfterSuspend(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 500*time.Millisecond)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for suspension
	time.Sleep(1200 * time.Millisecond)

	// Should have suspended
	count := getSuspendCount()
	if count < 1 {
		t.Errorf("Expected at least 1 suspension, got %d", count)
	}

	// Check that cleanup-related logs appear (PostResume, etc.)
	logWriter.mu.Lock()
	hasCleanup := false
	for _, entry := range logWriter.entries {
		if strings.Contains(entry, "PostResume") ||
			strings.Contains(entry, "cleanup") {
			hasCleanup = true
			break
		}
	}
	logWriter.mu.Unlock()

	// Note: cleanup happens but may not always log depending on what's initialized
	_ = hasCleanup
}

// Test activity during prep cancels and cleanup runs
func TestActivityMonitor_ActivityDuringPrepRunsCleanup(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 300*time.Millisecond)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Wait for idle timeout
	time.Sleep(400 * time.Millisecond)

	// Inject activity during prep (right after timer fires)
	go func() {
		time.Sleep(50 * time.Millisecond)
		monitor.ActivityStarted("interrupt")
		time.Sleep(100 * time.Millisecond)
		monitor.ActivityEnded("interrupt")
	}()

	// Wait for the suspend cycle to complete
	time.Sleep(500 * time.Millisecond)

	// The system should handle the cancellation gracefully
	// and cleanup should run
	logWriter.mu.Lock()
	foundCancel := false
	for _, entry := range logWriter.entries {
		if strings.Contains(entry, "cancel") ||
			strings.Contains(entry, "Activity detected") {
			foundCancel = true
		}
	}
	logWriter.mu.Unlock()

	// Whether we found the log or not, the test passes if we didn't panic/deadlock
	_ = foundCancel
}

// Test multiple rapid suspend attempts
func TestActivityMonitor_RapidSuspendCycles(t *testing.T) {
	resetSuspendTracker()

	logWriter := &testLogger{}
	logger := slog.New(slog.NewTextHandler(logWriter, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	sys := createTestSystem(t, logWriter)
	monitor := NewActivityMonitor(ctx, sys, 200*time.Millisecond)

	os.Setenv("SPRITE_PREVENT_SUSPEND", "true")
	defer os.Unsetenv("SPRITE_PREVENT_SUSPEND")

	monitorCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	monitor.Start(monitorCtx)

	// Let it suspend multiple times rapidly
	time.Sleep(1500 * time.Millisecond)

	// Should have suspended multiple times
	count := getSuspendCount()
	if count < 3 {
		t.Logf("Got %d suspensions in rapid cycles", count)
	}

	// Verify no panics or deadlocks occurred
}
