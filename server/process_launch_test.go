package main

import (
	"log/slog"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"
)

// TestStartProcessWithLaunchScript tests the PID file monitoring with a launch.sh-like script
func TestStartProcessWithLaunchScript(t *testing.T) {
	// Create a temporary directory for test files
	tmpDir := t.TempDir()

	// Create a mock launch.sh script that behaves like the real one
	launchScriptPath := filepath.Join(tmpDir, "launch.sh")
	launchScript := `#!/bin/bash
# Mock launch.sh that simulates the real behavior

# Check for CRUN_PID_FILE environment variable
if [ -n "${CRUN_PID_FILE:-}" ]; then
    echo "launch.sh: Got PID file path: $CRUN_PID_FILE" >&2
    # Simulate crun by writing our PID to the file
    echo $$ > "$CRUN_PID_FILE"
fi

# Simulate running a container by sleeping
exec sleep 2
`
	if err := os.WriteFile(launchScriptPath, []byte(launchScript), 0755); err != nil {
		t.Fatal(err)
	}

	// Create a simple system for testing
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelDebug}))

	sys := &System{
		config: SystemConfig{
			ProcessCommand:    []string{launchScriptPath}, // Just launch.sh with no args
			ProcessWorkingDir: tmpDir,
		},
		logger:         logger,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr:       &systemState{},
		processMu:      sync.Mutex{},
	}

	// Start state manager
	go sys.runStateManager()
	defer close(sys.stopCh)

	// Test that launch.sh is detected and PID file is monitored
	t.Run("LaunchScriptWithPIDFile", func(t *testing.T) {
		start := time.Now()
		err := sys.StartProcess()
		if err != nil {
			t.Fatalf("StartProcess failed: %v", err)
		}
		elapsed := time.Since(start)

		// Should have waited for PID file
		t.Logf("StartProcess took %v", elapsed)

		// Verify process is marked as running
		if !sys.IsProcessRunning() {
			t.Error("Process should be marked as running")
		}

		// Verify CRUN_PID_FILE was set in environment
		pidFileFound := false
		for _, env := range sys.config.ProcessEnvironment {
			if len(env) > 14 && env[:14] == "CRUN_PID_FILE=" {
				pidFileFound = true
				t.Logf("Found PID file env var: %s", env)
				break
			}
		}
		if !pidFileFound {
			t.Error("CRUN_PID_FILE environment variable was not set")
		}

		// Stop the process
		if err := sys.StopProcess(); err != nil {
			t.Errorf("StopProcess failed: %v", err)
		}
	})
}

// TestStartProcessWithLaunchScriptArgs tests that launch.sh with arguments is not treated as crun
func TestStartProcessWithLaunchScriptArgs(t *testing.T) {
	tmpDir := t.TempDir()

	// Create a mock launch.sh script
	launchScriptPath := filepath.Join(tmpDir, "launch.sh")
	launchScript := `#!/bin/bash
echo "launch.sh called with args: $@"
# Should not get CRUN_PID_FILE when called with args
if [ -n "${CRUN_PID_FILE:-}" ]; then
    echo "ERROR: CRUN_PID_FILE should not be set when launch.sh has args" >&2
    exit 1
fi
exit 0
`
	if err := os.WriteFile(launchScriptPath, []byte(launchScript), 0755); err != nil {
		t.Fatal(err)
	}

	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelDebug}))

	sys := &System{
		config: SystemConfig{
			ProcessCommand:    []string{launchScriptPath, "some", "args"}, // launch.sh with args
			ProcessWorkingDir: tmpDir,
		},
		logger:         logger,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr:       &systemState{},
		processMu:      sync.Mutex{},
	}

	go sys.runStateManager()
	defer close(sys.stopCh)

	// Should start immediately without PID file monitoring
	err := sys.StartProcess()
	if err != nil {
		t.Fatalf("StartProcess failed: %v", err)
	}

	// Wait for process to complete
	select {
	case <-sys.processDoneCh:
		// Process completed successfully
	case <-time.After(2 * time.Second):
		t.Error("Process should have completed quickly")
	}
}
