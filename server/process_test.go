package main

import (
	"log/slog"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"
)

// TestStartProcessWithPIDFile tests the PID file monitoring functionality
func TestStartProcessWithPIDFile(t *testing.T) {
	// Create a temporary directory for test files
	tmpDir := t.TempDir()

	// Create a mock crun script
	mockCrunPath := filepath.Join(tmpDir, "mock-crun")
	mockCrunScript := `#!/bin/bash
# Mock crun script that simulates crun behavior

PID_FILE=""
ARGS=()

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --pid-file)
            PID_FILE="$2"
            shift 2
            ;;
        run)
            shift
            # Get remaining args after "run"
            ARGS=("$@")
            break
            ;;
        *)
            shift
            ;;
    esac
done

# Simulate crun starting a container
if [ -n "$PID_FILE" ]; then
    # Write our PID to the file (simulating container PID)
    echo $$ > "$PID_FILE"
fi

# Execute a simple command that runs for a bit
exec sleep 2
`
	if err := os.WriteFile(mockCrunPath, []byte(mockCrunScript), 0755); err != nil {
		t.Fatal(err)
	}

	// Create a simple system for testing
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelDebug}))

	sys := &System{
		config: SystemConfig{
			ProcessCommand:    []string{mockCrunPath, "run", "app"},
			ProcessWorkingDir: tmpDir, // Use temp dir as working directory
		},
		logger:         logger,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr:       &systemState{},
		processMu:      sync.Mutex{}, // Initialize mutex
	}

	// Start state manager
	go sys.runStateManager()
	defer close(sys.stopCh)

	// Test 1: Successful PID file creation
	t.Run("SuccessfulPIDFile", func(t *testing.T) {
		err := sys.StartProcess()
		if err != nil {
			t.Fatalf("StartProcess failed: %v", err)
		}

		// Verify process is marked as running
		if !sys.IsProcessRunning() {
			t.Error("Process should be marked as running")
		}

		// Stop the process
		if err := sys.StopProcess(); err != nil {
			t.Errorf("StopProcess failed: %v", err)
		}
	})

	// Test 2: Process exits before PID file is written
	t.Run("ProcessExitsEarly", func(t *testing.T) {
		// Create a script that exits immediately (name it exactly "crun" to trigger PID file logic)
		mockFailScript := filepath.Join(tmpDir, "crun")
		failScript := `#!/bin/bash
# Parse --pid-file argument but exit before writing it
exit 1
`
		if err := os.WriteFile(mockFailScript, []byte(failScript), 0755); err != nil {
			t.Fatal(err)
		}

		// Create a new system for this test
		sys2 := &System{
			config: SystemConfig{
				ProcessCommand:    []string{mockFailScript, "run", "app"},
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
		go sys2.runStateManager()
		defer close(sys2.stopCh)

		err := sys2.StartProcess()
		if err == nil {
			t.Fatal("Expected StartProcess to fail when process exits early")
		}
		if err.Error() != "process exited before initialization" {
			t.Errorf("Unexpected error: %v", err)
		}
	})

	// Test 3: PID file write delay
	t.Run("DelayedPIDFile", func(t *testing.T) {
		// Create a script that delays writing the PID file (use subdirectory to avoid conflict)
		delayDir := filepath.Join(tmpDir, "delay")
		os.Mkdir(delayDir, 0755)
		mockDelayScript := filepath.Join(delayDir, "crun")
		delayScript := `#!/bin/bash
PID_FILE=""
while [[ $# -gt 0 ]]; do
    case $1 in
        --pid-file)
            PID_FILE="$2"
            shift 2
            ;;
        *)
            shift
            ;;
    esac
done

# Delay before writing PID file
sleep 0.5

if [ -n "$PID_FILE" ]; then
    echo $$ > "$PID_FILE"
fi

# Keep running
sleep 2
`
		if err := os.WriteFile(mockDelayScript, []byte(delayScript), 0755); err != nil {
			t.Fatal(err)
		}

		// Create a new system for this test
		sys3 := &System{
			config: SystemConfig{
				ProcessCommand:    []string{mockDelayScript, "run", "app"},
				ProcessWorkingDir: delayDir,
			},
			logger:         logger,
			processDoneCh:  make(chan error, 1),
			processReadyCh: make(chan struct{}),
			stateCh:        make(chan stateOp),
			stopCh:         make(chan struct{}),
			stateMgr:       &systemState{},
			processMu:      sync.Mutex{},
		}
		go sys3.runStateManager()
		defer close(sys3.stopCh)

		start := time.Now()
		err := sys3.StartProcess()
		elapsed := time.Since(start)

		if err != nil {
			t.Fatalf("StartProcess failed: %v", err)
		}

		// Should have waited at least 500ms for the PID file
		if elapsed < 500*time.Millisecond {
			t.Errorf("StartProcess returned too quickly: %v", elapsed)
		}

		// Stop the process
		sys3.StopProcess()
	})
}

// TestStartProcessWithoutCrun tests that non-crun processes work normally
func TestStartProcessWithoutCrun(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelDebug}))

	sys := &System{
		config: SystemConfig{
			ProcessCommand:    []string{"/bin/sh", "-c", "echo hello"},
			ProcessWorkingDir: t.TempDir(),
		},
		logger:         logger,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr:       &systemState{},
		processMu:      sync.Mutex{}, // Initialize mutex
	}

	// Start state manager
	go sys.runStateManager()
	defer close(sys.stopCh)

	err := sys.StartProcess()
	if err != nil {
		t.Fatalf("StartProcess failed: %v", err)
	}

	// Should complete quickly without waiting for PID file
	select {
	case <-sys.processDoneCh:
		// Process completed as expected
	case <-time.After(1 * time.Second):
		t.Error("Process should have completed quickly")
	}
}
