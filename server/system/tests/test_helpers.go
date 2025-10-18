package tests

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/overlay"
	"github.com/superfly/sprite-env/server/system"
)

// requireDockerTest fails the test if not running in Docker test container
func requireDockerTest(t *testing.T) {
	t.Helper()
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		t.Fatal("This test must run in the Docker test environment (SPRITE_TEST_DOCKER=1)")
	}
}

// SetTestDeadline sets a hard 30-second deadline for the test to prevent hangs
// This should be called at the start of every integration test
func SetTestDeadline(t *testing.T) (context.Context, context.CancelFunc) {
	return SetTestDeadlineWithTimeout(t, 30*time.Second)
}

// SetTestDeadlineWithTimeout sets a custom deadline for the test to prevent hangs
// This should be called at the start of every integration test that needs a custom timeout
func SetTestDeadlineWithTimeout(t *testing.T, timeout time.Duration) (context.Context, context.CancelFunc) {
	t.Helper()

	// Use the provided timeout
	deadline := time.Now().Add(timeout)

	// If test already has a deadline set via -timeout flag, use that instead
	if d, ok := t.Deadline(); ok && d.Before(deadline) {
		deadline = d
	}

	ctx, cancel := context.WithDeadline(context.Background(), deadline)

	// Start a goroutine to fail the test if deadline is reached
	done := make(chan struct{})
	go func() {
		select {
		case <-ctx.Done():
			if ctx.Err() == context.DeadlineExceeded {
				t.Errorf("TEST DEADLINE EXCEEDED - test took longer than %v, likely hanging", timeout)
			}
		case <-done:
			// Test completed normally
		}
	}()

	// Return a cancel that closes done channel
	originalCancel := cancel
	newCancel := func() {
		close(done)
		originalCancel()
	}

	return ctx, newCancel
}

// TestConfig creates a minimal test configuration
func TestConfig(testDir string) *system.Config {
	// Configure JuiceFS and overlay for tests to enable checkpoint manager
	juiceBase, _ := os.MkdirTemp("", "sprite-juicefs-*")
	// Create the data directory that JuiceFS will mount to
	os.MkdirAll(filepath.Join(juiceBase, "data"), 0755)
	lowerPath := filepath.Join(testDir, "lower")
	os.MkdirAll(lowerPath, 0755)

	// Create unique mount paths within testDir to allow parallel test execution
	// This prevents tests from conflicting on shared mount points
	overlayTargetPath := filepath.Join(testDir, "mnt", "newroot")
	checkpointMountPath := filepath.Join(testDir, "sprite", "checkpoints")
	os.MkdirAll(overlayTargetPath, 0755)
	os.MkdirAll(checkpointMountPath, 0755)

	return &system.Config{
		ProcessCommand:                 []string{"/bin/sh", "-c", "sleep 3600"},
		ProcessWorkingDir:              testDir,
		APIToken:                       "test-token-123",
		APIListenAddr:                  "127.0.0.1:0", // Random port
		ProcessGracefulShutdownTimeout: 5 * time.Second,
		WriteDir:                       testDir,
		LogDir:                         filepath.Join(testDir, "logs"),
		LogLevel:                       slog.LevelError, // Suppress INFO/DEBUG/WARN logs in tests
		LogJSON:                        false,
		JuiceFSDataPath:                juiceBase,
		JuiceFSLocalMode:               true,
		OverlayEnabled:                 true,
		OverlayLowerPaths:              []string{lowerPath},
		OverlayTargetPath:              overlayTargetPath,
		CheckpointMountPath:            checkpointMountPath,
	}
}

// TestSystem creates a new system and returns a cleanup function
// Usage: sys, cleanup, err := TestSystem(t, config); defer cleanup()
// Cleanup automatically calls Shutdown() and verifies no leftover mounts/devices
func TestSystem(t *testing.T, config *system.Config) (*system.System, func(), error) {
	t.Helper()

	// ALWAYS require running in Docker test container
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		return nil, func() {}, fmt.Errorf("FATAL: System tests MUST run in Docker container. Use 'make test' to run tests properly. Direct test execution is not supported")
	}

	sys, err := system.New(config)
	if err != nil {
		return nil, func() {}, err
	}

	// Attach test name to logs (uses system default log level)
	sys.WithLogger(sys.Logger().With("test", t.Name()))

	cleanup := func() {
		// Always try to stop the system, even if test already called Shutdown
		// Stop() is safe to call multiple times (returns nil if already stopped)
		// If it returns an error, that's a real problem that should fail the test
		if err := sys.Stop(); err != nil {
			t.Fatalf("Cleanup: Stop() failed: %v", err)
		}

		// Run cleanup verifiers to detect resource leaks
		// Verifiers will fail the test if resources are not cleaned up properly
		defer func() {
			// Verify all components cleaned up properly
			VerifyComponentCleanup(t, sys)

			// Use package-specific helpers for detailed verification
			if sys.OverlayManager != nil {
				overlay.VerifyNoTestOverlays(t, sys.OverlayManager)
			}
			if sys.JuiceFS != nil {
				juicefs.VerifyNoTestJuiceFS(t, sys.JuiceFS)
			}
		}()
	}

	return sys, cleanup, nil
}

// splitLines splits a string into lines
func splitLines(s string) []string {
	var lines []string
	start := 0
	for i := 0; i < len(s); i++ {
		if s[i] == '\n' {
			lines = append(lines, s[start:i])
			start = i + 1
		}
	}
	if start < len(s) {
		lines = append(lines, s[start:])
	}
	return lines
}

// findChar finds the first occurrence of a character in a string
func findChar(s string, c byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			return i
		}
	}
	return -1
}

// findStr finds the first occurrence of a substring in a string
func findStr(s, substr string) int {
	if len(substr) == 0 {
		return 0
	}
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return i
		}
	}
	return -1
}

// containsStr checks if a string contains a substring
func containsStr(s, substr string) bool {
	return findStr(s, substr) != -1
}

// isMounted checks if a path is currently mounted
func isMounted(path string) bool {
	output, err := exec.Command("mount").Output()
	if err != nil {
		return false
	}
	return containsStr(string(output), " on "+path+" type ")
}

// TestConfigWithLogLevel creates a test configuration with custom log level
func TestConfigWithLogLevel(testDir string, logLevel slog.Level) *system.Config {
	config := TestConfig(testDir)
	config.LogLevel = logLevel
	return config
}

// VerboseTestConfig creates a test configuration with debug logging enabled
func VerboseTestConfig(testDir string) *system.Config {
	config := TestConfig(testDir)
	config.LogLevel = slog.LevelDebug
	return config
}

// CreateTestScript creates a test script that handles signals properly
func CreateTestScript(t *testing.T, dir string, name string) string {
	t.Helper()

	scriptPath := filepath.Join(dir, name)
	scriptContent := `#!/bin/bash
echo "Test process starting (PID $$)"
trap "echo 'Test process received SIGTERM'; exit 0" SIGTERM
while true; do
	sleep 1
done
`
	if err := os.WriteFile(scriptPath, []byte(scriptContent), 0755); err != nil {
		t.Fatalf("Failed to create test script: %v", err)
	}
	return scriptPath
}

// CreateCrashScript creates a test script that exits with an error
func CreateCrashScript(t *testing.T, dir string, name string) string {
	t.Helper()

	scriptPath := filepath.Join(dir, name)
	scriptContent := `#!/bin/bash
echo "Process that crashes on SIGTERM (PID $$)"
trap "echo 'Crashing!'; exit 42" SIGTERM
while true; do
	sleep 1
done
`
	if err := os.WriteFile(scriptPath, []byte(scriptContent), 0755); err != nil {
		t.Fatalf("Failed to create crash script: %v", err)
	}
	return scriptPath
}

// SetupTestPorts creates test configuration with specific ports
func SetupTestPorts(t *testing.T, config *system.Config) {
	t.Helper()
	config.APIListenAddr = fmt.Sprintf("127.0.0.1:%s", GetFreePort(t))
}

// GetFreePort finds an available port
func GetFreePort(t *testing.T) string {
	t.Helper()

	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer listener.Close()

	_, port, err := net.SplitHostPort(listener.Addr().String())
	if err != nil {
		t.Fatal(err)
	}

	return port
}

// SetupTestEnvironment creates a temporary directory and sets up basic environment variables
func SetupTestEnvironment(t *testing.T) string {
	t.Helper()
	testDir := t.TempDir()

	// Create required subdirectories
	if err := os.MkdirAll(filepath.Join(testDir, "logs"), 0755); err != nil {
		t.Fatalf("Failed to create logs directory: %v", err)
	}

	// Set required environment variables
	os.Setenv("SPRITE_WRITE_DIR", testDir)
	os.Setenv("HOST_ID", fmt.Sprintf("test-host-%s", t.Name()))
	t.Cleanup(func() {
		os.Unsetenv("SPRITE_WRITE_DIR")
		os.Unsetenv("HOST_ID")
	})

	return testDir
}

// VerifyComponentCleanup runs cleanup verifiers for all system components
// This validates that all external resources have been properly cleaned up
func VerifyComponentCleanup(t *testing.T, sys *system.System) {
	t.Helper()

	ctx := t.Context()

	// Track failures
	var failures []string

	// Verify DBManager cleanup (coordinator - checks sub-components)
	if sys.DBManager != nil {
		// DBManager is a coordinator with no direct resources
		// Verify its sub-components instead
		if leaser := sys.DBManager.GetLeaser(); leaser != nil {
			for i, verify := range leaser.CleanupVerifiers() {
				if err := verify(ctx); err != nil {
					failures = append(failures, fmt.Sprintf("DBManager.Leaser cleanup verifier %d failed: %v", i, err))
				}
			}
		}
		// Note: Litestream verifiers would go here when implemented
	}

	// Verify JuiceFS cleanup
	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(ctx); err != nil {
				failures = append(failures, fmt.Sprintf("JuiceFS cleanup verifier %d failed: %v", i, err))
			}
		}
	}

	// Verify OverlayManager cleanup
	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(ctx); err != nil {
				failures = append(failures, fmt.Sprintf("OverlayManager cleanup verifier %d failed: %v", i, err))
			}
		}
	}

	// Verify ServicesManager cleanup
	if sys.ServicesManager != nil {
		for i, verify := range sys.ServicesManager.CleanupVerifiers() {
			if err := verify(ctx); err != nil {
				failures = append(failures, fmt.Sprintf("ServicesManager cleanup verifier %d failed: %v", i, err))
			}
		}
	}

	// Report all failures and FAIL the test immediately
	// This prevents subsequent tests from inheriting leaked resources
	if len(failures) > 0 {
		t.Errorf("Component cleanup verification FAILED:")
		for _, failure := range failures {
			t.Errorf("  - %s", failure)
		}
		t.Fatalf("Test failed cleanup verification - %d resource(s) leaked", len(failures))
	}
}
