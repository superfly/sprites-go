package tests

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"syscall"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/overlay"
	"github.com/superfly/sprite-env/server/system"
)

// requireDockerTest skips the test if not running in Docker test container
func requireDockerTest(t *testing.T) {
	t.Helper()
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		t.Skip("This test requires Docker test container (run via 'make test')")
	}
}

// SetTestDeadline sets a hard 30-second deadline for the test to prevent hangs
// This should be called at the start of every integration test
func SetTestDeadline(t *testing.T) (context.Context, context.CancelFunc) {
	t.Helper()

	// Default to 30 seconds as requested
	deadline := time.Now().Add(30 * time.Second)

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
				t.Error("TEST DEADLINE EXCEEDED - test took longer than 30 seconds, likely hanging")
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

// VerifyNoLeftoverMounts checks that no test-related storage mounts remain after test cleanup
// This is automatically called by TestSystem's cleanup function.
// Tests should NOT call this directly - it's handled automatically.
func VerifyNoLeftoverMounts(t *testing.T) {
	t.Helper()

	var failures []string

	// Check for mount output
	output, err := exec.Command("mount").Output()
	if err != nil {
		t.Logf("Warning: Could not check mounts: %v", err)
		return
	}
	mountOutput := string(output)

	// Check for /mnt/newroot mount
	if containsStr(mountOutput, " on /mnt/newroot type ") {
		failures = append(failures, "/mnt/newroot is still mounted")
	}

	// Check for /mnt/user-data mount
	if containsStr(mountOutput, " on /mnt/user-data type ") {
		failures = append(failures, "/mnt/user-data is still mounted")
	}

	// Check for any SpriteFS/JuiceFS mounts
	if containsStr(mountOutput, "SpriteFS on") || containsStr(mountOutput, "type fuse.juicefs") {
		failures = append(failures, "JuiceFS/SpriteFS mounts are still present")
	}

	// Check for checkpoint mounts under /.sprite/checkpoints/
	for _, line := range splitLines(mountOutput) {
		if containsStr(line, " on /.sprite/checkpoints/") &&
			!containsStr(line, " on /.sprite/checkpoints type ") { // Allow the base tmpfs mount
			failures = append(failures, "Checkpoint mount still present: "+line)
		}
	}

	// Check for loopback devices
	loopOutput, err := exec.Command("losetup", "-a").Output()
	if err == nil {
		loopList := strings.TrimSpace(string(loopOutput))
		if loopList != "" {
			failures = append(failures, fmt.Sprintf("Loopback devices still attached:\n%s", loopList))
		}
	}

	// Fail the test if any issues found
	if len(failures) > 0 {
		t.Errorf("Storage cleanup verification FAILED - leftover mounts/devices detected:")
		for _, failure := range failures {
			t.Errorf("  - %s", failure)
		}

		// Print full mount output for debugging
		t.Logf("Full mount output:\n%s", mountOutput)
	}
}

// TestConfig creates a minimal test configuration
func TestConfig(testDir string) *system.Config {
	// Configure JuiceFS and overlay for tests to enable checkpoint manager
	juiceBase, _ := os.MkdirTemp("", "sprite-juicefs-*")
	// Create the data directory that JuiceFS will mount to
	os.MkdirAll(filepath.Join(juiceBase, "data"), 0755)
	lowerPath := filepath.Join(testDir, "lower")
	os.MkdirAll(lowerPath, 0755)

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
		OverlayTargetPath:              "/mnt/newroot",
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

	// Add test name to logger context for easier debugging
	// This makes all logs from this system include the test name
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
			// Also run general verification for any other mounts
			VerifyNoLeftoverMounts(t)
		}()
	}

	return sys, cleanup, nil
}

// aggressiveUnmountAll unmounts all mounts that might be using loop devices
// This MUST be called before detaching loop devices
// Returns error if any critical mounts fail to unmount
func aggressiveUnmountAll() error {
	startTime := time.Now()

	// Get all mounts
	output, err := exec.Command("mount").Output()
	if err != nil {
		return nil
	}

	lines := string(output)
	if lines == "" {
		return nil
	}

	// Find all overlay and loop-based mounts that we deliberately created
	// We'll unmount in reverse order (last mounted first)
	var mountsToUnmount []string

	for _, line := range splitLines(lines) {
		if line == "" {
			continue
		}

		// Look for overlay mounts or loop device mounts
		// Format: "overlay on /mnt/newroot type overlay ..."
		// Format: "/dev/loop0 on /mnt/user-data type ext4 ..."
		if containsStr(line, "overlay on") || containsStr(line, "/dev/loop") {
			// Extract mount point (between "on " and " type")
			onIdx := findStr(line, " on ")
			if onIdx == -1 {
				continue
			}
			typeIdx := findStr(line, " type ")
			if typeIdx == -1 {
				continue
			}

			mountPoint := line[onIdx+4 : typeIdx]

			// NEVER unmount the root filesystem - that's the container's root overlay
			if mountPoint == "/" {
				continue
			}

			// Skip system mounts
			if containsStr(mountPoint, "docker-init") {
				continue
			}

			// Only unmount mounts that we deliberately created for the system:
			// 1. Mounts under /mnt/ (like /mnt/newroot, /mnt/user-data)
			// 2. Checkpoint subdirectory mounts (like /.sprite/checkpoints/v1, /.sprite/checkpoints/active)
			//    but NOT the base /.sprite/checkpoints itself (which is now a tmpfs)
			isTestMount := false
			if len(mountPoint) >= 5 && mountPoint[:5] == "/mnt/" {
				// Mounts under /mnt/ are test mounts
				isTestMount = true
			} else if len(mountPoint) > len("/.sprite/checkpoints/") &&
				mountPoint[:len("/.sprite/checkpoints/")] == "/.sprite/checkpoints/" {
				// Subdirectories of /.sprite/checkpoints are checkpoint mounts
				isTestMount = true
			}

			if isTestMount {
				mountsToUnmount = append(mountsToUnmount, mountPoint)
			}
		}
	}

	if len(mountsToUnmount) > 0 {
		fmt.Printf("INFO: Found %d test overlay/loop mounts to clean up: %v\n", len(mountsToUnmount), mountsToUnmount)
	}

	var failedMounts []string

	// Unmount in reverse order
	for i := len(mountsToUnmount) - 1; i >= 0; i-- {
		mountPoint := mountsToUnmount[i]

		// Try force unmount
		_ = exec.Command("umount", "-f", mountPoint).Run()
		time.Sleep(50 * time.Millisecond)

		// Check if still mounted and retry
		if isMounted(mountPoint) {
			fmt.Printf("WARNING: Mount %s still present after first unmount attempt, retrying with force\n", mountPoint)
			_ = exec.Command("umount", "-f", mountPoint).Run()
			time.Sleep(100 * time.Millisecond)

			// Final check
			if isMounted(mountPoint) {
				fmt.Printf("ERROR: Mount %s STILL present after multiple unmount attempts\n", mountPoint)
				failedMounts = append(failedMounts, mountPoint)
			}
		}
	}

	// Wait for unmounts to complete
	time.Sleep(200 * time.Millisecond)

	elapsed := time.Since(startTime)
	if elapsed > 500*time.Millisecond {
		fmt.Printf("WARNING: aggressiveUnmountAll took %v (longer than 500ms)\n", elapsed)
	}

	// Fail fast if we couldn't unmount critical mounts
	if len(failedMounts) > 0 {
		return fmt.Errorf("CRITICAL: Failed to unmount %d mounts: %v - cannot proceed with loopback cleanup", len(failedMounts), failedMounts)
	}

	return nil
}

// aggressiveLoopbackCleanup detaches ALL loopback devices, even orphaned ones
// This MUST be called AFTER aggressiveUnmountAll
func aggressiveLoopbackCleanup() {
	startTime := time.Now()

	// Get list of all loop devices
	output, err := exec.Command("losetup", "-a").Output()
	if err != nil {
		return
	}

	lines := string(output)
	if lines == "" {
		return
	}

	loopDevices := []string{}

	// Parse each line to extract loop device names
	// Format: /dev/loop0: [0052]:6 (/path/to/file)
	for _, line := range splitLines(lines) {
		if line == "" {
			continue
		}

		// Extract device name (everything before the colon)
		colonIdx := findChar(line, ':')
		if colonIdx == -1 {
			continue
		}

		loopDev := line[:colonIdx]
		loopDevices = append(loopDevices, loopDev)
	}

	if len(loopDevices) > 0 {
		fmt.Printf("WARNING: Found %d loopback devices to clean up: %v\n", len(loopDevices), loopDevices)
	}

	// Detach each device
	for _, loopDev := range loopDevices {
		// Try to detach this loop device
		// First try normal detach
		if err := exec.Command("losetup", "-d", loopDev).Run(); err != nil {
			fmt.Printf("WARNING: Failed to detach %s on first attempt, retrying after delay\n", loopDev)
			// If that fails, the device might still be busy
			// Wait a moment and try again
			time.Sleep(100 * time.Millisecond)
			if err := exec.Command("losetup", "-d", loopDev).Run(); err != nil {
				fmt.Printf("ERROR: Failed to detach %s after retry: %v\n", loopDev, err)
			}
		}

		// Give it a moment
		time.Sleep(50 * time.Millisecond)
	}

	// Wait a bit for all detaches to complete
	time.Sleep(200 * time.Millisecond)

	// Verify all devices were detached
	if output, err := exec.Command("losetup", "-a").Output(); err == nil {
		remaining := string(output)
		if remaining != "" {
			fmt.Printf("ERROR: Some loopback devices still attached after cleanup:\n%s\n", remaining)
		}
	}

	elapsed := time.Since(startTime)
	if elapsed > 500*time.Millisecond {
		fmt.Printf("WARNING: aggressiveLoopbackCleanup took %v (longer than 500ms)\n", elapsed)
	}
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

// RegisterSystemCleanup registers a cleanup handler to ensure the system is properly shut down
// This should be called immediately after creating a system instance in tests
func RegisterSystemCleanup(t *testing.T, sys *system.System) {
	t.Helper()
	t.Cleanup(func() {
		// Always try to shutdown, even if test failed or system already stopped
		// Use massive timeout for thorough cleanup
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
		defer cancel()

		t.Logf("Test cleanup: shutting down system")
		if err := sys.Shutdown(ctx); err != nil {
			t.Logf("Cleanup shutdown error (may be expected if already shut down): %v", err)
		}

		// AGGRESSIVE cleanup of any leftover resources

		// Kill any remaining processes
		if sys.IsProcessRunning() {
			pid := sys.ProcessPID()
			if pid > 0 {
				t.Logf("Cleanup: Process still running (PID %d), force killing", pid)
				_ = syscall.Kill(-pid, syscall.SIGKILL)
				time.Sleep(500 * time.Millisecond)
			}
		}

		// Aggressively unmount overlayfs
		if sys.OverlayManager != nil {
			if sys.OverlayManager.IsOverlayFSMounted() {
				t.Logf("Cleanup: OverlayFS still mounted, forcing unmount")
				cleanupCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				_ = sys.OverlayManager.Unmount(cleanupCtx)
				cancel()
			}
		}

		// Unmount ALL test mounts before detaching loop devices
		t.Logf("Cleanup: Unmounting all test overlay and loop-based mounts")
		if err := aggressiveUnmountAll(); err != nil {
			t.Logf("Cleanup ERROR: %v", err)
			t.Logf("Cleanup: Cannot proceed with loopback cleanup - mounts still busy")
			return
		}

		// Aggressively clean up ALL loopback devices
		t.Logf("Cleanup: Detaching all loopback devices")
		aggressiveLoopbackCleanup()

		// Verify loopbacks are gone
		if output, err := exec.Command("losetup", "-a").Output(); err == nil {
			loopList := string(output)
			if loopList != "" {
				t.Logf("Cleanup: Loopback devices still present after cleanup, trying again:\n%s", loopList)
				if err := aggressiveUnmountAll(); err != nil {
					t.Logf("Cleanup ERROR: %v", err)
				} else {
					time.Sleep(500 * time.Millisecond)
					aggressiveLoopbackCleanup()
				}
			}
		}

		// Aggressively unmount JuiceFS
		if sys.JuiceFS != nil {
			if sys.JuiceFS.IsMounted() {
				t.Logf("Cleanup: JuiceFS still mounted, forcing stop")
				cleanupCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				stopErr := sys.JuiceFS.Stop(cleanupCtx)
				cancel()

				// If still mounted, force unmount
				if stopErr != nil && sys.JuiceFS.IsMounted() {
					t.Logf("Cleanup: JuiceFS STILL mounted after stop, trying force unmount")
					_ = exec.Command("sh", "-c", "umount -f /tmp/sprite-juicefs-*/data 2>/dev/null || true").Run()
					time.Sleep(500 * time.Millisecond)

					// Last resort: kill juicefs processes
					if sys.JuiceFS.IsMounted() {
						_ = exec.Command("pkill", "-9", "juicefs").Run()
						time.Sleep(200 * time.Millisecond)
						_ = exec.Command("sh", "-c", "umount -f /tmp/sprite-juicefs-*/data 2>/dev/null || true").Run()
					}
				}
			}
		}

		t.Logf("Test cleanup: complete")
	})
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
	t.Cleanup(func() {
		os.Unsetenv("SPRITE_WRITE_DIR")
	})

	return testDir
}

// StartSystemWithTimeout starts a system with a timeout for boot
func StartSystemWithTimeout(t *testing.T, sys *system.System, timeout time.Duration) {
	t.Helper()

	done := make(chan error, 1)
	go func() {
		done <- sys.Start()
	}()

	select {
	case err := <-done:
		if err != nil {
			// Print diagnostics on failure
			t.Log("=== System start failed, dumping diagnostics ===")
			if mountCmd := exec.Command("mount"); mountCmd != nil {
				if output, mountErr := mountCmd.Output(); mountErr == nil {
					t.Logf("mount output:\n%s", string(output))
				}
			}
			if losetupCmd := exec.Command("losetup", "-a"); losetupCmd != nil {
				if output, losetupErr := losetupCmd.Output(); losetupErr == nil {
					t.Logf("losetup -a output:\n%s", string(output))
				}
			}
			t.Log("=== End diagnostics ===")
			t.Fatalf("Failed to start system: %v", err)
		}
	case <-time.After(timeout):
		t.Fatal("Timeout waiting for system to start")
	}
}

// ShutdownSystemWithTimeout shuts down a system with a timeout
func ShutdownSystemWithTimeout(t *testing.T, sys *system.System, timeout time.Duration) {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	if err := sys.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown error: %v", err)
	}
}

// VerifySystemRunning checks that all major subsystems are running
func VerifySystemRunning(t *testing.T, sys *system.System) {
	t.Helper()

	// Check process is running
	if !sys.IsProcessRunning() {
		t.Error("Process should be running")
	}

	// Check API server is available
	if sys.APIServer == nil {
		t.Error("API server should be initialized")
	}

	// Check socket server is available
	if sys.SocketServer == nil {
		t.Error("Socket server should be initialized")
	}
}

// VerifySystemStopped checks that all subsystems are stopped
func VerifySystemStopped(t *testing.T, sys *system.System) {
	t.Helper()

	// Process should not be running
	if sys.IsProcessRunning() {
		t.Error("Process should not be running")
	}
}

// VerifyComponentCleanup runs cleanup verifiers for all system components
// This validates that all external resources have been properly cleaned up
func VerifyComponentCleanup(t *testing.T, sys *system.System) {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

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

// WaitForCondition waits for a condition to be true within a timeout
func WaitForCondition(t *testing.T, timeout, interval time.Duration, condition func() bool, description string) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	ticker := time.NewTicker(interval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			t.Fatalf("Timeout waiting for %s: %v", description, ctx.Err())
		case <-ticker.C:
			if condition() {
				return
			}
		}
	}
}
