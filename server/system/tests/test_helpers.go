package tests

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"syscall"
	"testing"
	"time"

	"github.com/superfly/sprite-env/server/system"
)

// requireDockerTest skips the test if not running in Docker test container
func requireDockerTest(t *testing.T) {
	t.Helper()
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		t.Skip("This test requires Docker test container (run via 'make test')")
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
// Usage: sys, cleanup, err := TestSystem(config); defer cleanup()
func TestSystem(config *system.Config) (*system.System, func(), error) {
	// ALWAYS require running in Docker test container
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		return nil, func() {}, fmt.Errorf("FATAL: System tests MUST run in Docker container. Use 'make test' to run tests properly. Direct test execution is not supported")
	}

	sys, err := system.New(config)
	if err != nil {
		return nil, func() {}, err
	}

	cleanup := func() {
		cleanupStart := time.Now()

		// Give ourselves a massive timeout for aggressive cleanup
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
		defer cancel()

		// PHASE 1: AGGRESSIVELY KILL THE PROCESS
		// Kill the process and verify it's actually dead
		if sys.IsProcessRunning() {
			pid := sys.ProcessPID()
			if pid > 0 {
				phaseStart := time.Now()
				fmt.Printf("WARNING: Process still running (PID %d), aggressively killing\n", pid)

				// Send SIGKILL to entire process group
				_ = syscall.Kill(-pid, syscall.SIGKILL)

				// Wait up to 10 seconds for process to die, checking repeatedly
				deadline := time.Now().Add(10 * time.Second)
				retries := 0
				for time.Now().Before(deadline) {
					if !sys.IsProcessRunning() {
						break
					}
					time.Sleep(100 * time.Millisecond)
					retries++
					// Try killing again in case it didn't work the first time
					_ = syscall.Kill(-pid, syscall.SIGKILL)
				}

				if retries > 0 {
					fmt.Printf("WARNING: Had to retry SIGKILL %d times for PID %d\n", retries, pid)
				}

				// Final verification
				if sys.IsProcessRunning() {
					fmt.Printf("ERROR: Process STILL running after multiple SIGKILL attempts, trying direct PID kill\n")
					// Last ditch effort: kill by PID directly (not just process group)
					_ = syscall.Kill(pid, syscall.SIGKILL)
					time.Sleep(500 * time.Millisecond)

					if sys.IsProcessRunning() {
						fmt.Printf("CRITICAL: Process STILL running after all kill attempts\n")
					}
				}

				elapsed := time.Since(phaseStart)
				if elapsed > time.Second {
					fmt.Printf("WARNING: Process kill took %v\n", elapsed)
				}
			}
		}

		// Stop services manager
		if sys.ServicesManager != nil {
			_ = sys.ServicesManager.StopForUnmount()
		}

		// PHASE 2: AGGRESSIVELY UNMOUNT OVERLAYFS AND ALL MOUNTS
		// We must unmount everything BEFORE detaching loop devices
		phaseStart := time.Now()

		// Try normal overlay unmount first
		if sys.OverlayManager != nil {
			_ = sys.OverlayManager.Unmount(ctx)
		}

		// Now unmount ANY remaining mounts that might be using loop devices
		// This is critical - we need to unmount everything before detaching loops
		fmt.Printf("INFO: Running aggressive unmount of all overlay/loop mounts\n")
		aggressiveUnmountAll()

		elapsed := time.Since(phaseStart)
		if elapsed > 2*time.Second {
			fmt.Printf("WARNING: Unmount phase took %v\n", elapsed)
		}

		// PHASE 3: AGGRESSIVELY CLEAN UP ALL LOOPBACK DEVICES
		// Now that everything is unmounted, detach ALL loop devices
		phaseStart = time.Now()
		fmt.Printf("INFO: Running aggressive loopback device cleanup\n")
		aggressiveLoopbackCleanup()

		elapsed = time.Since(phaseStart)
		if elapsed > 2*time.Second {
			fmt.Printf("WARNING: Loopback cleanup phase took %v\n", elapsed)
		}

		// PHASE 4: Verify all loopback devices are gone
		// Check that no test-related loop devices remain
		if output, err := exec.Command("losetup", "-a").Output(); err == nil {
			loopList := string(output)
			if loopList != "" {
				fmt.Printf("WARNING: Loopback devices still present after cleanup, running second round\n")
				// Try unmounting and cleanup again
				aggressiveUnmountAll()
				time.Sleep(500 * time.Millisecond)
				aggressiveLoopbackCleanup()

				// Final check
				if output, err := exec.Command("losetup", "-a").Output(); err == nil && string(output) != "" {
					fmt.Printf("ERROR: Loopback devices STILL present after second cleanup round:\n%s\n", string(output))
				}
			}
		}

		// Force stop JuiceFS process if still running
		if sys.JuiceFS != nil && sys.JuiceFS.IsMounted() {
			phaseStart := time.Now()
			fmt.Printf("WARNING: JuiceFS still mounted, attempting to stop\n")

			// Try graceful stop first with timeout
			stopCtx, stopCancel := context.WithTimeout(ctx, 10*time.Second)
			stopErr := sys.JuiceFS.Stop(stopCtx)
			stopCancel()

			// If still mounted after attempted stop, force unmount
			if stopErr != nil && sys.JuiceFS.IsMounted() {
				fmt.Printf("WARNING: JuiceFS graceful stop failed, forcing unmount\n")
				mountPath := filepath.Join(config.JuiceFSDataPath, "data")
				_ = exec.Command("umount", "-f", mountPath).Run()
				time.Sleep(500 * time.Millisecond)

				// Verify it's actually unmounted
				if sys.JuiceFS.IsMounted() {
					fmt.Printf("WARNING: JuiceFS STILL mounted after force unmount, killing processes\n")
					// Kill any juicefs processes
					_ = exec.Command("pkill", "-9", "juicefs").Run()
					time.Sleep(200 * time.Millisecond)
					_ = exec.Command("umount", "-f", mountPath).Run()
					time.Sleep(500 * time.Millisecond)

					if sys.JuiceFS.IsMounted() {
						fmt.Printf("ERROR: JuiceFS STILL mounted after all unmount attempts\n")
					}
				}
			}

			elapsed := time.Since(phaseStart)
			if elapsed > 15*time.Second {
				fmt.Printf("WARNING: JuiceFS cleanup took %v\n", elapsed)
			}
		}

		// Stop database manager (stops litestream for metadata DB)
		if sys.DBManager != nil {
			_ = sys.DBManager.Stop(ctx)
		}

		// Stop network services
		if sys.APIServer != nil {
			_ = sys.APIServer.Stop(ctx)
		}
		if sys.SocketServer != nil {
			_ = sys.SocketServer.Stop()
		}

		// Stop utilities
		if sys.AdminChannel != nil {
			_ = sys.AdminChannel.Stop()
		}
		if sys.Reaper != nil {
			_ = sys.Reaper.Stop(time.Second)
		}

		totalElapsed := time.Since(cleanupStart)
		if totalElapsed > 30*time.Second {
			fmt.Printf("WARNING: Total cleanup took %v (longer than 30s)\n", totalElapsed)
		} else if totalElapsed > 10*time.Second {
			fmt.Printf("INFO: Total cleanup took %v\n", totalElapsed)
		}
	}

	return sys, cleanup, nil
}

// aggressiveUnmountAll unmounts all mounts that might be using loop devices
// This MUST be called before detaching loop devices
func aggressiveUnmountAll() {
	startTime := time.Now()

	// Get all mounts
	output, err := exec.Command("mount").Output()
	if err != nil {
		return
	}

	lines := string(output)
	if lines == "" {
		return
	}

	// Find all overlay and loop-based mounts
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
			mountsToUnmount = append(mountsToUnmount, mountPoint)
		}
	}

	if len(mountsToUnmount) > 0 {
		fmt.Printf("WARNING: Found %d overlay/loop mounts to clean up: %v\n", len(mountsToUnmount), mountsToUnmount)
	}

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
			}
		}
	}

	// Wait for unmounts to complete
	time.Sleep(200 * time.Millisecond)

	elapsed := time.Since(startTime)
	if elapsed > 500*time.Millisecond {
		fmt.Printf("WARNING: aggressiveUnmountAll took %v (longer than 500ms)\n", elapsed)
	}
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

		// Unmount ALL mounts before detaching loop devices
		t.Logf("Cleanup: Unmounting all overlay and loop-based mounts")
		aggressiveUnmountAll()

		// Aggressively clean up ALL loopback devices
		t.Logf("Cleanup: Detaching all loopback devices")
		aggressiveLoopbackCleanup()

		// Verify loopbacks are gone
		if output, err := exec.Command("losetup", "-a").Output(); err == nil {
			loopList := string(output)
			if loopList != "" {
				t.Logf("Cleanup: Loopback devices still present after cleanup, trying again:\n%s", loopList)
				aggressiveUnmountAll()
				time.Sleep(500 * time.Millisecond)
				aggressiveLoopbackCleanup()
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
