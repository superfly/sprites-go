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
	sys, err := system.New(config)
	if err != nil {
		return nil, func() {}, err
	}

	cleanup := func() {
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer cancel()

		// Stop each component individually, swallowing errors
		// Components are responsible for cleaning up their own resources

		// Force kill process if running (no graceful shutdown in cleanup)
		if sys.IsProcessRunning() {
			pid := sys.ProcessPID()
			if pid > 0 {
				// Send SIGKILL to process group
				_ = syscall.Kill(-pid, syscall.SIGKILL)
				// Give it a moment to die
				time.Sleep(100 * time.Millisecond)
			}
		}

		// Stop services manager
		if sys.ServicesManager != nil {
			_ = sys.ServicesManager.StopForUnmount()
		}

		// Stop overlay manager (unmounts overlayfs, checkpoint mounts, and loop devices)
		if sys.OverlayManager != nil {
			_ = sys.OverlayManager.Unmount(ctx)
		}

		// Force kill JuiceFS process if still running
		if sys.JuiceFS != nil && sys.JuiceFS.IsMounted() {
			// Try graceful stop first with short timeout
			stopCtx, stopCancel := context.WithTimeout(ctx, 5*time.Second)
			stopErr := sys.JuiceFS.Stop(stopCtx)
			stopCancel()

			// If still mounted after attempted stop, force unmount
			if stopErr != nil && sys.JuiceFS.IsMounted() {
				_ = exec.Command("umount", "-f", "-l", filepath.Join(config.JuiceFSDataPath, "data")).Run()
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
	}

	return sys, cleanup, nil
}

// RegisterSystemCleanup registers a cleanup handler to ensure the system is properly shut down
// This should be called immediately after creating a system instance in tests
func RegisterSystemCleanup(t *testing.T, sys *system.System) {
	t.Helper()
	t.Cleanup(func() {
		// Always try to shutdown, even if test failed or system already stopped
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer cancel()

		t.Logf("Test cleanup: shutting down system")
		if err := sys.Shutdown(ctx); err != nil {
			t.Logf("Cleanup shutdown error (may be expected if already shut down): %v", err)
		}

		// Extra verification: manually unmount any leftover mounts
		if sys.OverlayManager != nil {
			if sys.OverlayManager.IsOverlayFSMounted() {
				t.Logf("Cleanup: OverlayFS still mounted, forcing unmount")
				cleanupCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				defer cancel()
				_ = sys.OverlayManager.Unmount(cleanupCtx)
			}
		}

		if sys.JuiceFS != nil {
			if sys.JuiceFS.IsMounted() {
				t.Logf("Cleanup: JuiceFS still mounted, forcing stop")
				cleanupCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				defer cancel()
				_ = sys.JuiceFS.Stop(cleanupCtx)
			}
		}
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
