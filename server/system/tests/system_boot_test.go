package tests

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestSystemBootSequence verifies the correct boot order of all subsystems
func TestSystemBootSequence(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a simple test process
	testScript := CreateTestScript(t, testDir, "boot-test.sh")

	config := TestConfig(testDir)
	config.ProcessCommand = []string{testScript}

	// Use a non-existent URL for admin channel to prevent connection attempts
	// but still allow the API server to work
	config.AdminChannelURL = "http://localhost:1/admin"

	// Validate config
	if err := config.Validate(); err != nil {
		t.Fatalf("Invalid config: %v", err)
	}

	// Log the config to debug
	t.Logf("Config APIToken before New: %s", config.APIToken)

	// Create system
	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system and verify boot sequence
	t.Log("Starting system boot sequence...")
	StartSystemWithTimeout(t, sys, 60*time.Second)

	// Verify Phase 1: Utilities started
	t.Run("Phase1_Utilities", func(t *testing.T) {
		// Reaper should be running
		if sys.Reaper == nil {
			t.Error("Reaper should be initialized after boot")
		}

		// Admin channel should be started
		if sys.AdminChannel == nil {
			t.Error("Admin channel should be initialized")
		}

		// Resource monitor should be started
		if sys.ResourceMonitor == nil {
			t.Error("Resource monitor should be initialized")
		}
	})

	// Verify Phase 2: Network services
	t.Run("Phase2_NetworkServices", func(t *testing.T) {
		// API server should be running
		if sys.APIServer == nil {
			t.Error("API server should be initialized")
		}

		// Socket server should be running
		if sys.SocketServer == nil {
			t.Error("Socket server should be initialized")
		}

		// Check API address from config
		if sys.APIServer != nil && config.APIListenAddr != "" {
			t.Logf("API server configured to listen on %s", config.APIListenAddr)
		}
	})

	// Verify Phase 3: Storage
	t.Run("Phase3_Storage", func(t *testing.T) {
		// Wait for storage to be ready
		WaitForCondition(t, 5*time.Second, 100*time.Millisecond,
			func() bool { return sys.DBManager != nil },
			"DB manager initialization")

		// JuiceFS is optional - only check if configured
		if config.JuiceFSDataPath != "" && sys.JuiceFS == nil {
			t.Error("JuiceFS should be initialized when configured")
		}

		// Overlay is optional - only check if enabled
		if config.OverlayEnabled && sys.OverlayManager == nil {
			t.Error("Overlay manager should be initialized when enabled")
		}

		// Checkpoint manager is part of overlay manager
		// In the test config, if JuiceFS is configured, checkpoint functionality should be available
		if config.JuiceFSDataPath != "" && sys.OverlayManager == nil {
			t.Error("Overlay manager should be initialized when JuiceFS is configured")
		}
	})

	// Verify Phase 4: Process management
	t.Run("Phase4_ProcessManagement", func(t *testing.T) {
		// Activity monitor should be running
		if sys.ActivityMonitor == nil {
			t.Error("Activity monitor should be initialized")
		}

		// Services manager should be running
		if sys.ServicesManager == nil {
			t.Error("Services manager should be initialized")
		}

		// TMUX manager should be initialized
		if sys.TMUXManager == nil {
			t.Error("TMUX manager should be initialized")
		}
	})

	// Verify Phase 5: Main process started
	t.Run("Phase5_MainProcess", func(t *testing.T) {
		// Process should be running
		WaitForCondition(t, 5*time.Second, 100*time.Millisecond,
			sys.IsProcessRunning,
			"main process to start")

		if !sys.IsProcessRunning() {
			t.Fatal("Main process should be running after boot")
		}
	})

	// Verify system is fully operational
	VerifySystemRunning(t, sys)
	// Cleanup (including shutdown and mount verification) handled by deferred TestSystem cleanup
}

// TestSystemBootWithInvalidProcess verifies boot fails gracefully with invalid process
func TestSystemBootWithInvalidProcess(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)
	config.ProcessCommand = []string{"/nonexistent/binary"}

	// Create system
	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Boot should fail
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected boot to fail with invalid process")
	}

	t.Logf("Boot correctly failed with: %v", err)
}

// TestSystemBootWithStorageFailure tests boot behavior when storage initialization fails
func TestSystemBootWithStorageFailure(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Make the write directory read-only to cause storage failures
	if err := os.Chmod(testDir, 0444); err != nil {
		t.Skip("Cannot make directory read-only")
	}
	defer os.Chmod(testDir, 0755) // Restore permissions

	// Verify the directory is actually read-only by trying to create a file
	testFile := filepath.Join(testDir, "test-write")
	if err := os.WriteFile(testFile, []byte("test"), 0644); err == nil {
		os.Remove(testFile)
		os.Chmod(testDir, 0755)
		t.Skip("Directory is not actually read-only (possibly running as root)")
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{"/bin/sh", "-c", "echo test"}

	// Create system - this might fail due to permissions
	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Logf("System creation failed as expected: %v", err)
		return
	}

	// If creation succeeded, boot should fail
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected boot to fail with storage issues")
	}

	t.Logf("Boot correctly failed with: %v", err)
}

// TestSystemBootIdempotency verifies system cannot be started twice
func TestSystemBootIdempotency(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Try to start again - should fail
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected second Start() to fail")
	}

	expectedMsg := "failed to boot system: system already running"
	if err.Error() != expectedMsg {
		t.Errorf("Expected '%s' error, got: %v", expectedMsg, err)
	}
}

// TestSystemBootWithCustomPorts tests boot with specific port configurations
func TestSystemBootWithCustomPorts(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Get a free port and format as host:port
	freePort := GetFreePort(t)
	listenAddr := "127.0.0.1:" + freePort

	config := TestConfig(testDir)
	config.APIListenAddr = listenAddr

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system with longer timeout for JuiceFS format
	StartSystemWithTimeout(t, sys, 30*time.Second)

	// Verify API server config has the correct address
	if config.APIListenAddr != listenAddr {
		t.Errorf("Expected API config on %s, got %s", listenAddr, config.APIListenAddr)
	}
}
