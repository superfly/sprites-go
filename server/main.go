package main

import (
	"flag"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"github.com/superfly/sprite-env/pkg/container"
	"github.com/superfly/sprite-env/server/system"
)

func main() {
	// Set up crash handler
	crashHandler, err := system.NewCrashHandler()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to create crash handler: %v\n", err)
		// Continue without crash handler
	}
	if crashHandler != nil {
		defer crashHandler.Close()
	}

	// Parse command line and get configuration
	config, err := system.ParseConfig()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing command line: %v\n", err)
		flag.Usage()
		os.Exit(1)
	}

	// Setup cgroups hierarchy BEFORE anything else
	// This must run first so containers can be placed in the proper cgroups
	if err := system.SetupCgroups(); err != nil {
		fmt.Fprintf(os.Stderr, "Failed to setup cgroups: %v\n", err)
		os.Exit(1)
	}

	// Ensure /dev/fly_vol exists BEFORE creating system
	// Temporary: just create directory instead of mounting
	if err := os.MkdirAll("/dev/fly_vol", 0755); err != nil {
		fmt.Fprintf(os.Stderr, "Failed to create /dev/fly_vol: %v\n", err)
		os.Exit(1)
	}

	// Migration: Move old checkpoint db from juicefs dir to checkpoints dir if needed
	// This must happen AFTER fly_vol is mounted but BEFORE system is created
	migrateCheckpointDB(config)

	// Create system
	sys, err := system.New(config)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to create system: %v\n", err)
		os.Exit(1)
	}

	// Initialize container process template once (warns if missing)
	container.InitProcessTemplateFromEnv()

	// Set system reference in crash handler for panic recovery shutdown
	if crashHandler != nil {
		crashHandler.SetSystem(sys)
	}

	// Start the system
	if err := sys.Start(); err != nil {
		fmt.Fprintf(os.Stderr, "Failed to start system: %v\n", err)
		fmt.Fprintf(os.Stderr, "Startup failed, triggering shutdown sequence...\n")

		// Trigger shutdown by closing the shutdown channel
		sys.HandleSignal(syscall.SIGTERM)

		// Wait for shutdown to complete
		exitCode, shutdownErr := sys.WaitForExit()
		if shutdownErr != nil {
			fmt.Fprintf(os.Stderr, "Shutdown error: %v\n", shutdownErr)
			os.Exit(1)
		}

		// Exit with the code from shutdown
		os.Exit(exitCode)
	}

	// Set up signal handling
	signalCh := make(chan os.Signal, 1)
	signal.Notify(signalCh, syscall.SIGTERM, syscall.SIGINT, syscall.SIGHUP)

	// Handle signals in a separate goroutine
	go func() {
		for sig := range signalCh {
			sys.HandleSignal(sig)
		}
	}()

	// Wait for the system to exit
	exitCode, err := sys.WaitForExit()
	if err != nil {
		fmt.Fprintf(os.Stderr, "System exit error: %v\n", err)
		os.Exit(1)
	}

	// Exit with the code from the process
	os.Exit(exitCode)
}

// migrateCheckpointDB moves old checkpoint db from juicefs dir to checkpoints dir if needed
// This migration must run AFTER /dev/fly_vol is mounted and BEFORE the system is created
func migrateCheckpointDB(config *system.Config) {
	oldDir := filepath.Join(config.WriteDir, "juicefs")
	oldPath := filepath.Join(oldDir, "checkpoints.db")
	newDir := filepath.Join(config.WriteDir, "checkpoints")
	newPath := filepath.Join(newDir, "checkpoints.db")

	// Check if old checkpoint db exists
	if _, err := os.Stat(oldPath); err != nil {
		// Old db doesn't exist, nothing to migrate
		return
	}

	// Check if new checkpoint db already exists
	if _, err := os.Stat(newPath); err == nil {
		// New db already exists, skip migration
		return
	}

	// Perform migration
	fmt.Fprintf(os.Stderr, "Migrating checkpoint db from %s to %s\n", oldPath, newPath)

	// Create new directory
	if err := os.MkdirAll(newDir, 0755); err != nil {
		fmt.Fprintf(os.Stderr, "Failed to create checkpoint db directory during migration: %v\n", err)
		return
	}

	// Move main db file
	if err := os.Rename(oldPath, newPath); err != nil {
		fmt.Fprintf(os.Stderr, "Failed to move checkpoint db during migration: %v\n", err)
		return
	}

	// Best-effort move WAL and SHM sidecars
	_ = os.Rename(oldPath+"-wal", newPath+"-wal")
	_ = os.Rename(oldPath+"-shm", newPath+"-shm")

	fmt.Fprintf(os.Stderr, "Checkpoint db migration completed successfully\n")
}
