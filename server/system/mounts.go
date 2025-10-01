package system

import (
	"fmt"
	"log/slog"
	"os"
	"os/exec"
)

// SetupFlyVolMount sets up the /dev/fly_vol bind mount if not already mounted
func SetupFlyVolMount() error {
	flyVolPath := "/dev/fly_vol"
	upperLayerPath := "/.fly-upper-layer/fly_vol"
	logger := slog.Default()

	logger.Debug("Checking if /dev/fly_vol is already mounted", "path", flyVolPath)
	// Check if /dev/fly_vol is already a mount point
	cmd := exec.Command("mountpoint", "-q", flyVolPath)
	if err := cmd.Run(); err == nil {
		// Already mounted
		logger.Debug("/dev/fly_vol is already mounted, skipping setup")
		return nil
	}
	logger.Debug("/dev/fly_vol is not mounted, proceeding with setup")

	// Create the upper layer directory
	logger.Debug("Creating upper layer directory", "path", upperLayerPath)
	if err := os.MkdirAll(upperLayerPath, 0755); err != nil {
		logger.Error("Failed to create upper layer directory", "path", upperLayerPath, "error", err)
		return fmt.Errorf("failed to create upper layer directory: %w", err)
	}

	// Check if upper layer exists and get info
	if info, err := os.Stat(upperLayerPath); err == nil {
		logger.Debug("Upper layer directory created/exists", "path", upperLayerPath, "mode", info.Mode())
	}

	// Create /dev/fly_vol directory
	logger.Debug("Creating /dev/fly_vol directory", "path", flyVolPath)
	if err := os.MkdirAll(flyVolPath, 0755); err != nil {
		logger.Error("Failed to create /dev/fly_vol directory", "path", flyVolPath, "error", err)
		return fmt.Errorf("failed to create /dev/fly_vol directory: %w", err)
	}

	// Bind mount /.fly-upper-layer/fly_vol to /dev/fly_vol
	logger.Info("Performing bind mount", "source", upperLayerPath, "target", flyVolPath)
	cmd = exec.Command("mount", "--bind", upperLayerPath, flyVolPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		logger.Error("Failed to bind mount /dev/fly_vol",
			"source", upperLayerPath,
			"target", flyVolPath,
			"error", err,
			"output", string(output))
		return fmt.Errorf("failed to bind mount /dev/fly_vol: %w", err)
	}

	logger.Info("/dev/fly_vol bind mount completed successfully", "source", upperLayerPath, "target", flyVolPath)
	return nil
}
