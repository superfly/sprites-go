package juicefs

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"time"
)

// OverlayManager manages the root overlay loopback mount
//
// The overlay provides a writable filesystem layer that can be:
// - Frozen during checkpoints to ensure consistency
// - Unmounted and remounted during restore operations
// - Automatically managed alongside the JuiceFS lifecycle
//
// The overlay uses a 100GB sparse ext4 image stored at:
// ${JUICEFS_BASE}/data/active/root-overlay.img
//
// And is mounted at:
// ${JUICEFS_BASE}/root-overlay
type OverlayManager struct {
	juiceFS   *JuiceFS
	imagePath string
	mountPath string
	imageSize string
	logger    *slog.Logger

	// Overlayfs configuration
	lowerPath         string // Lower directory (e.g., /mnt/app-image)
	overlayTargetPath string // Where to mount the overlay (e.g., /mnt/newroot)
	skipOverlayFS     bool   // Skip overlayfs mounting (for testing)
}

// NewOverlay creates a new overlay manager instance
func NewOverlay(j *JuiceFS, logger *slog.Logger) *OverlayManager {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	return &OverlayManager{
		juiceFS:           j,
		imagePath:         filepath.Join(mountPath, "active", "root-upper.img"),
		mountPath:         filepath.Join(mountPath, "root-upper"),
		imageSize:         "100G",           // 100GB sparse image
		lowerPath:         "/mnt/app-image", // Default lower directory
		overlayTargetPath: "/mnt/newroot",   // Default overlay mount point
		skipOverlayFS:     false,            // Default to mounting overlayfs
		logger:            logger,
	}
}

// GetMountPath returns the path where the overlay is mounted
func (om *OverlayManager) GetMountPath() string {
	return om.mountPath
}

// GetImagePath returns the path to the overlay image file
func (om *OverlayManager) GetImagePath() string {
	return om.imagePath
}

// SetLowerPath sets the path to the lower directory for overlay
func (om *OverlayManager) SetLowerPath(path string) {
	om.lowerPath = path
}

// SetAppImagePath sets the path to the app image (lower directory for overlay)
// Deprecated: Use SetLowerPath instead
func (om *OverlayManager) SetAppImagePath(path string) {
	om.SetLowerPath(path)
}

// SetOverlayTargetPath sets where to mount the final overlay
func (om *OverlayManager) SetOverlayTargetPath(path string) {
	om.overlayTargetPath = path
}

// SetSkipOverlayFS sets whether to skip overlayfs mounting (useful for testing)
func (om *OverlayManager) SetSkipOverlayFS(skip bool) {
	om.skipOverlayFS = skip
}

// GetLowerPath returns the configured lower directory path
func (om *OverlayManager) GetLowerPath() string {
	return om.lowerPath
}

// GetAppImagePath returns the configured app image path (lower directory)
// Deprecated: Use GetLowerPath instead
func (om *OverlayManager) GetAppImagePath() string {
	return om.GetLowerPath()
}

// GetOverlayTargetPath returns the configured overlay target path
func (om *OverlayManager) GetOverlayTargetPath() string {
	return om.overlayTargetPath
}

// EnsureImage creates the sparse image if it doesn't exist
func (om *OverlayManager) EnsureImage() error {
	// Check if image already exists
	if _, err := os.Stat(om.imagePath); err == nil {
		return nil // Image already exists
	}

	// Ensure the directory exists
	imageDir := filepath.Dir(om.imagePath)
	if err := os.MkdirAll(imageDir, 0755); err != nil {
		return fmt.Errorf("failed to create image directory: %w", err)
	}

	om.logger.Info("Creating sparse image", "size", om.imageSize, "path", om.imagePath)

	// Create sparse image using dd
	cmd := exec.Command("dd", "if=/dev/zero", fmt.Sprintf("of=%s", om.imagePath),
		"bs=1", "count=0", fmt.Sprintf("seek=%s", om.imageSize))
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to create sparse image: %w, output: %s", err, string(output))
	}

	// Format with ext4
	om.logger.Info("Formatting image with ext4...")
	cmd = exec.Command("mkfs.ext4", om.imagePath)
	if output, err := cmd.CombinedOutput(); err != nil {
		// Clean up the image file if formatting fails
		os.Remove(om.imagePath)
		return fmt.Errorf("failed to format image: %w, output: %s", err, string(output))
	}

	om.logger.Info("Root overlay image created successfully", "path", om.imagePath)
	return nil
}

// Mount mounts the overlay image
func (om *OverlayManager) Mount(ctx context.Context) error {
	// Ensure mount directory exists
	if err := os.MkdirAll(om.mountPath, 0755); err != nil {
		return fmt.Errorf("failed to create mount directory: %w", err)
	}

	// Check if already mounted
	if om.isMounted() {
		om.logger.Info("Root overlay already mounted", "path", om.mountPath)

		// Skip overlayfs if configured
		if om.skipOverlayFS {
			return nil
		}

		// Check if overlayfs is also mounted
		if om.isOverlayFSMounted() {
			om.logger.Info("OverlayFS already mounted", "path", om.overlayTargetPath)
			return nil
		}

		// Mount only the overlayfs if loopback is mounted but overlayfs isn't
		return om.mountOverlayFS(ctx)
	}

	// Ensure image exists
	if err := om.EnsureImage(); err != nil {
		return fmt.Errorf("failed to ensure overlay image: %w", err)
	}

	// Verify the image file is accessible
	if info, err := os.Stat(om.imagePath); err != nil {
		return fmt.Errorf("overlay image not accessible at %s: %w", om.imagePath, err)
	} else {
		om.logger.Debug("Overlay image verified", "path", om.imagePath, "size", info.Size())
	}

	// Try to mount the image with a timeout
	om.logger.Info("Mounting root overlay", "mountPath", om.mountPath)
	om.logger.Debug("Source image", "path", om.imagePath)

	// Create a context with timeout for the mount command
	mountCtx, cancel := context.WithTimeout(ctx, 10*time.Second)
	defer cancel()

	cmd := exec.CommandContext(mountCtx, "mount", "-o", "loop", om.imagePath, om.mountPath)
	output, err := cmd.CombinedOutput()

	// Check if it was a timeout
	if mountCtx.Err() == context.DeadlineExceeded {
		om.logger.Error("Mount command timed out after 10 seconds, likely due to I/O error")
		err = fmt.Errorf("mount timeout")
	}

	// Check for I/O errors which indicate a corrupted image
	if err != nil && (stringContains(string(output), "I/O error") ||
		stringContains(string(output), "can't read superblock") ||
		err.Error() == "mount timeout") {
		om.logger.Error("Mount failed with I/O error, attempting recovery...", "error", err)
		if len(output) > 0 {
			om.logger.Debug("Mount output", "output", string(output))
		}

		// Delete the corrupted image
		om.logger.Info("Removing corrupted image", "path", om.imagePath)
		if removeErr := os.Remove(om.imagePath); removeErr != nil {
			om.logger.Warn("Failed to remove corrupted image", "error", removeErr)
		}

		// Recreate the image
		om.logger.Info("Recreating overlay image...")
		if createErr := om.EnsureImage(); createErr != nil {
			return fmt.Errorf("failed to recreate overlay image after I/O error: %w", createErr)
		}

		// Try mounting again with fresh timeout
		om.logger.Info("Retrying mount after recreating image...")
		mountCtx2, cancel2 := context.WithTimeout(ctx, 10*time.Second)
		defer cancel2()

		cmd = exec.CommandContext(mountCtx2, "mount", "-o", "loop", om.imagePath, om.mountPath)
		output, err = cmd.CombinedOutput()
	}

	if err != nil {
		return fmt.Errorf("failed to mount overlay: %w, output: %s", err, string(output))
	}

	om.logger.Info("Root overlay mounted successfully", "path", om.mountPath)

	// Skip overlayfs if configured
	if om.skipOverlayFS {
		return nil
	}

	// Now mount the overlayfs
	return om.mountOverlayFS(ctx)
}

// mountOverlayFS creates and mounts the overlay filesystem
func (om *OverlayManager) mountOverlayFS(ctx context.Context) error {
	// Check if app image path exists
	if _, err := os.Stat(om.lowerPath); os.IsNotExist(err) {
		return fmt.Errorf("app image path does not exist: %s", om.lowerPath)
	}

	// Create upper and work directories in the mounted loopback
	upperDir := filepath.Join(om.mountPath, "upper")
	workDir := filepath.Join(om.mountPath, "work")

	if err := os.MkdirAll(upperDir, 0755); err != nil {
		return fmt.Errorf("failed to create upper directory: %w", err)
	}

	if err := os.MkdirAll(workDir, 0755); err != nil {
		return fmt.Errorf("failed to create work directory: %w", err)
	}

	// Create target mount point
	if err := os.MkdirAll(om.overlayTargetPath, 0755); err != nil {
		return fmt.Errorf("failed to create overlay target directory: %w", err)
	}

	// Mount the overlay
	om.logger.Info("Mounting OverlayFS", "targetPath", om.overlayTargetPath)
	om.logger.Debug("OverlayFS paths",
		"lower", om.lowerPath,
		"upper", upperDir,
		"work", workDir)

	mountOptions := fmt.Sprintf("lowerdir=%s,upperdir=%s,workdir=%s",
		om.lowerPath, upperDir, workDir)

	cmd := exec.CommandContext(ctx, "mount", "-t", "overlay", "overlay",
		"-o", mountOptions, om.overlayTargetPath)

	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to mount overlayfs: %w, output: %s", err, string(output))
	}

	om.logger.Info("OverlayFS mounted successfully", "path", om.overlayTargetPath)
	return nil
}

// Unmount unmounts the overlay
func (om *OverlayManager) Unmount(ctx context.Context) error {
	// First unmount overlayfs if it's mounted
	if om.isOverlayFSMounted() {
		om.logger.Info("Unmounting OverlayFS", "path", om.overlayTargetPath)

		// Try normal unmount first
		cmd := exec.CommandContext(ctx, "umount", om.overlayTargetPath)
		if output, err := cmd.CombinedOutput(); err != nil {
			// Try force unmount
			om.logger.Debug("Normal overlayfs unmount failed, trying force unmount...")
			cmd = exec.CommandContext(ctx, "umount", "-f", om.overlayTargetPath)
			if output2, err2 := cmd.CombinedOutput(); err2 != nil {
				return fmt.Errorf("failed to unmount overlayfs: %w, outputs: %s, %s", err2, string(output), string(output2))
			}
		}
		om.logger.Info("OverlayFS unmounted successfully")
	}

	// Then unmount the loopback mount
	if !om.isMounted() {
		return nil
	}

	om.logger.Info("Unmounting root overlay", "path", om.mountPath)

	// Sync first
	if err := om.sync(ctx); err != nil {
		om.logger.Warn("Sync failed", "error", err)
	}

	// Try normal unmount first
	cmd := exec.CommandContext(ctx, "umount", om.mountPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		// Try force unmount
		om.logger.Debug("Normal unmount failed, trying force unmount...")
		cmd = exec.CommandContext(ctx, "umount", "-f", om.mountPath)
		if output2, err2 := cmd.CombinedOutput(); err2 != nil {
			return fmt.Errorf("failed to unmount overlay: %w, outputs: %s, %s", err2, string(output), string(output2))
		}
	}

	om.logger.Info("Root overlay unmounted successfully")
	return nil
}

// PrepareForCheckpoint prepares the overlay for checkpointing by syncing and freezing
func (om *OverlayManager) PrepareForCheckpoint(ctx context.Context) error {
	// If overlayfs is skipped, just sync and freeze the loopback mount
	if om.skipOverlayFS {
		if !om.isMounted() {
			return fmt.Errorf("loopback mount not mounted")
		}

		om.logger.Info("Syncing loopback mount", "path", om.mountPath)
		if err := om.sync(ctx); err != nil {
			return fmt.Errorf("failed to sync loopback mount: %w", err)
		}

		om.logger.Info("Freezing ext4 filesystem", "path", om.mountPath)
		freezeCmd := exec.CommandContext(ctx, "fsfreeze", "--freeze", om.mountPath)
		if output, err := freezeCmd.CombinedOutput(); err != nil {
			return fmt.Errorf("failed to freeze ext4 filesystem: %w, output: %s", err, string(output))
		}

		return nil
	}

	// Normal path with overlayfs
	if !om.isOverlayFSMounted() {
		return fmt.Errorf("overlayfs not mounted")
	}

	// Sync the overlayfs filesystem (where actual writes occur)
	om.logger.Info("Syncing OverlayFS filesystem", "path", om.overlayTargetPath)
	syncCmd := exec.CommandContext(ctx, "sync", "-f", om.overlayTargetPath)
	if output, err := syncCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to sync overlayfs: %w, output: %s", err, string(output))
	}

	// Also sync the underlying loopback mount to ensure all data is flushed
	om.logger.Info("Syncing underlying ext4 filesystem", "path", om.mountPath)
	syncCmd = exec.CommandContext(ctx, "sync", "-f", om.mountPath)
	if output, err := syncCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to sync loopback mount: %w, output: %s", err, string(output))
	}

	// Freeze the underlying ext4 filesystem (not the overlayfs)
	om.logger.Info("Freezing underlying ext4 filesystem", "path", om.mountPath)
	freezeCmd := exec.CommandContext(ctx, "fsfreeze", "--freeze", om.mountPath)
	if output, err := freezeCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to freeze ext4 filesystem: %w, output: %s", err, string(output))
	}

	return nil
}

// UnfreezeAfterCheckpoint unfreezes the overlay after checkpointing
func (om *OverlayManager) UnfreezeAfterCheckpoint(ctx context.Context) error {
	if !om.isMounted() {
		return nil // Not an error if not mounted
	}

	om.logger.Info("Unfreezing underlying ext4 filesystem", "path", om.mountPath)
	unfreezeCmd := exec.CommandContext(ctx, "fsfreeze", "--unfreeze", om.mountPath)
	if output, err := unfreezeCmd.CombinedOutput(); err != nil {
		// Check if it's already unfrozen by trying to write to the underlying mount
		testFile := filepath.Join(om.mountPath, ".freeze_test")
		if testErr := os.WriteFile(testFile, []byte("test"), 0644); testErr == nil {
			// Successfully wrote, so it's not frozen
			os.Remove(testFile)
			return nil
		}
		return fmt.Errorf("failed to unfreeze ext4 filesystem: %w, output: %s", err, string(output))
	}

	return nil
}

// UpdateImagePath updates the image path after a restore operation
func (om *OverlayManager) UpdateImagePath() {
	mountPath := filepath.Join(om.juiceFS.config.BaseDir, "data")
	om.imagePath = filepath.Join(mountPath, "active", "root-upper.img")
}

// Helper methods

func (om *OverlayManager) isMounted() bool {
	// Check if the mount point exists and is actually mounted
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}

	mounts := string(mountsData)
	// Look for a line that has our mount path as the mount point
	expectedMount := fmt.Sprintf(" %s ", om.mountPath)
	return stringContains(mounts, expectedMount)
}

func (om *OverlayManager) isOverlayFSMounted() bool {
	// Check if overlayfs is mounted
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}

	mounts := string(mountsData)
	// Look for a line like: overlay /mnt/newroot overlay ...
	expectedMount := fmt.Sprintf("overlay %s overlay", om.overlayTargetPath)
	return stringContains(mounts, expectedMount)
}

func (om *OverlayManager) sync(ctx context.Context) error {
	// Use a reasonable timeout for sync
	syncCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()

	syncCmd := exec.CommandContext(syncCtx, "sync", "-f", om.mountPath)
	if output, err := syncCmd.CombinedOutput(); err != nil {
		if len(output) > 0 {
			return fmt.Errorf("sync failed: %w, output: %s", err, string(output))
		}
		return fmt.Errorf("sync failed: %w", err)
	}
	return nil
}

// stringContains checks if a string contains a substring
func stringContains(s, substr string) bool {
	return len(s) >= len(substr) && stringContainsAt(s, substr)
}

func stringContainsAt(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
