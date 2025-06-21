package juicefs

import (
	"context"
	"fmt"
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
}

// NewOverlay creates a new overlay manager instance
func NewOverlay(j *JuiceFS) *OverlayManager {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	return &OverlayManager{
		juiceFS:   j,
		imagePath: filepath.Join(mountPath, "active", "root-overlay.img"),
		mountPath: filepath.Join(j.config.BaseDir, "root-overlay"),
		imageSize: "100G", // 100GB sparse image
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

	fmt.Printf("Creating %s sparse image at %s...\n", om.imageSize, om.imagePath)

	// Create sparse image using dd
	cmd := exec.Command("dd", "if=/dev/zero", fmt.Sprintf("of=%s", om.imagePath),
		"bs=1", "count=0", fmt.Sprintf("seek=%s", om.imageSize))
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to create sparse image: %w, output: %s", err, string(output))
	}

	// Format with ext4
	fmt.Println("Formatting image with ext4...")
	cmd = exec.Command("mkfs.ext4", om.imagePath)
	if output, err := cmd.CombinedOutput(); err != nil {
		// Clean up the image file if formatting fails
		os.Remove(om.imagePath)
		return fmt.Errorf("failed to format image: %w, output: %s", err, string(output))
	}

	fmt.Printf("Root overlay image created successfully at %s\n", om.imagePath)
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
		fmt.Printf("Root overlay already mounted at %s\n", om.mountPath)
		return nil
	}

	// Ensure image exists
	if err := om.EnsureImage(); err != nil {
		return fmt.Errorf("failed to ensure overlay image: %w", err)
	}

	// Mount the image
	fmt.Printf("Mounting root overlay at %s...\n", om.mountPath)
	cmd := exec.CommandContext(ctx, "mount", "-o", "loop", om.imagePath, om.mountPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to mount overlay: %w, output: %s", err, string(output))
	}

	fmt.Printf("Root overlay mounted successfully at %s\n", om.mountPath)
	return nil
}

// Unmount unmounts the overlay
func (om *OverlayManager) Unmount(ctx context.Context) error {
	if !om.isMounted() {
		return nil
	}

	fmt.Printf("Unmounting root overlay at %s...\n", om.mountPath)

	// Sync first
	if err := om.sync(ctx); err != nil {
		fmt.Printf("Warning: sync failed: %v\n", err)
	}

	// Try normal unmount first
	cmd := exec.CommandContext(ctx, "umount", om.mountPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		// Try force unmount
		fmt.Println("Normal unmount failed, trying force unmount...")
		cmd = exec.CommandContext(ctx, "umount", "-f", om.mountPath)
		if output2, err2 := cmd.CombinedOutput(); err2 != nil {
			return fmt.Errorf("failed to unmount overlay: %w, outputs: %s, %s", err2, string(output), string(output2))
		}
	}

	fmt.Printf("Root overlay unmounted successfully\n")
	return nil
}

// PrepareForCheckpoint prepares the overlay for checkpointing by syncing and freezing
func (om *OverlayManager) PrepareForCheckpoint(ctx context.Context) error {
	if !om.isMounted() {
		return fmt.Errorf("overlay not mounted")
	}

	// Sync the filesystem
	fmt.Printf("Syncing root overlay filesystem...\n")
	if err := om.sync(ctx); err != nil {
		return fmt.Errorf("failed to sync overlay: %w", err)
	}

	// Freeze the filesystem
	fmt.Printf("Freezing root overlay filesystem...\n")
	freezeCmd := exec.CommandContext(ctx, "fsfreeze", "--freeze", om.mountPath)
	if output, err := freezeCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to freeze overlay: %w, output: %s", err, string(output))
	}

	return nil
}

// UnfreezeAfterCheckpoint unfreezes the overlay after checkpointing
func (om *OverlayManager) UnfreezeAfterCheckpoint(ctx context.Context) error {
	if !om.isMounted() {
		return nil // Not an error if not mounted
	}

	fmt.Printf("Unfreezing root overlay filesystem...\n")
	unfreezeCmd := exec.CommandContext(ctx, "fsfreeze", "--unfreeze", om.mountPath)
	if output, err := unfreezeCmd.CombinedOutput(); err != nil {
		// Check if it's already unfrozen
		if _, statErr := os.Stat(om.mountPath); statErr == nil {
			// Mount point exists, try to write a test file to see if it's frozen
			testFile := filepath.Join(om.mountPath, ".freeze_test")
			if testErr := os.WriteFile(testFile, []byte("test"), 0644); testErr == nil {
				// Successfully wrote, so it's not frozen
				os.Remove(testFile)
				return nil
			}
		}
		return fmt.Errorf("failed to unfreeze overlay: %w, output: %s", err, string(output))
	}

	return nil
}

// UpdateImagePath updates the image path after a restore operation
func (om *OverlayManager) UpdateImagePath() {
	mountPath := filepath.Join(om.juiceFS.config.BaseDir, "data")
	om.imagePath = filepath.Join(mountPath, "active", "root-overlay.img")
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

func (om *OverlayManager) sync(ctx context.Context) error {
	syncCmd := exec.CommandContext(ctx, "sync", "-f", om.mountPath)

	// Use a reasonable timeout for sync
	syncCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()

	syncCmd = exec.CommandContext(syncCtx, "sync", "-f", om.mountPath)
	return syncCmd.Run()
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
