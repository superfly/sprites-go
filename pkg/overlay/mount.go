package overlay

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

// EnsureImage creates the sparse image if it doesn't exist
func (m *Manager) EnsureImage() error {
	// Ensure the directory exists first (even if image exists, to prevent races)
	imageDir := filepath.Dir(m.imagePath)
	if err := os.MkdirAll(imageDir, 0755); err != nil {
		return fmt.Errorf("failed to create image directory: %w", err)
	}

	// Check if image already exists
	if info, err := os.Stat(m.imagePath); err == nil {
		m.logger.Debug("Overlay image already exists", "path", m.imagePath, "size", info.Size())
		return nil // Image already exists
	}

	m.logger.Info("Creating sparse image", "size", m.imageSize, "path", m.imagePath)

	// Create sparse image using dd
	cmd := exec.Command("dd", "if=/dev/zero", fmt.Sprintf("of=%s", m.imagePath),
		"bs=1", "count=0", fmt.Sprintf("seek=%s", m.imageSize))
	m.logger.Debug("Running dd command", "cmd", cmd.String())
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to create sparse image: %w, output: %s", err, string(output))
	}

	// Verify sparse file was created
	if info, err := os.Stat(m.imagePath); err != nil {
		return fmt.Errorf("failed to verify sparse image creation: %w", err)
	} else {
		m.logger.Debug("Sparse image created", "actualSize", info.Size())
	}

	// Format with ext4 (optimized for JuiceFS block/slice layouts)
	m.logger.Info("Formatting image with ext4...")
	cmd = exec.Command("mkfs.ext4",
		"-F",         // Force formatting without prompts
		"-b", "4096", // 4K blocks align with page size and JuiceFS
		"-i", "16384", // One inode per 16K for overlayfs metadata files
		"-m", "0", // No reserved blocks (it's a dedicated overlay)
		"-E", "lazy_itable_init=1,lazy_journal_init=1,stride=1024,stripe-width=1024", // Optimize for 4MB blocks
		"-O", "extent,huge_file,flex_bg,dir_nlink,extra_isize,sparse_super2", // Enable optimizations
		"-J", "size=128", // 128MB journal for good performance
		m.imagePath)
	if output, err := cmd.CombinedOutput(); err != nil {
		// Clean up the image file if formatting fails
		os.Remove(m.imagePath)
		return fmt.Errorf("failed to format image: %w, output: %s", err, string(output))
	}

	m.logger.Info("Root overlay image created successfully", "path", m.imagePath)
	return nil
}

// WhenReady waits until both the loopback mount and overlayfs are ready or returns when context is cancelled.
// This uses a channel-based approach without polling.
func (m *Manager) WhenReady(ctx context.Context) error {
	select {
	case <-m.mountReady:
		// Check if there was an error during mount
		m.mountErrorMu.RLock()
		err := m.mountError
		m.mountErrorMu.RUnlock()
		return err
	case <-ctx.Done():
		return ctx.Err()
	}
}

// PrepareAndMount ensures the image exists, mounts it, and handles corruption recovery
// This is the high-level function that should be called by system code
func (m *Manager) PrepareAndMount(ctx context.Context) error {
	// Ensure image exists
	if _, err := os.Stat(m.imagePath); os.IsNotExist(err) {
		m.logger.Warn("Overlay image does not exist, creating it", "path", m.imagePath)
		if err := m.EnsureImage(); err != nil {
			return fmt.Errorf("failed to create overlay image: %w", err)
		}
	}

	// Try to mount
	err := m.Mount(ctx)
	if err == nil {
		return nil
	}

	// Check if it's a corruption error
	errStr := err.Error()
	if strings.Contains(errStr, "I/O error") || strings.Contains(errStr, "can't read superblock") {
		m.logger.Error("Mount failed with corruption indicators, attempting recovery", "error", err)

		// Backup the corrupted image
		timestamp := time.Now().Format("20060102-150405")
		backupPath := fmt.Sprintf("%s.corrupt-%s.bak", strings.TrimSuffix(m.imagePath, ".img"), timestamp)
		m.logger.Warn("Backing up corrupted image", "from", m.imagePath, "to", backupPath)

		if backupErr := os.Rename(m.imagePath, backupPath); backupErr != nil {
			m.logger.Warn("Failed to backup corrupted image, attempting removal", "error", backupErr)
			if removeErr := os.Remove(m.imagePath); removeErr != nil {
				return fmt.Errorf("failed to remove corrupted image: %w", removeErr)
			}
		} else {
			m.logger.Info("Corrupted image backed up successfully", "backupPath", backupPath)
		}

		// Recreate the image
		m.logger.Info("Recreating overlay image after corruption")
		if createErr := m.EnsureImage(); createErr != nil {
			return fmt.Errorf("failed to recreate overlay image after corruption: %w", createErr)
		}

		// Retry mount
		m.logger.Info("Retrying mount after recreating image")
		if retryErr := m.Mount(ctx); retryErr != nil {
			return fmt.Errorf("mount failed after recreation: %w", retryErr)
		}

		return nil
	}

	// Not a corruption error, return original error
	return err
}

// Mount mounts the overlay image
// The image must already exist - call PrepareAndMount() or EnsureImage() first
func (m *Manager) Mount(ctx context.Context) error {
	// Ensure mount directory exists
	if err := os.MkdirAll(m.mountPath, 0755); err != nil {
		return fmt.Errorf("failed to create mount directory: %w", err)
	}

	// Check if image exists and is accessible before trying to mount
	if _, err := os.Stat(m.imagePath); err != nil {
		return fmt.Errorf("overlay image does not exist at %s: %w (call EnsureImage() first)", m.imagePath, err)
	}

	// Check if already mounted
	if m.isMounted() {
		m.logger.Info("Root overlay already mounted", "path", m.mountPath)

		// Skip overlayfs if configured
		if m.skipOverlayFS {
			// Signal mount is ready
			m.signalMountReady(nil)
			return nil
		}

		// Check if overlayfs is also mounted
		if m.isOverlayFSMounted() {
			m.logger.Info("OverlayFS already mounted", "path", m.overlayTargetPath)
			// Signal mount is ready
			m.signalMountReady(nil)
			return nil
		}

		// Mount only the overlayfs if loopback is mounted but overlayfs isn't
		err := m.mountOverlayFS(ctx)
		// Signal mount is ready (with error if any)
		m.signalMountReady(err)
		return err
	}

	// Try to mount the image (no artificial timeout)
	m.logger.Info("Mounting root overlay", "mountPath", m.mountPath)
	m.logger.Debug("Source image", "path", m.imagePath)

	// Prefer explicit loop device attach with discard, then mount with -o discard
	m.logger.Debug("Mounting via loop device with discard", "image", m.imagePath, "target", m.mountPath)
	// Create a short timeout for attach+mount to fail fast on IO errors
	mountCtx, cancel := context.WithTimeout(ctx, 10*time.Second)
	defer cancel()

	loopDevice, err := attachLoopDevice(m.imagePath)
	if err != nil {
		return fmt.Errorf("failed to create loop device: %w", err)
	}
	m.loopDevice = loopDevice
	m.logger.Debug("Created loop device", "device", m.loopDevice)

	m.logger.Info("Mounting loop device to overlay mount path", "device", m.loopDevice, "target", m.mountPath, "options", "discard")
	cmd := exec.CommandContext(mountCtx, "mount", "-o", "discard", m.loopDevice, m.mountPath)
	mountStart := time.Now()
	mountOutput, err := cmd.CombinedOutput()
	mountDuration := time.Since(mountStart)

	if mountCtx.Err() == context.DeadlineExceeded {
		m.logger.Error("Loop device mount command timed out after 10 seconds, likely due to I/O error", "duration", mountDuration, "device", m.loopDevice, "target", m.mountPath)
		err = fmt.Errorf("mount timeout")
	}

	if err != nil {
		m.logger.Error("Loop device mount failed", "error", err, "output", string(mountOutput), "duration", mountDuration, "device", m.loopDevice, "target", m.mountPath)
		// Probe to see if mount actually succeeded despite error
		if m.isMounted() {
			m.logger.Warn("Loop device mount reported error but mount is present in /proc/mounts - treating as success", "device", m.loopDevice, "target", m.mountPath)
			err = nil
		}
	}

	if err != nil {
		// Detach loop on failure
		if m.loopDevice != "" {
			_ = detachLoopDevice(m.loopDevice)
			m.loopDevice = ""
		}
		return fmt.Errorf("failed to mount overlay: %w, output: %s", err, string(mountOutput))
	}

	m.logger.Info("Root overlay mounted successfully", "path", m.mountPath)

	// Skip overlayfs if configured
	if m.skipOverlayFS {
		// Signal mount is ready
		m.signalMountReady(nil)
		return nil
	}

	// Now mount the overlayfs
	err = m.mountOverlayFS(ctx)
	if err != nil {
		// Cleanup on failure: unmount the loop device
		m.logger.Error("OverlayFS mount failed, cleaning up loop device mount", "error", err)
		if unmountErr := m.Unmount(ctx); unmountErr != nil {
			m.logger.Error("Failed to cleanup after overlayfs mount failure", "error", unmountErr)
		}
		// Signal mount failed
		m.signalMountReady(err)
		return fmt.Errorf("failed to mount overlayfs: %w", err)
	}

	// Signal mount is ready
	m.signalMountReady(nil)

	return nil
}

// mountOverlayFS creates and mounts the overlay filesystem
func (m *Manager) mountOverlayFS(ctx context.Context) error {
	// Check if all lower paths exist
	for _, lowerPath := range m.lowerPaths {
		if _, err := os.Stat(lowerPath); os.IsNotExist(err) {
			return fmt.Errorf("lower path does not exist: %s", lowerPath)
		}
	}

	// Create root-upper directory if it doesn't exist
	rootUpperDir := filepath.Join(m.mountPath, "root-upper")
	rootUpperCreated := false
	if _, err := os.Stat(rootUpperDir); os.IsNotExist(err) {
		m.logger.Info("Creating root-upper directory", "path", rootUpperDir)
		if err := os.MkdirAll(rootUpperDir, 0755); err != nil {
			return fmt.Errorf("failed to create root-upper directory: %w", err)
		}
		rootUpperCreated = true
	}

	// Check for migration: if root-upper was just created and old directories exist, move them
	if rootUpperCreated {
		oldUpperDir := filepath.Join(m.mountPath, "upper")
		oldWorkDir := filepath.Join(m.mountPath, "work")

		// Check if both old directories exist
		upperExists := false
		workExists := false
		if _, err := os.Stat(oldUpperDir); err == nil {
			upperExists = true
		}
		if _, err := os.Stat(oldWorkDir); err == nil {
			workExists = true
		}

		// If both exist, migrate them
		if upperExists && workExists {
			m.logger.Info("Migrating existing upper and work directories to root-upper")

			// Move upper directory
			newUpperDir := filepath.Join(rootUpperDir, "upper")
			if err := os.Rename(oldUpperDir, newUpperDir); err != nil {
				return fmt.Errorf("failed to migrate upper directory: %w", err)
			}
			m.logger.Info("Migrated upper directory", "from", oldUpperDir, "to", newUpperDir)

			// Move work directory
			newWorkDir := filepath.Join(rootUpperDir, "work")
			if err := os.Rename(oldWorkDir, newWorkDir); err != nil {
				// Try to rollback upper directory move
				os.Rename(newUpperDir, oldUpperDir)
				return fmt.Errorf("failed to migrate work directory: %w", err)
			}
			m.logger.Info("Migrated work directory", "from", oldWorkDir, "to", newWorkDir)
		}
	}

	// Create upper and work directories inside root-upper
	upperDir := filepath.Join(rootUpperDir, "upper")
	workDir := filepath.Join(rootUpperDir, "work")

	if err := os.MkdirAll(upperDir, 0755); err != nil {
		return fmt.Errorf("failed to create upper directory: %w", err)
	}

	if err := os.MkdirAll(workDir, 0755); err != nil {
		return fmt.Errorf("failed to create work directory: %w", err)
	}

	// Create target mount point
	if err := os.MkdirAll(m.overlayTargetPath, 0755); err != nil {
		return fmt.Errorf("failed to create overlay target directory: %w", err)
	}

	// Mount the overlay
	m.logger.Info("Mounting OverlayFS", "targetPath", m.overlayTargetPath)

	// Join multiple lower paths with colon separator for overlayfs
	lowerDirs := strings.Join(m.lowerPaths, ":")
	m.logger.Debug("OverlayFS paths",
		"lower", lowerDirs,
		"upper", upperDir,
		"work", workDir)

	m.logger.Info("Mounting overlayfs using syscall", "target", m.overlayTargetPath, "lowerdir", lowerDirs, "upperdir", upperDir, "workdir", workDir)

	mountStart := time.Now()
	err := mountOverlayFS(m.overlayTargetPath, lowerDirs, upperDir, workDir)
	mountDuration := time.Since(mountStart)

	if err != nil {
		m.logger.Error("OverlayFS mount syscall failed",
			"error", err,
			"duration", mountDuration,
			"lowerdir", lowerDirs,
			"upperdir", upperDir,
			"workdir", workDir,
			"target", m.overlayTargetPath)

		// Probe to see if mount actually succeeded despite error
		if m.isOverlayFSMounted() {
			m.logger.Warn("OverlayFS mount reported error but mount is present - treating as success", "target", m.overlayTargetPath)
			err = nil
		} else {
			// Mount truly failed - check if directories are still accessible
			m.probeOverlayFSPaths(lowerDirs, upperDir, workDir)
			return fmt.Errorf("failed to mount overlayfs: %w", err)
		}
	} else {
		m.logger.Info("OverlayFS mount syscall completed successfully", "duration", mountDuration)
	}

	m.logger.Info("OverlayFS mounted successfully", "path", m.overlayTargetPath)

	return nil
}

// Unmount unmounts the overlay
func (m *Manager) Unmount(ctx context.Context) error {
	// Signal shutdown
	select {
	case <-m.stopCh:
		// Already stopping
	default:
		close(m.stopCh)
	}

	// Perform cleanup in reverse order of Start()
	// First unmount checkpoint mounts
	if err := m.UnmountCheckpoints(ctx); err != nil {
		m.logger.Warn("Failed to unmount checkpoints during overlay unmount", "error", err)
		// Continue - non-fatal
	}

	// Then unmount overlayfs if it's mounted
	if m.isOverlayFSMounted() {
		// Try normal unmount first
		cmd := exec.Command("umount", m.overlayTargetPath)
		if output, err := cmd.CombinedOutput(); err != nil {
			// Try force unmount
			cmd = exec.Command("umount", "-f", m.overlayTargetPath)
			if output2, err2 := cmd.CombinedOutput(); err2 != nil {
				return fmt.Errorf("failed to unmount overlayfs: %w, outputs: %s, %s", err2, string(output), string(output2))
			}
		}

		// Verify overlayfs is actually unmounted
		if m.isOverlayFSMounted() {
			return fmt.Errorf("overlayfs still mounted after unmount command")
		}
	}

	// Then unmount the loopback mount
	if !m.isMounted() {
		// Even if not mounted, ensure any associated loop device is detached
		if m.loopDevice != "" {
			if err := detachLoopDevice(m.loopDevice); err != nil {
				return fmt.Errorf("failed to detach loop device %s: %w", m.loopDevice, err)
			}
			m.loopDevice = ""
		}

		// Close stoppedCh and reset started flag
		select {
		case <-m.stoppedCh:
			// Already closed
		default:
			close(m.stoppedCh)
		}
		m.started = false
		return nil
	}

	m.logger.Info("Unmounting root overlay", "path", m.mountPath)

	// Sync first
	if err := m.sync(ctx); err != nil {
		m.logger.Warn("Sync failed", "error", err)
	}

	// Try normal unmount first
	cmd := exec.Command("umount", m.mountPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		// Try force unmount
		cmd = exec.Command("umount", "-f", m.mountPath)
		if output2, err2 := cmd.CombinedOutput(); err2 != nil {
			return fmt.Errorf("failed to unmount overlay: %w, outputs: %s, %s", err2, string(output), string(output2))
		}
	}

	// Verify loopback mount is actually unmounted
	if m.isMounted() {
		return fmt.Errorf("loopback mount still mounted after umount command")
	}

	// Detach loop device now that the mount is gone
	// The detachLoopDevice function will wait for the kernel to release all references
	if m.loopDevice != "" {
		if err := detachLoopDevice(m.loopDevice); err != nil {
			return fmt.Errorf("failed to detach loop device %s: %w", m.loopDevice, err)
		}
		m.loopDevice = ""
	}

	// Close stoppedCh and reset started flag
	select {
	case <-m.stoppedCh:
		// Already closed
	default:
		close(m.stoppedCh)
	}
	m.started = false

	return nil
}

// PrepareForCheckpoint prepares the overlay for checkpointing by syncing and freezing
func (m *Manager) PrepareForCheckpoint(ctx context.Context) error {
	if m.isOverlayFSMounted() {

		// 1) Sync the overlayfs filesystem (where actual writes occur)
		m.logger.Info("Syncing OverlayFS filesystem", "path", m.overlayTargetPath)
		syncCmd := exec.Command("sync", "-f", m.overlayTargetPath)
		if output, err := syncCmd.CombinedOutput(); err != nil {
			return fmt.Errorf("failed to sync overlayfs: %w, output: %s", err, string(output))
		}
		m.logger.Info("OverlayFS sync completed")
	}

	// 2) Freeze the underlying ext4 filesystem to prevent new writes
	m.logger.Info("Freezing underlying ext4 filesystem", "path", m.mountPath)
	freezeCmd := exec.Command("fsfreeze", "--freeze", m.mountPath)
	if output, err := freezeCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to freeze ext4 filesystem: %w, output: %s", err, string(output))
	}
	m.logger.Info("Filesystem frozen successfully")

	// 3) Sync the loopback mount while frozen
	m.logger.Info("Syncing loopback mount after freeze", "path", m.mountPath)
	if err := m.sync(ctx); err != nil {
		return fmt.Errorf("failed to sync loopback mount after freeze: %w", err)
	}

	f2, err := os.Open(m.imagePath)
	if err != nil {
		m.logger.Warn("Image open failed for fsync", "error", err, "path", m.imagePath)
	}
	if err == nil {
		defer f2.Close()
		if e := f2.Sync(); e != nil {
			m.logger.Warn("Image fsync failed", "error", e, "path", m.imagePath)
		}
	}

	return nil
}

// UnfreezeAfterCheckpoint unfreezes the overlay after checkpointing
func (m *Manager) UnfreezeAfterCheckpoint(ctx context.Context) error {
	if !m.isMounted() {
		return nil // Not an error if not mounted
	}

	m.logger.Info("Unfreezing underlying ext4 filesystem", "path", m.mountPath)
	unfreezeCmd := exec.Command("fsfreeze", "--unfreeze", m.mountPath)
	if output, err := unfreezeCmd.CombinedOutput(); err != nil {
		// Check if it's already unfrozen by trying to write to the underlying mount
		testFile := filepath.Join(m.mountPath, ".freeze_test")
		if testErr := os.WriteFile(testFile, []byte("test"), 0644); testErr == nil {
			// Successfully wrote, so it's not frozen
			os.Remove(testFile)
			m.logger.Info("Filesystem was already unfrozen")
			return nil
		}
		return fmt.Errorf("failed to unfreeze ext4 filesystem: %w, output: %s", err, string(output))
	}
	m.logger.Info("Filesystem unfrozen successfully")

	return nil
}

// Helper methods

func (m *Manager) IsMounted() bool {
	// Check if the mount point exists and is actually mounted
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}

	mounts := string(mountsData)
	// Look for a line that has our mount path as the mount point
	expectedMount := fmt.Sprintf(" %s ", m.mountPath)
	return strings.Contains(mounts, expectedMount)
}

func (m *Manager) IsOverlayFSMounted() bool {
	// Check if overlayfs is mounted
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}

	mounts := string(mountsData)
	// Look for a line like: overlay /mnt/newroot overlay ...
	expectedMount := fmt.Sprintf("overlay %s overlay", m.overlayTargetPath)
	return strings.Contains(mounts, expectedMount)
}

// Legacy private methods for backward compatibility
func (m *Manager) isMounted() bool {
	return m.IsMounted()
}

func (m *Manager) isOverlayFSMounted() bool {
	return m.IsOverlayFSMounted()
}

func (m *Manager) sync(ctx context.Context) error {
	// Don't use context for sync - let it complete fully
	// This is critical for data integrity during shutdown
	m.logger.Info("Starting filesystem sync", "path", m.mountPath)
	syncStart := time.Now()

	syncCmd := exec.Command("sync", "-f", m.mountPath)
	if output, err := syncCmd.CombinedOutput(); err != nil {
		if len(output) > 0 {
			return fmt.Errorf("sync failed: %w, output: %s", err, string(output))
		}
		return fmt.Errorf("sync failed: %w", err)
	}

	m.logger.Info("Filesystem sync completed", "path", m.mountPath, "duration", time.Since(syncStart))
	return nil
}

// probeOverlayFSPaths checks if overlay paths are accessible after mount failure
func (m *Manager) probeOverlayFSPaths(lowerDirs, upperDir, workDir string) {
	m.logger.Info("Probing overlayFS paths after mount failure")

	// Check each lower directory
	for i, lowerPath := range strings.Split(lowerDirs, ":") {
		if info, err := os.Stat(lowerPath); err != nil {
			m.logger.Error("Lower directory probe failed", "index", i, "path", lowerPath, "error", err)
		} else {
			m.logger.Info("Lower directory accessible", "index", i, "path", lowerPath, "isDir", info.IsDir())
		}
	}

	// Check upper directory
	if info, err := os.Stat(upperDir); err != nil {
		m.logger.Error("Upper directory probe failed", "path", upperDir, "error", err)
	} else {
		m.logger.Info("Upper directory accessible", "path", upperDir, "isDir", info.IsDir())
	}

	// Check work directory
	if info, err := os.Stat(workDir); err != nil {
		m.logger.Error("Work directory probe failed", "path", workDir, "error", err)
	} else {
		m.logger.Info("Work directory accessible", "path", workDir, "isDir", info.IsDir())
	}

	// Check target directory
	if info, err := os.Stat(m.overlayTargetPath); err != nil {
		m.logger.Error("Target directory probe failed", "path", m.overlayTargetPath, "error", err)
	} else {
		m.logger.Info("Target directory accessible", "path", m.overlayTargetPath, "isDir", info.IsDir())
	}

	// Check /proc/mounts to see what is mounted
	if mountsData, err := os.ReadFile("/proc/mounts"); err != nil {
		m.logger.Error("Failed to read /proc/mounts", "error", err)
	} else {
		m.logger.Info("Current /proc/mounts content", "mounts", string(mountsData))
	}
}

// signalMountReady signals that the mount is ready or stores an error
func (m *Manager) signalMountReady(err error) {
	m.mountOnce.Do(func() {
		if err != nil {
			m.mountErrorMu.Lock()
			m.mountError = err
			m.mountErrorMu.Unlock()
		}
		close(m.mountReady)
	})
}
