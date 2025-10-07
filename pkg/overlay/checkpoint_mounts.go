package overlay

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"

	"golang.org/x/sync/errgroup"
)

// MountCheckpoints mounts the last 5 checkpoints readonly at /.sprite/checkpoints/
// If a checkpoint doesn't have a root-upper.img file, it bind mounts an empty directory
// Also mounts the current active upper directory readonly at /.sprite/checkpoints/active
func (m *Manager) MountCheckpoints(ctx context.Context) error {
	m.checkpointMu.Lock()
	defer m.checkpointMu.Unlock()

	// Clean up orphaned checkpoints before mounting
	if m.checkpointDB != nil {
		if err := m.CleanupOrphanedCheckpoints(); err != nil {
			m.logger.Warn("Failed to cleanup orphaned checkpoints", "error", err)
			// Continue - non-fatal
		}
	}

	// Set up the base checkpoint directory with shared propagation (idempotent)
	if err := m.SetupCheckpointMountBase(ctx); err != nil {
		return fmt.Errorf("failed to setup checkpoint mount base: %w", err)
	}

	// Mount the active upper directory first
	if err := m.mountActiveCheckpoint(ctx); err != nil {
		m.logger.Warn("Failed to mount active checkpoint", "error", err)
		// Continue - non-fatal
	}

	// Get list of checkpoints (sorted newest first)
	checkpoints, err := m.listCheckpoints()
	if err != nil {
		return fmt.Errorf("failed to list checkpoints: %w", err)
	}

	// Keep only last 5
	if len(checkpoints) > 5 {
		checkpoints = checkpoints[:5]
	}

	m.logger.Info("Mounting checkpoints", "count", len(checkpoints), "path", m.checkpointMountPath)

	// Release the lock for parallel mounting operations
	m.checkpointMu.Unlock()

	// Mount results to collect from parallel operations
	type mountResult struct {
		cpName     string
		mountPath  string
		loopDevice string
		err        error
	}

	// Use background context for mounting - these operations should complete
	// even if the caller's context is canceled
	g, gctx := errgroup.WithContext(context.Background())
	results := make(chan mountResult, len(checkpoints))

	for _, cpName := range checkpoints {
		cpName := cpName // Capture for goroutine
		g.Go(func() error {
			loopDevice, mountPath, err := m.doMountSingleCheckpoint(gctx, cpName)
			results <- mountResult{
				cpName:     cpName,
				mountPath:  mountPath,
				loopDevice: loopDevice,
				err:        err,
			}
			return err
		})
	}

	// Wait for all parallel mounts to complete
	mountErr := g.Wait()
	close(results)

	// Reacquire the lock to update maps
	m.checkpointMu.Lock()

	// Process all results and update maps
	for res := range results {
		if res.err != nil {
			m.logger.Warn("Failed to mount checkpoint", "checkpoint", res.cpName, "error", res.err)
		} else {
			m.checkpointMounts[res.cpName] = res.mountPath
			if res.loopDevice != "" {
				m.checkpointLoopDevices[res.cpName] = res.loopDevice
			}
		}
	}

	return mountErr
}

// listCheckpoints returns a list of checkpoint directory names, sorted newest first
func (m *Manager) listCheckpoints() ([]string, error) {
	entries, err := os.ReadDir(m.checkpointBasePath)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil // No checkpoints yet
		}
		return nil, err
	}

	var checkpoints []string
	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		name := entry.Name()
		// Skip orphaned and in-progress checkpoints
		if strings.HasSuffix(name, ".orphaned") || strings.HasSuffix(name, ".in-progress") {
			continue
		}
		// Include only vN directories
		if strings.HasPrefix(name, "v") {
			checkpoints = append(checkpoints, name)
		}
	}

	// Sort by version number (newest first)
	// Extract numeric part and sort
	type checkpoint struct {
		name string
		num  int
	}
	var cps []checkpoint
	for _, name := range checkpoints {
		numStr := strings.TrimPrefix(name, "v")
		if num, err := strconv.Atoi(numStr); err == nil {
			cps = append(cps, checkpoint{name, num})
		}
	}

	// Sort descending by number
	for i := 0; i < len(cps); i++ {
		for j := i + 1; j < len(cps); j++ {
			if cps[j].num > cps[i].num {
				cps[i], cps[j] = cps[j], cps[i]
			}
		}
	}

	result := make([]string, len(cps))
	for i, cp := range cps {
		result[i] = cp.name
	}

	return result, nil
}

// doMountSingleCheckpoint mounts a single checkpoint readonly and returns mount info
// Returns (loopDevice, mountPath, error). Maps are not updated - caller should update them.
func (m *Manager) doMountSingleCheckpoint(ctx context.Context, cpName string) (string, string, error) {
	cpDir := filepath.Join(m.checkpointBasePath, cpName)
	imgPath := filepath.Join(cpDir, "root-upper.img")
	mountPath := filepath.Join(m.checkpointMountPath, cpName)

	// Check if image file exists
	if _, err := os.Stat(imgPath); err != nil {
		if os.IsNotExist(err) {
			// No image file - skip mounting this checkpoint
			m.logger.Info("Checkpoint has no disk image, skipping mount", "checkpoint", cpName)
			return "", "", nil // Not an error, just skip
		}
		// Other error (I/O, permission, etc.) - skip this checkpoint
		m.logger.Warn("Cannot access checkpoint disk image, skipping mount", "checkpoint", cpName, "error", err)
		return "", "", nil // Not fatal, just skip
	}

	// Ensure mount point exists
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		return "", "", fmt.Errorf("failed to create mount point: %w", err)
	}

	// Mount the image file
	m.logger.Info("Mounting checkpoint image", "checkpoint", cpName, "image", imgPath, "mount", mountPath)

	// Attach to loop device
	losetupCmd := exec.CommandContext(ctx, "losetup", "-f", "--show", "-r", imgPath)
	output, err := losetupCmd.CombinedOutput()
	if err != nil {
		return "", "", fmt.Errorf("losetup failed: %w, output: %s", err, string(output))
	}

	loopDevice := strings.TrimSpace(string(output))

	// Mount readonly
	mountCmd := exec.CommandContext(ctx, "mount", "-o", "ro", loopDevice, mountPath)
	if output, err := mountCmd.CombinedOutput(); err != nil {
		// Cleanup loop device
		exec.Command("losetup", "-d", loopDevice).Run()
		return "", "", fmt.Errorf("mount failed: %w, output: %s", err, string(output))
	}

	m.logger.Info("Checkpoint mounted successfully", "checkpoint", cpName, "path", mountPath)

	return loopDevice, mountPath, nil
}

// isCheckpointMounted checks if a checkpoint is currently mounted
func (m *Manager) isCheckpointMounted(cpName string) bool {
	_, exists := m.checkpointMounts[cpName]
	return exists
}

// UnmountCheckpoints unmounts all checkpoint mounts including the active checkpoint
func (m *Manager) UnmountCheckpoints(ctx context.Context) error {
	m.checkpointMu.Lock()
	defer m.checkpointMu.Unlock()

	var firstErr error

	// Unmount active checkpoint first
	if err := m.unmountActiveCheckpoint(ctx); err != nil {
		m.logger.Warn("Failed to unmount active checkpoint", "error", err)
		firstErr = err
	}

	// Unmount all other checkpoints
	for cpName, mountPath := range m.checkpointMounts {
		m.logger.Info("Unmounting checkpoint", "checkpoint", cpName, "path", mountPath)

		// Unmount
		umountCmd := exec.CommandContext(ctx, "umount", mountPath)
		if output, err := umountCmd.CombinedOutput(); err != nil {
			m.logger.Warn("Failed to unmount checkpoint", "checkpoint", cpName, "error", err, "output", string(output))
			if firstErr == nil {
				firstErr = fmt.Errorf("unmount %s: %w", cpName, err)
			}
		}

		// Detach loop device if exists
		if loopDevice, ok := m.checkpointLoopDevices[cpName]; ok {
			losetupCmd := exec.CommandContext(ctx, "losetup", "-d", loopDevice)
			if output, err := losetupCmd.CombinedOutput(); err != nil {
				m.logger.Warn("Failed to detach loop device", "checkpoint", cpName, "device", loopDevice, "error", err, "output", string(output))
			}
			delete(m.checkpointLoopDevices, cpName)
		}

		delete(m.checkpointMounts, cpName)
	}

	// Finally unmount the base checkpoint directory
	if err := m.unmountCheckpointBase(ctx); err != nil {
		m.logger.Warn("Failed to unmount checkpoint base", "error", err)
		if firstErr == nil {
			firstErr = err
		}
	}

	return firstErr
}

// OnCheckpointCreated is called when a new checkpoint is created
// It updates the checkpoint mounts to include the new checkpoint
func (m *Manager) OnCheckpointCreated(ctx context.Context) error {
	m.checkpointMu.Lock()
	defer m.checkpointMu.Unlock()

	m.logger.Info("Checkpoint created notification received, updating mounts")

	// Get list of checkpoints (sorted newest first)
	checkpoints, err := m.listCheckpoints()
	if err != nil {
		return fmt.Errorf("failed to list checkpoints: %w", err)
	}

	// Keep only last 5
	keep := checkpoints
	if len(checkpoints) > 5 {
		keep = checkpoints[:5]
	}

	// Build set of checkpoints we want to keep mounted
	shouldBeMounted := make(map[string]bool)
	for _, cpName := range keep {
		shouldBeMounted[cpName] = true
	}

	// Unmount any checkpoints that are no longer in the top 5
	for cpName, mountPath := range m.checkpointMounts {
		if !shouldBeMounted[cpName] {
			m.logger.Info("Unmounting old checkpoint", "checkpoint", cpName, "path", mountPath)

			// Unmount
			umountCmd := exec.CommandContext(ctx, "umount", mountPath)
			if output, err := umountCmd.CombinedOutput(); err != nil {
				m.logger.Warn("Failed to unmount old checkpoint", "checkpoint", cpName, "error", err, "output", string(output))
			}

			// Detach loop device if exists
			if loopDevice, ok := m.checkpointLoopDevices[cpName]; ok {
				losetupCmd := exec.CommandContext(ctx, "losetup", "-d", loopDevice)
				if output, err := losetupCmd.CombinedOutput(); err != nil {
					m.logger.Warn("Failed to detach loop device", "checkpoint", cpName, "device", loopDevice, "error", err, "output", string(output))
				}
				delete(m.checkpointLoopDevices, cpName)
			}

			delete(m.checkpointMounts, cpName)
		}
	}

	// Mount any new checkpoints that aren't already mounted
	for _, cpName := range keep {
		if !m.isCheckpointMounted(cpName) {
			loopDevice, mountPath, err := m.doMountSingleCheckpoint(ctx, cpName)
			if err != nil {
				m.logger.Warn("Failed to mount new checkpoint", "checkpoint", cpName, "error", err)
				// Continue with other checkpoints
			} else if mountPath != "" {
				// Update maps with successful mount
				m.checkpointMounts[cpName] = mountPath
				if loopDevice != "" {
					m.checkpointLoopDevices[cpName] = loopDevice
				}
			}
		}
	}

	return nil
}

// SetupCheckpointMountBase creates and configures the checkpoint mount directory with shared propagation
// Uses tmpfs to avoid inheriting the container's root overlay mount
func (m *Manager) SetupCheckpointMountBase(ctx context.Context) error {
	// Ensure the directory exists
	if err := os.MkdirAll(m.checkpointMountPath, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoint mount base: %w", err)
	}

	// Check if already mounted
	checkCmd := exec.CommandContext(ctx, "mountpoint", "-q", m.checkpointMountPath)
	if err := checkCmd.Run(); err == nil {
		m.logger.Debug("Checkpoint mount base already set up", "path", m.checkpointMountPath)
		return nil
	}

	// Mount as tmpfs to create an isolated filesystem
	// This prevents the Docker container's root overlay from appearing as a child mount
	mountCmd := exec.CommandContext(ctx, "mount", "-t", "tmpfs", "tmpfs", m.checkpointMountPath)
	if output, err := mountCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to mount checkpoint base as tmpfs: %w, output: %s", err, string(output))
	}

	// Make it a shared mount so submounts (checkpoints) propagate to containers
	// Since tmpfs creates a new filesystem (not inside the overlay), this won't
	// cause the container's root overlay to propagate into this directory
	shareCmd := exec.CommandContext(ctx, "mount", "--make-shared", m.checkpointMountPath)
	if output, err := shareCmd.CombinedOutput(); err != nil {
		// Try to cleanup the tmpfs mount
		exec.Command("umount", m.checkpointMountPath).Run()
		return fmt.Errorf("failed to make checkpoint base shared: %w, output: %s", err, string(output))
	}

	m.logger.Info("Checkpoint mount base configured as tmpfs with shared propagation", "path", m.checkpointMountPath)
	return nil
}

// unmountCheckpointBase unmounts the base checkpoint directory
func (m *Manager) unmountCheckpointBase(ctx context.Context) error {
	// Check if mounted
	checkCmd := exec.CommandContext(ctx, "mountpoint", "-q", m.checkpointMountPath)
	if err := checkCmd.Run(); err != nil {
		// Not mounted
		return nil
	}

	m.logger.Info("Unmounting checkpoint mount base", "path", m.checkpointMountPath)

	// Unmount
	umountCmd := exec.CommandContext(ctx, "umount", m.checkpointMountPath)
	if output, err := umountCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("unmount checkpoint base failed: %w, output: %s", err, string(output))
	}

	m.logger.Info("Checkpoint mount base unmounted successfully")
	return nil
}

// mountActiveCheckpoint mounts the current active upper directory readonly at /.sprite/checkpoints/active
func (m *Manager) mountActiveCheckpoint(ctx context.Context) error {
	// Determine the active upper directory path
	activeUpperDir := filepath.Join(m.mountPath, "root-upper", "upper")

	// Check if the directory exists
	if _, err := os.Stat(activeUpperDir); os.IsNotExist(err) {
		m.logger.Debug("Active upper directory does not exist yet", "path", activeUpperDir)
		return nil // Not an error - might not be mounted yet
	}

	// Ensure mount point exists
	if err := os.MkdirAll(m.activeCheckpointMount, 0755); err != nil {
		return fmt.Errorf("failed to create active checkpoint mount point: %w", err)
	}

	// Check if already mounted
	checkCmd := exec.CommandContext(ctx, "mountpoint", "-q", m.activeCheckpointMount)
	if err := checkCmd.Run(); err == nil {
		m.logger.Debug("Active checkpoint already mounted", "path", m.activeCheckpointMount)
		return nil
	}

	m.logger.Info("Mounting active upper directory readonly", "source", activeUpperDir, "target", m.activeCheckpointMount)

	// Bind mount (step 1: create the bind mount)
	mountCmd := exec.CommandContext(ctx, "mount", "--bind", activeUpperDir, m.activeCheckpointMount)
	if output, err := mountCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("bind mount active failed: %w, output: %s", err, string(output))
	}

	// Remount readonly (step 2: make it read-only)
	remountCmd := exec.CommandContext(ctx, "mount", "-o", "remount,ro,bind", m.activeCheckpointMount)
	if output, err := remountCmd.CombinedOutput(); err != nil {
		// Cleanup: unmount the bind mount we just created
		exec.CommandContext(ctx, "umount", m.activeCheckpointMount).Run()
		return fmt.Errorf("remount active readonly failed: %w, output: %s", err, string(output))
	}

	m.logger.Info("Active checkpoint mounted successfully", "path", m.activeCheckpointMount)
	return nil
}

// unmountActiveCheckpoint unmounts the active checkpoint mount
func (m *Manager) unmountActiveCheckpoint(ctx context.Context) error {
	// Check if mounted
	checkCmd := exec.CommandContext(ctx, "mountpoint", "-q", m.activeCheckpointMount)
	if err := checkCmd.Run(); err != nil {
		// Not mounted
		return nil
	}

	m.logger.Info("Unmounting active checkpoint", "path", m.activeCheckpointMount)

	// Unmount
	umountCmd := exec.CommandContext(ctx, "umount", m.activeCheckpointMount)
	if output, err := umountCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("unmount active checkpoint failed: %w, output: %s", err, string(output))
	}

	m.logger.Info("Active checkpoint unmounted successfully")
	return nil
}
