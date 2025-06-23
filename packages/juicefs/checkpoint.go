package juicefs

import (
	"bufio"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"
)

// CheckpointInfo contains information about a checkpoint
type CheckpointInfo struct {
	ID         string    `json:"id"`
	CreateTime time.Time `json:"create_time"`
	SourceID   string    `json:"source_id,omitempty"` // If this was restored from another checkpoint
	History    []string  `json:"history,omitempty"`   // Restore history from .history file
}

// Checkpoint creates a checkpoint of the active directory
func (j *JuiceFS) Checkpoint(ctx context.Context, checkpointID string) error {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	versionFile := filepath.Join(activeDir, ".version")

	// Ensure checkpoints directory exists
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoints directory: %w", err)
	}

	// Check if active directory exists
	if _, err := os.Stat(activeDir); os.IsNotExist(err) {
		return fmt.Errorf("active directory does not exist at %s", activeDir)
	}

	// Get current version
	currentVersion, err := j.GetCurrentVersion()
	if err != nil {
		return fmt.Errorf("failed to get current version: %w", err)
	}

	// The checkpoint will use the current version
	versionID := fmt.Sprintf("v%d", currentVersion)
	checkpointPath := filepath.Join(checkpointsDir, versionID)

	// Check if checkpoint already exists
	if _, err := os.Stat(checkpointPath); err == nil {
		return fmt.Errorf("checkpoint %s already exists at %s", versionID, checkpointPath)
	}

	// Increment version in active BEFORE creating checkpoint
	nextVersion := currentVersion + 1

	// Write new version to active directory with exclusive lock
	file, err := os.OpenFile(versionFile, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		return fmt.Errorf("failed to open version file: %w", err)
	}

	// Get exclusive lock
	if err := syscall.Flock(int(file.Fd()), syscall.LOCK_EX); err != nil {
		file.Close()
		return fmt.Errorf("failed to acquire exclusive lock on version file: %w", err)
	}

	// Write the new version
	if _, err := fmt.Fprintf(file, "v%d\n", nextVersion); err != nil {
		syscall.Flock(int(file.Fd()), syscall.LOCK_UN)
		file.Close()
		return fmt.Errorf("failed to write new version: %w", err)
	}

	if err := file.Sync(); err != nil {
		syscall.Flock(int(file.Fd()), syscall.LOCK_UN)
		file.Close()
		return fmt.Errorf("failed to sync version file: %w", err)
	}

	syscall.Flock(int(file.Fd()), syscall.LOCK_UN)
	file.Close()

	// Prepare overlay for checkpoint (sync and freeze)
	if j.overlayMgr != nil {
		if err := j.overlayMgr.PrepareForCheckpoint(ctx); err != nil {
			return fmt.Errorf("failed to prepare overlay for checkpoint: %w", err)
		}

		// Ensure we unfreeze the overlay even if the clone fails
		defer func() {
			if unfreezeErr := j.overlayMgr.UnfreezeAfterCheckpoint(ctx); unfreezeErr != nil {
				fmt.Printf("Warning: failed to unfreeze overlay: %v\n", unfreezeErr)
			}
		}()
	}

	// Clone active directory to checkpoint
	fmt.Printf("Creating checkpoint %s...\n", versionID)
	cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", activeDir, checkpointPath)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to create checkpoint: %w, output: %s", err, string(output))
	}

	// Update the .latest_version symlink to point to this checkpoint
	latestLink := filepath.Join(checkpointsDir, ".latest_version")
	// Remove old symlink if it exists
	os.Remove(latestLink)
	// Create new symlink (relative path)
	if err := os.Symlink(versionID, latestLink); err != nil {
		fmt.Printf("Warning: failed to update latest version symlink: %v\n", err)
	}

	// Also create .latest symlink pointing to the checkpoint's .version file
	latestVersionLink := filepath.Join(checkpointsDir, ".latest")
	os.Remove(latestVersionLink)
	// Create symlink to the .version file inside the checkpoint
	versionFilePath := filepath.Join(versionID, ".version")
	if err := os.Symlink(versionFilePath, latestVersionLink); err != nil {
		fmt.Printf("Warning: failed to create .latest symlink: %v\n", err)
	}

	fmt.Printf("Checkpoint created successfully at %s\n", checkpointPath)
	return nil
}

// CheckpointWithVersion creates a checkpoint and returns the version used
func (j *JuiceFS) CheckpointWithVersion(ctx context.Context) (string, error) {
	// Get current version before checkpoint (this will be the checkpoint ID)
	version, err := j.GetCurrentVersion()
	if err != nil {
		return "", fmt.Errorf("failed to get current version: %w", err)
	}

	// Create checkpoint (which will increment the version)
	err = j.Checkpoint(ctx, "")
	if err != nil {
		return "", err
	}

	// Return the version that was used for the checkpoint
	return fmt.Sprintf("v%d", version), nil
}

// Restore restores from a checkpoint
func (j *JuiceFS) Restore(ctx context.Context, checkpointID string) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	mountPath := filepath.Join(j.config.BaseDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	checkpointPath := filepath.Join(checkpointsDir, checkpointID)

	// Check if checkpoint exists
	if _, err := os.Stat(checkpointPath); os.IsNotExist(err) {
		return fmt.Errorf("checkpoint %s does not exist at %s", checkpointID, checkpointPath)
	}

	// Create a checkpoint of current state before restoring
	fmt.Printf("Creating checkpoint before restore...\n")
	preRestoreVersion, err := j.CheckpointWithVersion(ctx)
	if err != nil {
		// Log warning but don't fail the restore
		fmt.Printf("Warning: failed to create pre-restore checkpoint: %v\n", err)
	} else {
		fmt.Printf("Created pre-restore checkpoint %s\n", preRestoreVersion)
	}

	// Get current version after checkpoint (it was incremented)
	currentVersion, err := j.GetCurrentVersion()
	if err != nil {
		// If we can't read version, we'll use 0
		currentVersion = 0
	}

	// Handle overlay if present
	if j.overlayMgr != nil {
		// First sync and freeze the overlay (same as checkpoint)
		if err := j.overlayMgr.PrepareForCheckpoint(ctx); err != nil {
			// If prepare fails, it might be because overlay is not mounted, which is ok
			fmt.Printf("Note: could not prepare overlay for restore: %v\n", err)
		} else {
			// Unfreeze after sync
			if err := j.overlayMgr.UnfreezeAfterCheckpoint(ctx); err != nil {
				fmt.Printf("Warning: failed to unfreeze overlay: %v\n", err)
			}
		}

		// Unmount the overlay before restore
		if err := j.overlayMgr.Unmount(ctx); err != nil {
			fmt.Printf("Warning: failed to unmount overlay: %v\n", err)
		}
	}

	// If active directory exists, remove it
	if _, err := os.Stat(activeDir); err == nil {
		fmt.Printf("Removing current active directory...\n")
		if err := os.RemoveAll(activeDir); err != nil {
			return fmt.Errorf("failed to remove active directory: %w", err)
		}
	}

	// Clone checkpoint to active directory
	fmt.Printf("Restoring from checkpoint %s...\n", checkpointID)
	cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", checkpointPath, activeDir)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to restore from checkpoint: %w, output: %s", err, string(output))
	}

	// Write back the saved version to active/.version
	versionFile := filepath.Join(activeDir, ".version")
	if err := os.WriteFile(versionFile, []byte(fmt.Sprintf("v%d\n", currentVersion)), 0644); err != nil {
		fmt.Printf("Warning: failed to restore version file: %v\n", err)
	}

	// The clone operation will have copied the .history file from the checkpoint (if it exists)
	// Now append the new restore record to track that we restored TO the current version
	currentVersionStr := fmt.Sprintf("v%d", currentVersion)
	if err := j.appendToHistory(currentVersionStr); err != nil {
		fmt.Printf("Warning: failed to append to history file: %v\n", err)
	}

	// Mount the overlay from the restored active directory
	if j.overlayMgr != nil {
		// Update the image path to point to the restored active directory
		j.overlayMgr.UpdateImagePath()

		fmt.Printf("Mounting overlay from restored checkpoint...\n")
		fmt.Printf("  New image path: %s\n", j.overlayMgr.GetImagePath())

		// Mount the overlay
		if err := j.overlayMgr.Mount(ctx); err != nil {
			// Log error but don't fail the restore
			fmt.Printf("Warning: failed to mount overlay after restore: %v\n", err)
		}
	}

	// Initialize version file
	if err := j.initializeVersion(); err != nil {
		fmt.Printf("Warning: failed to initialize version file: %v\n", err)
	}

	// Initialize history file if it doesn't exist
	historyFile := filepath.Join(mountPath, "active", ".history")
	if _, err := os.Stat(historyFile); os.IsNotExist(err) {
		// Get current version
		version, err := j.GetCurrentVersion()
		if err == nil {
			// Get active directory creation time
			if info, err := os.Stat(activeDir); err == nil {
				// Use directory modification time as creation time
				createTime := info.ModTime().Format(time.RFC3339)
				// Write initial history entry with directory creation time
				versionStr := fmt.Sprintf("v%d", version)
				record := fmt.Sprintf("to=%s;time=%s\n", versionStr, createTime)
				if err := os.WriteFile(historyFile, []byte(record), 0644); err != nil {
					fmt.Printf("Warning: failed to initialize history file: %v\n", err)
				}
			}
		}
	}

	fmt.Printf("Restore from %s complete\n", checkpointID)
	return nil
}

// ListCheckpoints returns a list of all available checkpoints
func (j *JuiceFS) ListCheckpoints(ctx context.Context) ([]CheckpointInfo, error) {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	// Check if checkpoints directory exists
	if _, err := os.Stat(checkpointsDir); os.IsNotExist(err) {
		// Return empty list if directory doesn't exist
		return []CheckpointInfo{}, nil
	}

	// Read all entries in checkpoints directory
	entries, err := os.ReadDir(checkpointsDir)
	if err != nil {
		return nil, fmt.Errorf("failed to read checkpoints directory: %w", err)
	}

	var checkpoints []CheckpointInfo
	for _, entry := range entries {
		if !entry.IsDir() {
			continue // Skip non-directories
		}

		// Skip the .latest_version symlink
		if entry.Name() == ".latest_version" {
			continue
		}

		// Skip the .latest symlink
		if entry.Name() == ".latest" {
			continue
		}

		info, err := entry.Info()
		if err != nil {
			continue // Skip entries we can't stat
		}

		checkpoint := CheckpointInfo{
			ID:         entry.Name(),
			CreateTime: info.ModTime(), // Use directory modification time as creation time
		}

		checkpoints = append(checkpoints, checkpoint)
	}

	return checkpoints, nil
}

// ListCheckpointsReverse returns checkpoints sorted by creation time in reverse order (newest first)
func (j *JuiceFS) ListCheckpointsReverse(ctx context.Context) ([]CheckpointInfo, error) {
	checkpoints, err := j.ListCheckpoints(ctx)
	if err != nil {
		return nil, err
	}

	// Sort by creation time in reverse order
	for i := 0; i < len(checkpoints)-1; i++ {
		for j := i + 1; j < len(checkpoints); j++ {
			if checkpoints[i].CreateTime.Before(checkpoints[j].CreateTime) {
				checkpoints[i], checkpoints[j] = checkpoints[j], checkpoints[i]
			}
		}
	}

	return checkpoints, nil
}

// ListCheckpointsWithActive returns checkpoints including the active state at the top
func (j *JuiceFS) ListCheckpointsWithActive(ctx context.Context) ([]CheckpointInfo, error) {
	// Get regular checkpoints first
	checkpoints, err := j.ListCheckpointsReverse(ctx)
	if err != nil {
		return nil, err
	}

	// Get active info
	activeInfo, err := j.GetCheckpoint(ctx, "active")
	if err != nil {
		// If we can't get active info, just return checkpoints
		return checkpoints, nil
	}

	// Mark the active checkpoint ID with " (active)" suffix
	activeInfo.ID = activeInfo.ID + " (active)"

	// Prepend active to the list
	result := make([]CheckpointInfo, 0, len(checkpoints)+1)
	result = append(result, *activeInfo)
	result = append(result, checkpoints...)

	return result, nil
}

// ListCheckpointsWithHistory returns checkpoints that have the specified version in their history
func (j *JuiceFS) ListCheckpointsWithHistory(ctx context.Context, version string) ([]string, error) {
	mountPath := filepath.Join(j.config.BaseDir, "data")

	// Also check active directory's history
	activeDir := filepath.Join(mountPath, "active")
	activeHistoryFile := filepath.Join(activeDir, ".history")

	var results []string
	searchPattern := fmt.Sprintf("to=%s;", version)

	// Check active directory history
	if data, err := os.ReadFile(activeHistoryFile); err == nil {
		lines := strings.Split(string(data), "\n")
		for _, line := range lines {
			line = strings.TrimSpace(line)
			if line != "" && strings.Contains(line, searchPattern) {
				results = append(results, fmt.Sprintf("active/.history: %s", line))
				break // Only report once per directory
			}
		}
	}

	// Check checkpoint directories
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	// Check if checkpoints directory exists
	if _, err := os.Stat(checkpointsDir); os.IsNotExist(err) {
		return results, nil // Return what we have from active
	}

	// Read all entries in checkpoints directory
	entries, err := os.ReadDir(checkpointsDir)
	if err != nil {
		return nil, fmt.Errorf("failed to read checkpoints directory: %w", err)
	}

	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}

		// Skip the .latest_version symlink
		if entry.Name() == ".latest_version" {
			continue
		}

		// Skip the .latest symlink
		if entry.Name() == ".latest" {
			continue
		}

		// Check history file in checkpoint
		historyFile := filepath.Join(checkpointsDir, entry.Name(), ".history")
		data, err := os.ReadFile(historyFile)
		if err != nil {
			continue // No history file
		}

		// Search for the version in history
		lines := strings.Split(string(data), "\n")
		for _, line := range lines {
			line = strings.TrimSpace(line)
			if line != "" && strings.Contains(line, searchPattern) {
				results = append(results, fmt.Sprintf("%s/.history: %s", entry.Name(), line))
				break // Only report the first match per checkpoint
			}
		}
	}

	return results, nil
}

// GetCheckpoint returns information about a specific checkpoint
func (j *JuiceFS) GetCheckpoint(ctx context.Context, checkpointID string) (*CheckpointInfo, error) {
	if checkpointID == "" {
		return nil, fmt.Errorf("checkpoint ID is required")
	}

	mountPath := filepath.Join(j.config.BaseDir, "data")

	// Handle special "active" checkpoint ID
	if checkpointID == "active" {
		// Get current version
		version, err := j.GetCurrentVersion()
		if err != nil {
			return nil, fmt.Errorf("failed to get current version: %w", err)
		}

		// Get active directory info
		activeDir := filepath.Join(mountPath, "active")
		info, err := os.Stat(activeDir)
		if err != nil {
			return nil, fmt.Errorf("failed to stat active directory: %w", err)
		}

		checkpoint := &CheckpointInfo{
			ID:         fmt.Sprintf("v%d", version),
			CreateTime: info.ModTime(),
		}

		// Read .history file if it exists
		historyFile := filepath.Join(activeDir, ".history")
		if data, err := os.ReadFile(historyFile); err == nil {
			lines := strings.Split(string(data), "\n")
			for _, line := range lines {
				line = strings.TrimSpace(line)
				if line != "" {
					checkpoint.History = append(checkpoint.History, line)
				}
			}
		}

		return checkpoint, nil
	}

	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	checkpointPath := filepath.Join(checkpointsDir, checkpointID)

	// Check if checkpoint exists
	info, err := os.Stat(checkpointPath)
	if os.IsNotExist(err) {
		return nil, fmt.Errorf("checkpoint %s does not exist", checkpointID)
	}
	if err != nil {
		return nil, fmt.Errorf("failed to stat checkpoint: %w", err)
	}

	if !info.IsDir() {
		return nil, fmt.Errorf("checkpoint %s is not a directory", checkpointID)
	}

	checkpoint := &CheckpointInfo{
		ID:         checkpointID,
		CreateTime: info.ModTime(),
	}

	// Read .history file if it exists
	historyFile := filepath.Join(checkpointPath, ".history")
	if data, err := os.ReadFile(historyFile); err == nil {
		lines := strings.Split(string(data), "\n")
		for _, line := range lines {
			line = strings.TrimSpace(line)
			if line != "" {
				checkpoint.History = append(checkpoint.History, line)
			}
		}
	}

	return checkpoint, nil
}

// GetCurrentVersion reads the current version from active/.version file
// Returns 0 if the file doesn't exist (initial state)
func (j *JuiceFS) GetCurrentVersion() (int, error) {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	versionFile := filepath.Join(mountPath, "active", ".version")

	// Open file for reading with shared lock
	file, err := os.Open(versionFile)
	if os.IsNotExist(err) {
		return 0, nil // Initial state
	}
	if err != nil {
		return 0, fmt.Errorf("failed to open version file: %w", err)
	}
	defer file.Close()

	// Get shared lock
	if err := syscall.Flock(int(file.Fd()), syscall.LOCK_SH); err != nil {
		return 0, fmt.Errorf("failed to acquire shared lock on version file: %w", err)
	}
	defer syscall.Flock(int(file.Fd()), syscall.LOCK_UN)

	// Read version
	var version int
	scanner := bufio.NewScanner(file)
	if scanner.Scan() {
		versionStr := strings.TrimPrefix(scanner.Text(), "v")
		version, err = strconv.Atoi(versionStr)
		if err != nil {
			return 0, fmt.Errorf("invalid version format in file: %s", scanner.Text())
		}
	}

	return version, nil
}

// initializeVersion creates the initial .version file if it doesn't exist
func (j *JuiceFS) initializeVersion() error {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	versionFile := filepath.Join(mountPath, "active", ".version")

	// Check if file already exists
	if _, err := os.Stat(versionFile); err == nil {
		return nil // Already initialized
	}

	// Create initial version file with v0
	if err := os.MkdirAll(filepath.Dir(versionFile), 0755); err != nil {
		return fmt.Errorf("failed to create active directory: %w", err)
	}

	return os.WriteFile(versionFile, []byte("v0\n"), 0644)
}

// appendToHistory appends a restore record to the .history file
func (j *JuiceFS) appendToHistory(toVersion string) error {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	historyFile := filepath.Join(mountPath, "active", ".history")

	// Open file for appending, create if not exists
	file, err := os.OpenFile(historyFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return fmt.Errorf("failed to open history file: %w", err)
	}
	defer file.Close()

	// Format: to=v9;time=<timestamp>
	timestamp := time.Now().Format(time.RFC3339)
	record := fmt.Sprintf("to=%s;time=%s\n", toVersion, timestamp)

	if _, err := file.WriteString(record); err != nil {
		return fmt.Errorf("failed to write to history file: %w", err)
	}

	return file.Sync()
}
