package juicefs

import (
	"context"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"time"
)

// DirectoryStats contains statistics about a directory
type DirectoryStats struct {
	FileCount    int
	DirCount     int
	TotalSize    int64
	LastModified time.Time
}

// CheckpointDivergence represents how much active has diverged from a checkpoint
type CheckpointDivergence struct {
	FileCountDiff int
	SizeDiff      int64
	TimeSinceMod  time.Duration
	Indicator     string
}

// GetDirectoryStats calculates statistics for a directory
func GetDirectoryStats(dirPath string) (*DirectoryStats, error) {
	return GetDirectoryStatsWithTimeout(dirPath, 5*time.Second)
}

// GetDirectoryStatsWithTimeout calculates statistics for a directory with a timeout
func GetDirectoryStatsWithTimeout(dirPath string, timeout time.Duration) (*DirectoryStats, error) {
	stats := &DirectoryStats{}
	
	// Create a context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()
	
	// Use a channel to signal completion
	done := make(chan error, 1)
	
	go func() {
		err := filepath.WalkDir(dirPath, func(path string, d fs.DirEntry, err error) error {
			// Check if context is cancelled
			select {
			case <-ctx.Done():
				return ctx.Err()
			default:
			}
			
			if err != nil {
				// Skip inaccessible files
				return nil
			}
			
			info, err := d.Info()
			if err != nil {
				// Skip files we can't stat
				return nil
			}
			
			if d.IsDir() {
				stats.DirCount++
			} else {
				stats.FileCount++
				stats.TotalSize += info.Size()
			}
			
			if info.ModTime().After(stats.LastModified) {
				stats.LastModified = info.ModTime()
			}
			
			return nil
		})
		done <- err
	}()
	
	// Wait for completion or timeout
	select {
	case err := <-done:
		if err != nil {
			return nil, fmt.Errorf("failed to walk directory: %w", err)
		}
	case <-ctx.Done():
		return nil, fmt.Errorf("directory stats calculation timed out after %v", timeout)
	}
	
	return stats, nil
}

// CalculateDivergence calculates how much the active directory has diverged from a checkpoint
func CalculateDivergence(activeStats, checkpointStats *DirectoryStats) *CheckpointDivergence {
	if activeStats == nil || checkpointStats == nil {
		return nil
	}
	
	fileCountDiff := activeStats.FileCount - checkpointStats.FileCount
	sizeDiff := activeStats.TotalSize - checkpointStats.TotalSize
	timeSinceMod := activeStats.LastModified.Sub(checkpointStats.LastModified)
	
	// Calculate divergence indicator
	indicator := getDivergenceIndicator(fileCountDiff, sizeDiff)
	
	return &CheckpointDivergence{
		FileCountDiff: fileCountDiff,
		SizeDiff:      sizeDiff,
		TimeSinceMod:  timeSinceMod,
		Indicator:     indicator,
	}
}

// getDivergenceIndicator returns a visual indicator of divergence level
func getDivergenceIndicator(fileCountDiff int, sizeDiff int64) string {
	// Calculate total change magnitude
	fileChange := abs(fileCountDiff)
	sizeChangeMB := abs64(sizeDiff) / (1024 * 1024)
	
	totalChange := fileChange + int(sizeChangeMB)
	
	if totalChange == 0 {
		return "✓ (no changes)"
	} else if totalChange < 10 {
		return "→ (minimal)"
	} else if totalChange < 100 {
		return "→→ (moderate)"  
	} else if totalChange < 1000 {
		return "→→→ (significant)"
	} else {
		return "→→→→ (major)"
	}
}

// abs returns absolute value for int
func abs(n int) int {
	if n < 0 {
		return -n
	}
	return n
}

// abs returns absolute value for int64
func abs64(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// FormatSize formats a size in bytes to human-readable format
func FormatSize(size int64) string {
	const unit = 1024
	if size < unit {
		return fmt.Sprintf("%d B", size)
	}
	div, exp := int64(unit), 0
	for n := size / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.2f %cB", float64(size)/float64(div), "KMGTPE"[exp])
}

// CheckpointInfoWithStats extends CheckpointInfo with statistics
type CheckpointInfoWithStats struct {
	CheckpointInfo
	Stats      *DirectoryStats
	Divergence *CheckpointDivergence // Only for active
}

// ListCheckpointsWithStats returns checkpoints with statistics and divergence info
func (j *JuiceFS) ListCheckpointsWithStats(ctx context.Context) ([]CheckpointInfoWithStats, error) {
	// Get regular checkpoints with active
	checkpoints, err := j.ListCheckpointsWithActive(ctx)
	if err != nil {
		return nil, err
	}
	
	mountPath := filepath.Join(j.config.BaseDir, "data")
	result := make([]CheckpointInfoWithStats, 0, len(checkpoints))
	
	var activeStats *DirectoryStats
	var lastCheckpointStats *DirectoryStats
	
	for i, cp := range checkpoints {
		cpWithStats := CheckpointInfoWithStats{
			CheckpointInfo: cp,
		}
		
		// Determine the directory path
		var dirPath string
		if cp.ID == "Current" {
			dirPath = filepath.Join(mountPath, "active")
		} else {
			dirPath = filepath.Join(mountPath, "checkpoints", cp.ID)
		}
		
		// Get stats if directory exists
		if _, err := os.Stat(dirPath); err == nil {
			stats, err := GetDirectoryStats(dirPath)
			if err == nil {
				cpWithStats.Stats = stats
				
				// Save active stats for divergence calculation
				if cp.ID == "Current" {
					activeStats = stats
				} else if i == 1 && activeStats != nil {
					// This is the most recent checkpoint after active
					lastCheckpointStats = stats
				}
			}
		}
		
		result = append(result, cpWithStats)
	}
	
	// Calculate divergence for active if we have both active and last checkpoint stats
	if len(result) > 0 && activeStats != nil && lastCheckpointStats != nil {
		if result[0].ID == "Current" {
			result[0].Divergence = CalculateDivergence(activeStats, lastCheckpointStats)
		}
	}
	
	return result, nil
}

// EnsureV0Checkpoint ensures a proper v0 checkpoint exists for empty environment
func (j *JuiceFS) EnsureV0Checkpoint(ctx context.Context) error {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	v0Path := filepath.Join(mountPath, "checkpoints", "v0")
	
	// Check if v0 already exists
	if _, err := os.Stat(v0Path); err == nil {
		j.logger.Info("v0 checkpoint already exists")
		return nil
	}
	
	// Create v0 directory
	if err := os.MkdirAll(v0Path, 0755); err != nil {
		return fmt.Errorf("failed to create v0 checkpoint directory: %w", err)
	}
	
	// Create basic structure for empty environment
	// This represents a clean, empty environment state
	dirs := []string{
		filepath.Join(v0Path, "fs"),
		filepath.Join(v0Path, "home"),
	}
	
	for _, dir := range dirs {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return fmt.Errorf("failed to create v0 subdirectory %s: %w", dir, err)
		}
	}
	
	// Create a marker file to indicate this is the initial checkpoint
	markerPath := filepath.Join(v0Path, ".v0-initial")
	if err := os.WriteFile(markerPath, []byte("Initial empty environment checkpoint\n"), 0644); err != nil {
		return fmt.Errorf("failed to create v0 marker file: %w", err)
	}
	
	j.logger.Info("Created v0 checkpoint for empty environment")
	return nil
}