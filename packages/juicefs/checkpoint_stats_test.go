package juicefs

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestGetDirectoryStats(t *testing.T) {
	// Create a temporary directory structure for testing
	tmpDir := t.TempDir()
	
	// Create some test files and directories
	testDirs := []string{
		filepath.Join(tmpDir, "dir1"),
		filepath.Join(tmpDir, "dir2"),
		filepath.Join(tmpDir, "dir1", "subdir"),
	}
	
	for _, dir := range testDirs {
		if err := os.MkdirAll(dir, 0755); err != nil {
			t.Fatalf("Failed to create test directory: %v", err)
		}
	}
	
	// Create test files with known sizes
	testFiles := map[string]string{
		filepath.Join(tmpDir, "file1.txt"):              "Hello World",
		filepath.Join(tmpDir, "dir1", "file2.txt"):      "Test content here",
		filepath.Join(tmpDir, "dir1", "subdir", "file3.txt"): "More test data",
	}
	
	totalExpectedSize := int64(0)
	for path, content := range testFiles {
		if err := os.WriteFile(path, []byte(content), 0644); err != nil {
			t.Fatalf("Failed to create test file: %v", err)
		}
		totalExpectedSize += int64(len(content))
	}
	
	// Get directory stats
	stats, err := GetDirectoryStats(tmpDir)
	if err != nil {
		t.Fatalf("GetDirectoryStats failed: %v", err)
	}
	
	// Verify stats
	if stats.FileCount != len(testFiles) {
		t.Errorf("Expected %d files, got %d", len(testFiles), stats.FileCount)
	}
	
	// Directory count includes the root directory
	expectedDirCount := len(testDirs) + 1
	if stats.DirCount != expectedDirCount {
		t.Errorf("Expected %d directories, got %d", expectedDirCount, stats.DirCount)
	}
	
	if stats.TotalSize != totalExpectedSize {
		t.Errorf("Expected total size %d, got %d", totalExpectedSize, stats.TotalSize)
	}
	
	if stats.LastModified.IsZero() {
		t.Error("LastModified time should not be zero")
	}
}

func TestCalculateDivergence(t *testing.T) {
	baseTime := time.Now()
	
	tests := []struct {
		name           string
		activeStats    *DirectoryStats
		checkpointStats *DirectoryStats
		expectedIndicator string
		expectedFileDiff int
		expectedSizeDiff int64
	}{
		{
			name: "no changes",
			activeStats: &DirectoryStats{
				FileCount:    10,
				DirCount:     5,
				TotalSize:    1000,
				LastModified: baseTime,
			},
			checkpointStats: &DirectoryStats{
				FileCount:    10,
				DirCount:     5,
				TotalSize:    1000,
				LastModified: baseTime,
			},
			expectedIndicator: "✓ (no changes)",
			expectedFileDiff:  0,
			expectedSizeDiff:  0,
		},
		{
			name: "minimal changes",
			activeStats: &DirectoryStats{
				FileCount:    15,
				DirCount:     5,
				TotalSize:    2000,
				LastModified: baseTime.Add(1 * time.Hour),
			},
			checkpointStats: &DirectoryStats{
				FileCount:    10,
				DirCount:     5,
				TotalSize:    1000,
				LastModified: baseTime,
			},
			expectedIndicator: "→ (minimal)",
			expectedFileDiff:  5,
			expectedSizeDiff:  1000,
		},
		{
			name: "moderate changes",
			activeStats: &DirectoryStats{
				FileCount:    60,
				DirCount:     10,
				TotalSize:    50*1024*1024, // 50MB
				LastModified: baseTime.Add(2 * time.Hour),
			},
			checkpointStats: &DirectoryStats{
				FileCount:    10,
				DirCount:     5,
				TotalSize:    1024*1024, // 1MB
				LastModified: baseTime,
			},
			expectedIndicator: "→→ (moderate)",
			expectedFileDiff:  50,
			expectedSizeDiff:  49*1024*1024,
		},
		{
			name: "significant changes",
			activeStats: &DirectoryStats{
				FileCount:    510,
				DirCount:     50,
				TotalSize:    500*1024*1024, // 500MB
				LastModified: baseTime.Add(3 * time.Hour),
			},
			checkpointStats: &DirectoryStats{
				FileCount:    10,
				DirCount:     5,
				TotalSize:    1024*1024, // 1MB
				LastModified: baseTime,
			},
			expectedIndicator: "→→→ (significant)",
			expectedFileDiff:  500,
			expectedSizeDiff:  499*1024*1024,
		},
		{
			name: "major changes",
			activeStats: &DirectoryStats{
				FileCount:    5010,
				DirCount:     500,
				TotalSize:    5000*1024*1024, // 5GB
				LastModified: baseTime.Add(4 * time.Hour),
			},
			checkpointStats: &DirectoryStats{
				FileCount:    10,
				DirCount:     5,
				TotalSize:    1024*1024, // 1MB
				LastModified: baseTime,
			},
			expectedIndicator: "→→→→ (major)",
			expectedFileDiff:  5000,
			expectedSizeDiff:  4999*1024*1024,
		},
		{
			name: "nil checkpoint stats",
			activeStats: &DirectoryStats{
				FileCount: 10,
			},
			checkpointStats: nil,
			expectedIndicator: "",
			expectedFileDiff:  0,
			expectedSizeDiff:  0,
		},
	}
	
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			divergence := CalculateDivergence(tt.activeStats, tt.checkpointStats)
			
			if tt.checkpointStats == nil {
				if divergence != nil {
					t.Error("Expected nil divergence for nil checkpoint stats")
				}
				return
			}
			
			if divergence.Indicator != tt.expectedIndicator {
				t.Errorf("Expected indicator %q, got %q", tt.expectedIndicator, divergence.Indicator)
			}
			
			if divergence.FileCountDiff != tt.expectedFileDiff {
				t.Errorf("Expected file diff %d, got %d", tt.expectedFileDiff, divergence.FileCountDiff)
			}
			
			if divergence.SizeDiff != tt.expectedSizeDiff {
				t.Errorf("Expected size diff %d, got %d", tt.expectedSizeDiff, divergence.SizeDiff)
			}
		})
	}
}

func TestFormatSize(t *testing.T) {
	tests := []struct {
		size     int64
		expected string
	}{
		{0, "0 B"},
		{500, "500 B"},
		{1024, "1.00 KB"},
		{1536, "1.50 KB"},
		{1048576, "1.00 MB"},
		{1073741824, "1.00 GB"},
		{1099511627776, "1.00 TB"},
		{2684354560, "2.50 GB"},
	}
	
	for _, tt := range tests {
		result := FormatSize(tt.size)
		if result != tt.expected {
			t.Errorf("FormatSize(%d) = %q, expected %q", tt.size, result, tt.expected)
		}
	}
}

func TestDivergenceIndicatorEdgeCases(t *testing.T) {
	tests := []struct {
		name         string
		fileCountDiff int
		sizeDiff     int64
		expected     string
	}{
		{
			name:         "negative file changes",
			fileCountDiff: -5,
			sizeDiff:     -1000,
			expected:     "→ (minimal)",
		},
		{
			name:         "files removed but size increased",
			fileCountDiff: -10,
			sizeDiff:     100*1024*1024, // 100MB increase
			expected:     "→→→ (significant)", // 10 files + 100MB = 110 total change
		},
		{
			name:         "boundary case minimal to moderate",
			fileCountDiff: 9,
			sizeDiff:     0,
			expected:     "→ (minimal)",
		},
		{
			name:         "boundary case minimal to moderate exact",
			fileCountDiff: 10,
			sizeDiff:     0,
			expected:     "→→ (moderate)",
		},
	}
	
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			indicator := getDivergenceIndicator(tt.fileCountDiff, tt.sizeDiff)
			if indicator != tt.expected {
				t.Errorf("Expected indicator %q, got %q", tt.expected, indicator)
			}
		})
	}
}