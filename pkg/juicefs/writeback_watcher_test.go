package juicefs

import (
	"context"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// TestWritebackWatcher_Basic tests basic file tracking functionality
func TestWritebackWatcher_Basic(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	// Start watcher
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to initialize
	time.Sleep(100 * time.Millisecond)

	// Initially should have no pending files
	if count := watcher.GetPendingCount(); count != 0 {
		t.Errorf("Expected 0 pending files, got %d", count)
	}

	// Create a file in rawstaging
	testFile := filepath.Join(rawstagingDir, "test-chunk-1")
	if err := os.WriteFile(testFile, []byte("test data"), 0644); err != nil {
		t.Fatal(err)
	}

	// Wait for watcher to detect the file
	time.Sleep(200 * time.Millisecond)

	// Should now have 1 pending file
	if count := watcher.GetPendingCount(); count != 1 {
		t.Errorf("Expected 1 pending file after creation, got %d", count)
	}

	// Remove the file (simulating upload completion)
	if err := os.Remove(testFile); err != nil {
		t.Fatal(err)
	}

	// Wait for watcher to detect the removal
	time.Sleep(200 * time.Millisecond)

	// Should be back to 0 pending files
	if count := watcher.GetPendingCount(); count != 0 {
		t.Errorf("Expected 0 pending files after removal, got %d", count)
	}
}

// TestWritebackWatcher_MultipleFiles tests tracking multiple files
func TestWritebackWatcher_MultipleFiles(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	// Start watcher
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to initialize
	time.Sleep(100 * time.Millisecond)

	// Create multiple files
	numFiles := 5
	files := make([]string, numFiles)
	for i := 0; i < numFiles; i++ {
		files[i] = filepath.Join(rawstagingDir, "chunk-"+string(rune('A'+i)))
		if err := os.WriteFile(files[i], []byte("data"), 0644); err != nil {
			t.Fatal(err)
		}
		time.Sleep(50 * time.Millisecond) // Small delay between files
	}

	// Wait for all detections
	time.Sleep(200 * time.Millisecond)

	// Should have all files pending
	if count := watcher.GetPendingCount(); count != int64(numFiles) {
		t.Errorf("Expected %d pending files, got %d", numFiles, count)
	}

	// Remove files one by one
	for i, file := range files {
		if err := os.Remove(file); err != nil {
			t.Fatal(err)
		}
		time.Sleep(100 * time.Millisecond)

		expectedRemaining := int64(numFiles - i - 1)
		if count := watcher.GetPendingCount(); count != expectedRemaining {
			t.Errorf("After removing file %d, expected %d pending, got %d", i, expectedRemaining, count)
		}
	}
}

// TestWritebackWatcher_WhenFlushed tests the WhenFlushed blocking method
func TestWritebackWatcher_WhenFlushed(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	// Start watcher
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to initialize
	time.Sleep(100 * time.Millisecond)

	// WhenFlushed should return immediately when no pending files
	flushCtx, flushCancel := context.WithTimeout(context.Background(), 1*time.Second)
	defer flushCancel()

	if err := watcher.WhenFlushed(flushCtx); err != nil {
		t.Errorf("WhenFlushed should not error when already flushed: %v", err)
	}

	// Create a file
	testFile := filepath.Join(rawstagingDir, "test-chunk")
	if err := os.WriteFile(testFile, []byte("test"), 0644); err != nil {
		t.Fatal(err)
	}
	time.Sleep(200 * time.Millisecond)

	// Start goroutine to wait for flush
	flushed := make(chan error, 1)
	go func() {
		flushCtx := context.Background()
		flushed <- watcher.WhenFlushed(flushCtx)
	}()

	// Should not be flushed yet
	select {
	case <-flushed:
		t.Error("WhenFlushed returned before file was removed")
	case <-time.After(300 * time.Millisecond):
		// Expected - still waiting
	}

	// Remove the file
	if err := os.Remove(testFile); err != nil {
		t.Fatal(err)
	}

	// Should now complete
	select {
	case err := <-flushed:
		if err != nil {
			t.Errorf("WhenFlushed returned error: %v", err)
		}
	case <-time.After(1 * time.Second):
		t.Error("WhenFlushed did not complete after file removal")
	}
}

// TestWritebackWatcher_WhenFlushedTimeout tests timeout handling
func TestWritebackWatcher_WhenFlushedTimeout(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	// Start watcher
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to initialize
	time.Sleep(100 * time.Millisecond)

	// Create a file that we won't remove
	testFile := filepath.Join(rawstagingDir, "stuck-chunk")
	if err := os.WriteFile(testFile, []byte("test"), 0644); err != nil {
		t.Fatal(err)
	}
	time.Sleep(200 * time.Millisecond)

	// WhenFlushed with short timeout should timeout
	flushCtx, flushCancel := context.WithTimeout(context.Background(), 500*time.Millisecond)
	defer flushCancel()

	err = watcher.WhenFlushed(flushCtx)
	if err == nil {
		t.Error("Expected timeout error, got nil")
	}
	if err != context.DeadlineExceeded {
		t.Errorf("Expected DeadlineExceeded error, got: %v", err)
	}
}

// TestWritebackWatcher_ExistingFiles tests detection of files that exist before watcher starts
func TestWritebackWatcher_ExistingFiles(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create files BEFORE starting watcher
	numFiles := 3
	for i := 0; i < numFiles; i++ {
		testFile := filepath.Join(rawstagingDir, "existing-"+string(rune('A'+i)))
		if err := os.WriteFile(testFile, []byte("data"), 0644); err != nil {
			t.Fatal(err)
		}
	}

	// Now create and start watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to scan existing files
	time.Sleep(200 * time.Millisecond)

	// Should detect all existing files
	if count := watcher.GetPendingCount(); count != int64(numFiles) {
		t.Errorf("Expected %d existing files to be detected, got %d", numFiles, count)
	}
}

// TestWritebackWatcher_DelayedDirectory tests watcher when rawstaging dir doesn't exist initially
func TestWritebackWatcher_DelayedDirectory(t *testing.T) {
	// Create cache directory but NOT the rawstaging subdirectory yet
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")

	if err := os.MkdirAll(cacheDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher (rawstaging doesn't exist yet)
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to start and attempt first scan
	time.Sleep(200 * time.Millisecond)

	// Now create the directory structure
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")
	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create a file
	testFile := filepath.Join(rawstagingDir, "late-chunk")
	if err := os.WriteFile(testFile, []byte("data"), 0644); err != nil {
		t.Fatal(err)
	}

	// Wait for watcher to discover directory and file (retry is every 5 seconds, but file events might trigger sooner)
	// This test might take up to 6 seconds
	found := false
	for i := 0; i < 12; i++ {
		time.Sleep(500 * time.Millisecond)
		if watcher.GetPendingCount() > 0 {
			found = true
			break
		}
	}

	if !found {
		t.Error("Watcher did not detect file in delayed rawstaging directory")
	}
}

// TestWritebackWatcher_Stop tests clean shutdown
func TestWritebackWatcher_Stop(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}

	// Give watcher time to initialize
	time.Sleep(100 * time.Millisecond)

	// Stop should complete quickly
	stopDone := make(chan error, 1)
	go func() {
		stopDone <- watcher.Stop()
	}()

	select {
	case err := <-stopDone:
		if err != nil {
			t.Errorf("Stop returned error: %v", err)
		}
	case <-time.After(2 * time.Second):
		t.Error("Stop did not complete within 2 seconds")
	}

	// Wait should return immediately after Stop
	waitDone := make(chan struct{})
	go func() {
		watcher.Wait()
		close(waitDone)
	}()

	select {
	case <-waitDone:
		// Success
	case <-time.After(100 * time.Millisecond):
		t.Error("Wait did not return after Stop completed")
	}
}

// TestWritebackWatcher_StaleZeroByteFile tests detection of stale zero-byte files
func TestWritebackWatcher_StaleZeroByteFile(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create a zero-byte file with old timestamp (5 minutes ago)
	staleFile := filepath.Join(rawstagingDir, "stale-chunk")
	if err := os.WriteFile(staleFile, []byte{}, 0644); err != nil {
		t.Fatal(err)
	}

	// Set file time to 5 minutes ago
	oldTime := time.Now().Add(-5 * time.Minute)
	if err := os.Chtimes(staleFile, oldTime, oldTime); err != nil {
		t.Fatal(err)
	}

	// Create a recent zero-byte file (should not warn)
	recentFile := filepath.Join(rawstagingDir, "recent-chunk")
	if err := os.WriteFile(recentFile, []byte{}, 0644); err != nil {
		t.Fatal(err)
	}

	// Create a non-zero file with old timestamp (should not warn)
	nonZeroFile := filepath.Join(rawstagingDir, "nonzero-chunk")
	if err := os.WriteFile(nonZeroFile, []byte("data"), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.Chtimes(nonZeroFile, oldTime, oldTime); err != nil {
		t.Fatal(err)
	}

	// Capture log output to verify warning
	var logOutput strings.Builder
	logger := slog.New(slog.NewTextHandler(&logOutput, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	// Give watcher time to scan and detect the stale file
	time.Sleep(300 * time.Millisecond)

	// Check that warning was logged for stale zero-byte file
	output := logOutput.String()
	if !strings.Contains(output, "stale zero-byte file") {
		t.Error("Expected warning about stale zero-byte file, but none was logged")
	}

	// Count actual warnings (level=WARN) for each file
	staleChunkWarnings := strings.Count(output, "stale-chunk") - strings.Count(output, `file=stale-chunk size=`)
	recentChunkWarnings := strings.Count(output, "recent-chunk") - strings.Count(output, `file=recent-chunk size=`)
	nonZeroWarnings := strings.Count(output, "nonzero-chunk") - strings.Count(output, `file=nonzero-chunk size=`)

	// stale-chunk should appear in a warning (beyond the add event debug log)
	if staleChunkWarnings < 1 {
		t.Error("Expected warning to mention stale-chunk filename")
	}

	// recent-chunk and nonzero-chunk should NOT appear in warnings beyond their add event
	if recentChunkWarnings > 0 {
		t.Error("Should not warn about recent zero-byte file")
	}
	if nonZeroWarnings > 0 {
		t.Error("Should not warn about non-zero file")
	}
}

// TestWritebackWatcher_StaleFilePeriodicCheck tests periodic stale file checking
func TestWritebackWatcher_StaleFilePeriodicCheck(t *testing.T) {
	// This test would take 2+ minutes to test the periodic check naturally,
	// so we just verify the checkForStaleFiles method works
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create a file that becomes stale
	testFile := filepath.Join(rawstagingDir, "becoming-stale")
	if err := os.WriteFile(testFile, []byte{}, 0644); err != nil {
		t.Fatal(err)
	}

	var logOutput strings.Builder
	logger := slog.New(slog.NewTextHandler(&logOutput, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	time.Sleep(200 * time.Millisecond)

	// File is recent, should not warn
	watcher.checkForStaleFiles()
	if strings.Contains(logOutput.String(), "stale zero-byte") {
		t.Error("Should not warn about file that's not stale yet")
	}

	// Make file old
	oldTime := time.Now().Add(-5 * time.Minute)
	if err := os.Chtimes(testFile, oldTime, oldTime); err != nil {
		t.Fatal(err)
	}

	// Now it should warn
	logOutput.Reset()
	watcher.checkForStaleFiles()

	time.Sleep(100 * time.Millisecond)

	if !strings.Contains(logOutput.String(), "stale zero-byte") {
		t.Error("Expected warning about stale file after manual check")
	}
}

// TestWritebackWatcher_WaitForUploads tests the WaitForUploads method
func TestWritebackWatcher_WaitForUploads(t *testing.T) {
	// Create temporary cache directory structure
	tmpDir := t.TempDir()
	cacheDir := filepath.Join(tmpDir, "cache")
	uuidDir := filepath.Join(cacheDir, "test-uuid")
	rawstagingDir := filepath.Join(uuidDir, "rawstaging")

	if err := os.MkdirAll(rawstagingDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create watcher
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{Level: slog.LevelDebug}))
	ctx := tap.WithLogger(context.Background(), logger)

	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		t.Fatal(err)
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	if err := watcher.Start(ctx); err != nil {
		t.Fatal(err)
	}
	defer watcher.Stop()

	time.Sleep(100 * time.Millisecond)

	// Create files
	file1 := filepath.Join(rawstagingDir, "chunk-1")
	file2 := filepath.Join(rawstagingDir, "chunk-2")

	if err := os.WriteFile(file1, []byte("data"), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(file2, []byte("data"), 0644); err != nil {
		t.Fatal(err)
	}
	time.Sleep(200 * time.Millisecond)

	// Start waiting for uploads
	uploadsDone := make(chan struct {
		count int64
		err   error
	}, 1)

	go func() {
		count, err := watcher.WaitForUploads(context.Background())
		uploadsDone <- struct {
			count int64
			err   error
		}{count, err}
	}()

	// Should still be waiting
	select {
	case <-uploadsDone:
		t.Error("WaitForUploads completed before files were removed")
	case <-time.After(300 * time.Millisecond):
		// Expected
	}

	// Remove files
	os.Remove(file1)
	time.Sleep(100 * time.Millisecond)
	os.Remove(file2)

	// Should now complete
	select {
	case result := <-uploadsDone:
		if result.err != nil {
			t.Errorf("WaitForUploads returned error: %v", result.err)
		}
		if result.count != 2 {
			t.Errorf("Expected initial count of 2, got %d", result.count)
		}
	case <-time.After(2 * time.Second):
		t.Error("WaitForUploads did not complete after files removed")
	}
}
