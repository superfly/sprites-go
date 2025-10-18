package juicefs

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/fsnotify/fsnotify"
	"github.com/superfly/sprite-env/pkg/tap"
)

// WritebackWatcher monitors the JuiceFS rawstaging directory for pending uploads
// When files appear in rawstaging, they are waiting to be uploaded based on --upload-delay
// We track these files so JuiceFS.Stop() can wait for all uploads to complete before unmounting
type WritebackWatcher struct {
	logger         *slog.Logger
	cacheDir       string // Cache directory to search for rawstaging
	rawstagingPath string
	watcher        *fsnotify.Watcher
	stopCh         chan struct{}
	stoppedCh      chan struct{} // closed when processEvents exits
	stateDoneCh    chan struct{} // closed when stateManager exits
	readyCh        chan struct{} // closed when rawstaging directory is found and being watched

	// State management via channels (owned by state goroutine)
	cmdCh   chan watcherCmd
	countCh chan int64 // for responding to count queries
}

// watcherCmd represents commands sent to the state goroutine
type watcherCmd struct {
	typ       cmdType
	filename  string
	fileSize  int64                // file size for add/update operations
	timestamp time.Time            // timestamp for add/update operations
	respond   chan<- countResponse // optional response channel
}

type countResponse struct {
	total               int64
	nonZero             int64
	mostRecentTimestamp time.Time
}

type cmdType int

const (
	cmdAddFile cmdType = iota
	cmdRemoveFile
	cmdGetCount
	cmdGetNonZeroCount
	cmdCheckStale
	cmdInitFiles
)

// isIgnoredWritebackFile returns true for files we should not track in writeback
// Currently ignores temporary files with a .tmp suffix.
func isIgnoredWritebackFile(name string) bool {
	return strings.HasSuffix(name, ".tmp")
}

// NewWritebackWatcher creates a new writeback directory watcher
func NewWritebackWatcher(ctx context.Context, cacheDir string) (*WritebackWatcher, error) {
	logger := tap.Logger(ctx)
	logger = logger.With("source", "juicefs", "method", "monitor")

	// The rawstaging directory is inside the cache directory
	// JuiceFS creates it dynamically, so we need to find it
	// The structure is cache/<uuid>/rawstaging
	rawstagingPath, err := findRawstagingDir(cacheDir)
	if err != nil {
		// Directory might not exist yet - this is normal during mount initialization
		// JuiceFS creates the cache structure after mount completes
		logger.Info("Writeback directory not found yet, will watch cache directory and wait",
			"cacheDir", cacheDir)
	} else {
		logger.Info("Found writeback directory", "path", rawstagingPath)
	}

	w := &WritebackWatcher{
		logger:         logger,
		cacheDir:       cacheDir,
		rawstagingPath: rawstagingPath,
		stopCh:         make(chan struct{}),
		stoppedCh:      make(chan struct{}),
		stateDoneCh:    make(chan struct{}),
		readyCh:        make(chan struct{}),
		cmdCh:          make(chan watcherCmd, 100),
		countCh:        make(chan int64, 1),
	}

	return w, nil
}

// findRawstagingDir locates the rawstaging directory within the cache
func findRawstagingDir(cacheDir string) (string, error) {
	// Look for cache/<uuid>/rawstaging pattern
	entries, err := os.ReadDir(cacheDir)
	if err != nil {
		return "", fmt.Errorf("failed to read cache directory: %w", err)
	}

	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		// Check if this directory has a rawstaging subdirectory
		rawstagingPath := filepath.Join(cacheDir, entry.Name(), "rawstaging")
		if stat, err := os.Stat(rawstagingPath); err == nil && stat.IsDir() {
			return rawstagingPath, nil
		}
	}

	return "", fmt.Errorf("rawstaging directory not found in cache")
}

// Start begins monitoring the writeback directory
func (w *WritebackWatcher) Start(ctx context.Context) error {
	var err error
	w.watcher, err = fsnotify.NewWatcher()
	if err != nil {
		close(w.stoppedCh)
		return fmt.Errorf("failed to create fsnotify watcher: %w", err)
	}

	// If we found the rawstaging dir, start watching it recursively
	if w.rawstagingPath != "" {
		// Add recursive watches for the directory tree
		if err := w.addRecursiveWatch(w.rawstagingPath); err != nil {
			w.watcher.Close()
			close(w.stoppedCh)
			return fmt.Errorf("failed to watch writeback directory: %w", err)
		}
		w.logger.Info("Started watching writeback directory recursively", "path", w.rawstagingPath)

		// Count any existing files in the directory tree
		if err := w.scanExistingFiles(); err != nil {
			w.logger.Warn("Failed to scan existing files", "error", err)
		}

		// Signal that watcher is ready
		close(w.readyCh)
	} else {
		// If not found, also watch the cache directory so we can detect when rawstaging appears
		if err := w.watcher.Add(w.cacheDir); err != nil {
			w.watcher.Close()
			close(w.stoppedCh)
			return fmt.Errorf("failed to watch cache directory: %w", err)
		}
		w.logger.Info("Watching cache directory for rawstaging creation", "cacheDir", w.cacheDir)
	}
	// processEvents will signal ready when rawstaging is found

	// Start the state management goroutine
	go w.stateManager(ctx)

	// Start the event processing goroutine
	go w.processEvents(ctx)

	return nil
}

// addRecursiveWatch adds watches for a directory and all its subdirectories
func (w *WritebackWatcher) addRecursiveWatch(root string) error {
	return filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() {
			if err := w.watcher.Add(path); err != nil {
				return fmt.Errorf("failed to watch %s: %w", path, err)
			}
			w.logger.Debug("Added watch for directory", "path", path)
		}
		return nil
	})
}

// scanExistingFiles counts any files already in writeback when we start
func (w *WritebackWatcher) scanExistingFiles() error {
	// Walk the entire tree to find all files
	err := filepath.Walk(w.rawstagingPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if !info.IsDir() {
			filename := filepath.Base(path)
			if isIgnoredWritebackFile(filename) {
				return nil
			}
			select {
			case w.cmdCh <- watcherCmd{typ: cmdAddFile, filename: filename, fileSize: info.Size(), timestamp: info.ModTime()}:
			case <-w.stopCh:
				return fmt.Errorf("stopped")
			}
		}
		return nil
	})

	if err != nil && err.Error() != "stopped" {
		return err
	}

	// Check for stale files
	w.checkForStaleFiles()

	return nil
}

// checkStaleZeroByteFile checks if a file is zero bytes and older than threshold
func (w *WritebackWatcher) checkStaleZeroByteFile(filename string, now time.Time, threshold time.Duration) {
	filePath := filepath.Join(w.rawstagingPath, filename)
	info, err := os.Stat(filePath)
	if err != nil {
		return
	}

	// Check if file is zero bytes
	if info.Size() == 0 {
		age := now.Sub(info.ModTime())
		if age > threshold {
			w.logger.Warn("Found stale zero-byte file in writeback",
				"file", filename,
				"age", age.String(),
				"modTime", info.ModTime())
		}
	}
}

// checkForStaleFiles triggers a stale file check
func (w *WritebackWatcher) checkForStaleFiles() {
	select {
	case w.cmdCh <- watcherCmd{typ: cmdCheckStale}:
	case <-w.stopCh:
	}
}

// countBySize categorizes tracked files by size (using cached sizes)
// Returns (zeroByteCount, nonZeroCount)
func countBySize(fileSizes map[string]int64) (int64, int64) {
	var zeroCount, nonZeroCount int64
	for _, size := range fileSizes {
		if size == 0 {
			zeroCount++
		} else {
			nonZeroCount++
		}
	}
	return zeroCount, nonZeroCount
}

// stateManager owns all state and processes commands on a single goroutine
func (w *WritebackWatcher) stateManager(ctx context.Context) {
	defer close(w.stateDoneCh)

	fileSizes := make(map[string]int64) // filename -> size
	var pendingCount int64
	var totalUploaded int64           // lifetime counter of uploaded files
	var mostRecentTimestamp time.Time // timestamp of most recent file added

	// Setup periodic logging ticker
	logTicker := time.NewTicker(15 * time.Second)
	defer logTicker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-w.stopCh:
			return
		case <-logTicker.C:
			if pendingCount > 0 {
				// Count zero-length files using cached sizes
				zeroCount, nonZeroCount := countBySize(fileSizes)
				w.logger.Debug("Writeback status",
					"pendingFiles", nonZeroCount,
					"zeroByteFiles", zeroCount,
					"totalUploaded", totalUploaded,
					"mostRecentFile", mostRecentTimestamp.Format(time.RFC3339))
			}
		case cmd := <-w.cmdCh:
			switch cmd.typ {
			case cmdAddFile:
				if _, exists := fileSizes[cmd.filename]; !exists {
					fileSizes[cmd.filename] = cmd.fileSize
					pendingCount++
					if !cmd.timestamp.IsZero() {
						mostRecentTimestamp = cmd.timestamp
					}
					w.logger.Debug("File added to writeback",
						"file", cmd.filename,
						"size", cmd.fileSize,
						"pendingCount", pendingCount)
				} else {
					// File exists, maybe size changed - update it
					fileSizes[cmd.filename] = cmd.fileSize
					if !cmd.timestamp.IsZero() {
						mostRecentTimestamp = cmd.timestamp
					}
				}

			case cmdRemoveFile:
				if _, exists := fileSizes[cmd.filename]; exists {
					delete(fileSizes, cmd.filename)
					pendingCount--
					totalUploaded++
					w.logger.Debug("File removed from writeback (uploaded)",
						"file", cmd.filename,
						"pendingCount", pendingCount,
						"totalUploaded", totalUploaded)
				}

			case cmdGetCount:
				if cmd.respond != nil {
					zeroCount, nonZeroCount := countBySize(fileSizes)
					select {
					case cmd.respond <- countResponse{total: pendingCount, nonZero: nonZeroCount, mostRecentTimestamp: mostRecentTimestamp}:
					case <-w.stopCh:
					}
					w.logger.Debug("Count requested",
						"total", pendingCount,
						"nonZero", nonZeroCount,
						"zero", zeroCount)
				}

			case cmdGetNonZeroCount:
				if cmd.respond != nil {
					_, nonZeroCount := countBySize(fileSizes)
					select {
					case cmd.respond <- countResponse{total: pendingCount, nonZero: nonZeroCount, mostRecentTimestamp: mostRecentTimestamp}:
					case <-w.stopCh:
					}
				}

			case cmdCheckStale:
				// Check all pending files for stale zero-byte files
				if len(fileSizes) > 0 {
					now := time.Now()
					staleThreshold := 3 * time.Minute
					for filename := range fileSizes {
						w.checkStaleZeroByteFile(filename, now, staleThreshold)
					}
				}
			}
		}
	}
}

// processEvents handles fsnotify events
func (w *WritebackWatcher) processEvents(ctx context.Context) {
	defer close(w.stoppedCh)
	defer w.watcher.Close()

	// Setup retry ticker if rawstaging directory not found yet
	var retryTicker *time.Ticker
	var retryTickerCh <-chan time.Time
	if w.rawstagingPath == "" {
		w.logger.Info("Writeback directory not ready, will retry every 5 seconds")
		retryTicker = time.NewTicker(5 * time.Second)
		retryTickerCh = retryTicker.C
		defer retryTicker.Stop()
	}

	// Setup periodic stale file checker (runs every 2 minutes)
	staleCheckTicker := time.NewTicker(2 * time.Minute)
	defer staleCheckTicker.Stop()
	staleCheckCh := staleCheckTicker.C

	for {
		select {
		case <-ctx.Done():
			w.logger.Info("Writeback watcher stopped due to context cancellation")
			return

		case <-w.stopCh:
			w.logger.Info("Writeback watcher stopped")
			return

		case <-staleCheckCh:
			// Periodically check for stale zero-byte files
			if w.rawstagingPath != "" {
				w.checkForStaleFiles()
			}

		case <-retryTickerCh:
			// Try to find the rawstaging directory
			if w.rawstagingPath == "" {
				rawstagingPath, err := findRawstagingDir(w.cacheDir)
				if err == nil {
					w.logger.Info("Found writeback directory on retry", "path", rawstagingPath)
					w.rawstagingPath = rawstagingPath

					// Start watching it recursively
					if err := w.addRecursiveWatch(w.rawstagingPath); err != nil {
						w.logger.Error("Failed to watch writeback directory", "error", err)
						w.rawstagingPath = "" // Reset so we keep retrying
					} else {
						w.logger.Info("Started watching writeback directory recursively")
						// Stop the retry ticker
						if retryTicker != nil {
							retryTicker.Stop()
							retryTickerCh = nil
						}
						// Scan for existing files
						if err := w.scanExistingFiles(); err != nil {
							w.logger.Warn("Failed to scan existing files", "error", err)
						}
						// Signal that watcher is ready
						close(w.readyCh)
					}
				}
			}

		case err, ok := <-w.watcher.Errors:
			if !ok {
				w.logger.Warn("Watcher error channel closed")
				return
			}
			w.logger.Error("Watcher error", "error", err)

		case event, ok := <-w.watcher.Events:
			if !ok {
				w.logger.Warn("Watcher event channel closed")
				return
			}

			w.handleEvent(event)
		}
	}
}

// handleEvent processes a single fsnotify event
func (w *WritebackWatcher) handleEvent(event fsnotify.Event) {
	filename := filepath.Base(event.Name)

	// Check if this is a directory creation (need to watch new subdirs)
	if event.Op&fsnotify.Create == fsnotify.Create {
		if info, err := os.Stat(event.Name); err == nil && info.IsDir() {
			// If we're waiting for rawstaging, check if this might be it or a parent
			if w.rawstagingPath == "" {
				// Check if this is the rawstaging directory (cache/<uuid>/rawstaging)
				if filename == "rawstaging" && filepath.HasPrefix(event.Name, w.cacheDir) {
					w.logger.Info("Detected rawstaging directory creation via fsnotify", "path", event.Name)
					w.rawstagingPath = event.Name

					// Add recursive watch for rawstaging and its subdirs
					if err := w.addRecursiveWatch(w.rawstagingPath); err != nil {
						w.logger.Error("Failed to watch rawstaging directory", "error", err)
						w.rawstagingPath = "" // Reset
						return
					}

					// Scan for existing files
					if err := w.scanExistingFiles(); err != nil {
						w.logger.Warn("Failed to scan existing files", "error", err)
					}

					// Signal that watcher is ready
					close(w.readyCh)
					w.logger.Info("Writeback watcher is now ready")
					return
				}

				// If this is a UUID directory under cache, watch it so we can detect rawstaging creation
				if filepath.Dir(event.Name) == w.cacheDir {
					if err := w.watcher.Add(event.Name); err != nil {
						w.logger.Warn("Failed to watch UUID directory", "path", event.Name, "error", err)
					} else {
						w.logger.Debug("Added watch for UUID directory", "path", event.Name)
					}
				}
				return
			}

			// For other directories, just add watch if we're already watching rawstaging
			if filepath.HasPrefix(event.Name, w.rawstagingPath) {
				if err := w.watcher.Add(event.Name); err != nil {
					w.logger.Warn("Failed to watch new subdirectory", "path", event.Name, "error", err)
				} else {
					w.logger.Debug("Added watch for new subdirectory", "path", event.Name)
				}
			}
			return // Don't treat directory as a file
		}
	}

	// Ignore temporary files we don't want to track
	if isIgnoredWritebackFile(filename) {
		return
	}

	switch {
	case event.Op&fsnotify.Create == fsnotify.Create:
		// New file created - get its size and timestamp
		size := int64(0)
		timestamp := time.Now()
		if info, err := os.Stat(event.Name); err == nil {
			size = info.Size()
			timestamp = info.ModTime()
		}
		select {
		case w.cmdCh <- watcherCmd{typ: cmdAddFile, filename: filename, fileSize: size, timestamp: timestamp}:
		case <-w.stopCh:
		}

	case event.Op&fsnotify.Write == fsnotify.Write:
		// File written - update size (file might grow from 0 to non-zero)
		size := int64(0)
		timestamp := time.Now()
		if info, err := os.Stat(event.Name); err == nil {
			size = info.Size()
			timestamp = info.ModTime()
		}
		select {
		case w.cmdCh <- watcherCmd{typ: cmdAddFile, filename: filename, fileSize: size, timestamp: timestamp}:
		case <-w.stopCh:
		}

	case event.Op&fsnotify.Remove == fsnotify.Remove:
		// File removed - upload completed
		select {
		case w.cmdCh <- watcherCmd{typ: cmdRemoveFile, filename: filename}:
		case <-w.stopCh:
		}

	case event.Op&fsnotify.Rename == fsnotify.Rename:
		// File renamed away - treat as removal
		select {
		case w.cmdCh <- watcherCmd{typ: cmdRemoveFile, filename: filename}:
		case <-w.stopCh:
		}
	}
}

// Stop stops the watcher
func (w *WritebackWatcher) Stop() error {
	// Signal stop
	select {
	case <-w.stopCh:
		// Already stopped
	default:
		close(w.stopCh)
	}

	// Wait for both goroutines to exit
	<-w.stoppedCh   // processEvents goroutine
	<-w.stateDoneCh // stateManager goroutine

	// Don't call GetPendingCount() here as it would try to send to cmdCh
	// which might block if stateManager has already exited
	// The pending count is already logged periodically by stateManager

	return nil
}

// Wait blocks until the watcher stops
func (w *WritebackWatcher) Wait() {
	<-w.stoppedCh
}

// WaitUntilReady blocks until the watcher has found the rawstaging directory
// Returns immediately if already ready, or when context is cancelled
func (w *WritebackWatcher) WaitUntilReady(ctx context.Context) error {
	select {
	case <-w.readyCh:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	case <-w.stopCh:
		return fmt.Errorf("watcher stopped before becoming ready")
	}
}

// GetPendingCount returns the number of files currently pending upload
func (w *WritebackWatcher) GetPendingCount() int64 {
	respCh := make(chan countResponse, 1)
	select {
	case w.cmdCh <- watcherCmd{typ: cmdGetCount, respond: respCh}:
		select {
		case resp := <-respCh:
			return resp.total
		case <-w.stopCh:
			return 0
		}
	case <-w.stopCh:
		return 0
	}
}

// GetNonZeroPendingCount returns the number of non-zero-byte files pending upload
func (w *WritebackWatcher) GetNonZeroPendingCount() int64 {
	respCh := make(chan countResponse, 1)
	select {
	case w.cmdCh <- watcherCmd{typ: cmdGetNonZeroCount, respond: respCh}:
		select {
		case resp := <-respCh:
			return resp.nonZero
		case <-w.stopCh:
			return 0
		}
	case <-w.stopCh:
		return 0
	}
}

// LogStats logs the current writeback status (pending files and zero-byte files)
func (w *WritebackWatcher) LogStats() {
	if w.rawstagingPath == "" {
		return
	}

	respCh := make(chan countResponse, 1)
	select {
	case w.cmdCh <- watcherCmd{typ: cmdGetCount, respond: respCh}:
		select {
		case resp := <-respCh:
			zeroCount := resp.total - resp.nonZero
			w.logger.Info("Writeback status",
				"pendingFiles", resp.nonZero,
				"zeroByteFiles", zeroCount,
				"mostRecentFile", resp.mostRecentTimestamp.Format(time.RFC3339))
		case <-w.stopCh:
		}
	case <-w.stopCh:
	}
}

// WaitForUploads blocks until all non-zero pending uploads are complete or context is cancelled
// Zero-length files are considered flushed and won't block the wait
// Returns the number of files that were pending when we started waiting
func (w *WritebackWatcher) WaitForUploads(ctx context.Context) (int64, error) {
	initialCount := w.GetPendingCount()
	nonZeroCount := w.GetNonZeroPendingCount()

	if nonZeroCount == 0 {
		return 0, nil
	}

	w.logger.Info("Waiting for pending uploads to complete",
		"pendingCount", initialCount,
		"nonZeroCount", nonZeroCount)

	ticker := time.NewTicker(500 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			remaining := w.GetNonZeroPendingCount()
			total := w.GetPendingCount()
			w.logger.Warn("Upload wait cancelled by context",
				"remainingFiles", total,
				"remainingNonZero", remaining)
			return initialCount, ctx.Err()

		case <-ticker.C:
			count := w.GetNonZeroPendingCount()
			if count == 0 {
				total := w.GetPendingCount()
				w.logger.Info("All non-zero pending uploads completed",
					"totalRemaining", total)
				return initialCount, nil
			}
			total := w.GetPendingCount()
			w.logger.Debug("Still waiting for uploads",
				"totalPending", total,
				"nonZeroPending", count)
		}
	}
}

// WhenFlushed blocks until all non-zero pending writes are flushed (uploaded) or context is cancelled
// Zero-length files are considered flushed and won't block the wait
// This is useful for ensuring writeback data is fully committed before proceeding
func (w *WritebackWatcher) WhenFlushed(ctx context.Context) error {
	// Fast path: already flushed (only non-zero files matter)
	if w.GetNonZeroPendingCount() == 0 {
		return nil
	}

	w.logger.Debug("Waiting for writeback flush")

	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			remaining := w.GetNonZeroPendingCount()
			total := w.GetPendingCount()
			w.logger.Debug("Flush wait cancelled by context",
				"remainingFiles", total,
				"remainingNonZero", remaining)
			return ctx.Err()

		case <-ticker.C:
			if w.GetNonZeroPendingCount() == 0 {
				total := w.GetPendingCount()
				w.logger.Debug("Writeback flushed",
					"zeroByteFilesRemaining", total)
				return nil
			}
		}
	}
}
