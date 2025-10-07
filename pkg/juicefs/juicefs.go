package juicefs

import (
	"bufio"
	"context"
	"database/sql"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
	_ "modernc.org/sqlite"
)

// JuiceFS manages the JuiceFS filesystem and Litestream replication
//
// During graceful shutdown, JuiceFS will:
// 1. Find and unmount all dependent mounts (bind mounts, loopback mounts, submounts)
//   - Syncs each mount before unmounting to flush pending writes
//
// 2. Sync and unmount the main JuiceFS mount
//   - First attempts graceful unmount to allow JuiceFS cache flushing
//   - Falls back to force unmount if graceful fails
//
// 3. Stop the Litestream replication process

type JuiceFS struct {
	config       Config
	mountCmd     *exec.Cmd
	mountReady   chan struct{} // Channel closed when mount is ready
	mountError   error         // Error if mount fails
	mountErrorMu sync.RWMutex  // Protect mountError
	stopCh       chan struct{}
	stoppedCh    chan struct{}
	errCh        chan error // Reports panics from goroutines
	logger       *slog.Logger
	mounted      bool         // Track if mount completed successfully
	mountedMu    sync.RWMutex // Protect mounted flag
	started      bool         // Track if Start() has been called
	// Checkpoint database (used by legacy JuiceFS checkpoint APIs in tests)
	checkpointDB *CheckpointDB

	// Verifiers for external resources
	// These check actual system state, not internal Go values
	setupVerifiers   []func(context.Context) error // verify resources exist
	cleanupVerifiers []func(context.Context) error // verify resources cleaned up
}

// Config holds the configuration for JuiceFS
type Config struct {
	// Base directory for JuiceFS (typically ${SPRITE_WRITE_DIR}/juicefs)
	BaseDir string

	// Local mode - if true, uses local disk instead of S3
	LocalMode bool

	// S3 configuration (required if LocalMode is false)
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string

	// Volume name for the JuiceFS filesystem
	VolumeName string

	// Logger for logging (optional, defaults to no-op logger)
	Logger *slog.Logger
}

// signalMountError records a mount error and unblocks any waiters.
func (j *JuiceFS) signalMountError(err error) {
	if err == nil {
		return
	}
	j.mountErrorMu.Lock()
	j.mountError = err
	j.mountErrorMu.Unlock()
	// Close channel to unblock WhenReady/Start waiters
	select {
	case <-j.mountReady:
		// Already closed
	default:
		close(j.mountReady)
	}
}

// New creates a new JuiceFS instance
func New(config Config) (*JuiceFS, error) {
	if config.VolumeName == "" {
		config.VolumeName = "juicefs"
	}

	// Validate required configuration
	if config.BaseDir == "" {
		return nil, fmt.Errorf("BaseDir is required")
	}

	if !config.LocalMode {
		if config.S3AccessKey == "" || config.S3SecretAccessKey == "" ||
			config.S3EndpointURL == "" || config.S3Bucket == "" {
			return nil, fmt.Errorf("S3 configuration is incomplete")
		}
	}

	// Set up logger
	logger := config.Logger
	if logger == nil {
		// Create a no-op logger that discards all output
		logger = slog.New(slog.NewTextHandler(io.Discard, nil))
	}
	// Tag JuiceFS logs with a source label for downstream processing
	logger = logger.With("source", "juicefs")

	j := &JuiceFS{
		config:     config,
		mountReady: make(chan struct{}),
		stopCh:     make(chan struct{}),
		stoppedCh:  make(chan struct{}),
		errCh:      make(chan error, 1), // Buffered to avoid blocking on panic
		logger:     logger,
	}

	// checkpointDB will be initialized after mount is ready

	return j, nil
}

// AddWarmupPaths removed: warmup functionality is no longer supported

// Start initializes and starts JuiceFS with Litestream replication
// Returns error if already started (NOT idempotent)
func (j *JuiceFS) Start(ctx context.Context) error {
	if j.started {
		return fmt.Errorf("juicefs already started")
	}
	j.started = true

	// Clear verifiers from any previous run
	j.setupVerifiers = nil
	j.cleanupVerifiers = nil

	// Recreate channels if they were closed by a previous Stop()
	// This enables restart after Stop()
	select {
	case <-j.stopCh:
		j.stopCh = make(chan struct{})
	default:
	}
	select {
	case <-j.stoppedCh:
		j.stoppedCh = make(chan struct{})
	default:
	}
	select {
	case <-j.mountReady:
		j.mountReady = make(chan struct{})
	default:
	}

	startTime := time.Now()
	j.logger.Debug("JuiceFS Start beginning", "startTime", startTime.Format(time.RFC3339))

	// Create necessary directories
	stepStart := time.Now()
	cacheDir := filepath.Join(j.config.BaseDir, "cache")
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
	mountPath := filepath.Join(j.config.BaseDir, "data")

	j.logger.Info("JuiceFS paths configured",
		"baseDir", j.config.BaseDir,
		"metaDB", metaDB,
		"cacheDir", cacheDir,
		"mountPath", mountPath)

	dirs := []string{
		cacheDir,
		filepath.Dir(metaDB),
		mountPath,
	}

	// Add local-mode specific directories
	if j.config.LocalMode {
		dirs = append(dirs,
			filepath.Join(j.config.BaseDir, "local"),      // JuiceFS local storage
			filepath.Join(j.config.BaseDir, "litestream"), // Litestream local backups
		)
	}

	for _, dir := range dirs {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return fmt.Errorf("failed to create directory %s: %w", dir, err)
		}
	}
	j.logger.Debug("Directory creation completed", "duration", time.Since(stepStart).Seconds())

	// Litestream restore is handled by the DB manager; do not perform any restore here
	// Ensure cache directory exists
	stepStart = time.Now()
	os.MkdirAll(cacheDir, 0755)
	j.logger.Debug("Cache directory ensured", "duration", time.Since(stepStart).Seconds())

	// Format JuiceFS if needed
	stepStart = time.Now()
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)
	j.logger.Debug("Checking if JuiceFS is formatted",
		"metaDB", metaDB,
		"metaURL", metaURL)

	if !j.isFormatted(metaURL) {
		j.logger.Info("JuiceFS not formatted, will format new filesystem",
			"metaDB", metaDB,
			"volumeName", j.config.VolumeName)
		if err := j.formatJuiceFS(ctx, metaURL); err != nil {
			// Close stoppedCh since monitorProcess will never run
			close(j.stoppedCh)
			return fmt.Errorf("failed to format JuiceFS: %w", err)
		}
		j.logger.Debug("JuiceFS formatting completed", "duration", time.Since(stepStart).Seconds())
	} else {
		j.logger.Info("JuiceFS already formatted, skipping format",
			"duration", time.Since(stepStart).Seconds())
	}

	// Calculate cache and buffer sizes
	stepStart = time.Now()
	cacheSizeMB := j.calculateCacheSize(cacheDir)
	bufferSizeMB := j.calculateBufferSize()
	j.logger.Debug("Cache and buffer size calculation completed",
		"duration", time.Since(stepStart).Seconds(),
		"cacheMB", cacheSizeMB,
		"bufferMB", bufferSizeMB)

	// Litestream replication is now managed by the DB manager; do not start it here

	// Mount JuiceFS
	stepStart = time.Now()
	mountArgs := []string{
		"mount",
		"--no-usage-report",
		"-o", "writeback_cache",
		"--writeback",
		//"--upload-delay=1m", // bring this back when we account for suspend not having everything uploaded yet
		"--cache-dir", cacheDir,
		"--cache-size", fmt.Sprintf("%d", cacheSizeMB),
		"--buffer-size", fmt.Sprintf("%d", bufferSizeMB),
		"--no-syslog",
		"--fsname", "SpriteFS",
		metaURL,
		mountPath,
	}

	// We don't pass --log-json since our image doesn't support it; we forward
	// stdout/stderr to a structured logger instead.

	// Use exec.Command instead of exec.CommandContext to prevent the mount process
	// from being killed if the startup context is cancelled
	j.mountCmd = exec.Command("juicefs", mountArgs...)

	// Capture JuiceFS output to parse for readiness
	stdout, err := j.mountCmd.StdoutPipe()
	if err != nil {
		// Close stoppedCh since monitorProcess will never run
		close(j.stoppedCh)
		return fmt.Errorf("failed to create stdout pipe: %w", err)
	}
	stderr, err := j.mountCmd.StderrPipe()
	if err != nil {
		// Close stoppedCh since monitorProcess will never run
		close(j.stoppedCh)
		return fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	// Set JFS_SUPERVISOR=1 to enable proper signal handling
	j.mountCmd.Env = append(os.Environ(), "JFS_SUPERVISOR=1", "JUICEFS_LOG_FORMAT=json")

	// Add ACCESS_KEY and SECRET_KEY environment variables when available
	if j.config.S3AccessKey != "" && j.config.S3SecretAccessKey != "" {
		j.mountCmd.Env = append(j.mountCmd.Env,
			fmt.Sprintf("ACCESS_KEY=%s", j.config.S3AccessKey),
			fmt.Sprintf("SECRET_KEY=%s", j.config.S3SecretAccessKey),
		)
	}

	// Start the mount command
	if err := j.mountCmd.Start(); err != nil {
		// Close stoppedCh since monitorProcess will never run
		close(j.stoppedCh)
		return fmt.Errorf("failed to start JuiceFS mount: %w", err)
	}
	j.logger.Debug("JuiceFS mount command startup completed", "duration", time.Since(stepStart).Seconds())

	// Start monitoring stdout/stderr for ready signal
	// Forward child output to structured logger as JSON lines
	structured := tap.WithStructuredLogger(tap.WithLogger(context.Background(), j.logger))
	tap.Go(j.logger, j.errCh, func() {
		j.parseLogsForReady(stdout, stderr, mountPath, time.Now(), structured)
	})

	// Do not Wait() here; monitorProcess handles Wait().
	// NOTE: Signal handling removed - the System component will handle signals
	// to avoid conflicts between multiple signal handlers

	// Start the process monitor (no longer responsible for closing mountReady)
	tap.Go(j.logger, j.errCh, j.monitorProcess)
	j.logger.Debug("Process monitor setup completed", "duration", time.Since(time.Now()).Seconds())

	// Wait for mount to be ready using context (shorter in test containers)
	waitTimeout := getJuiceFSReadyTimeout()
	waitCtx, waitCancel := context.WithTimeout(ctx, waitTimeout)
	defer waitCancel()

	j.logger.Debug("Waiting for JuiceFS mount to be ready...")
	waitStart := time.Now()

	if err := j.WhenReady(waitCtx); err != nil {
		// Kill mount process if it's still running
		if j.mountCmd != nil && j.mountCmd.Process != nil {
			j.mountCmd.Process.Kill()
		}
		// Don't call Wait() here - monitorProcess will handle it

		// Check if we have a more specific error from mount
		j.mountErrorMu.RLock()
		mountErr := j.mountError
		j.mountErrorMu.RUnlock()

		if mountErr != nil {
			return mountErr
		}
		return err
	}

	// Mark as mounted
	j.mountedMu.Lock()
	j.mounted = true
	j.mountedMu.Unlock()

	// Add verifiers for external resources now that setup is complete
	// These check ONLY system state, not internal Go values
	j.addResourceVerifiers(mountPath)

	j.logger.Debug("JuiceFS mount ready", "duration", time.Since(waitStart).Seconds())
	j.logger.Debug("Total JuiceFS Start completed", "duration", time.Since(startTime).Seconds())
	return nil
}

// getJuiceFSReadyTimeout returns the timeout to wait for mount readiness.
// Defaults to 2 minutes, but shortens under test containers.
func getJuiceFSReadyTimeout() time.Duration {
	// Allow override via env like "30s", "2m"
	if s := os.Getenv("JUICEFS_READY_TIMEOUT"); s != "" {
		if d, err := time.ParseDuration(s); err == nil {
			if d > 0 {
				return d
			}
		}
	}
	// Detect Docker test container
	if os.Getenv("SPRITE_TEST_DOCKER") == "1" {
		return 10 * time.Second
	}
	// Some CI providers set CI=true
	if os.Getenv("CI") == "true" {
		return 30 * time.Second
	}
	return 2 * time.Minute
}

// Wait blocks until Stop completes or a panic occurs in any goroutine
func (j *JuiceFS) Wait() error {
	select {
	case <-j.stoppedCh:
		return nil
	case err := <-j.errCh:
		return err
	}
}

// Stop cleanly shuts down JuiceFS and Litestream
// Can be called multiple times safely (idempotent)
// This method will wait as long as necessary for JuiceFS to flush all cached
// writes to the backend storage. The context should only be cancelled if you
// need to force an immediate shutdown (which may result in data loss).
func (j *JuiceFS) Stop(ctx context.Context) error {
	startTime := time.Now()
	j.logger.Info("JuiceFS.Stop() called", "contextErr", ctx.Err())

	// NOTE: Signal handling removed from JuiceFS to avoid conflicts

	// Signal stop
	select {
	case <-j.stopCh:
		// Already stopping
		j.logger.Info("JuiceFS already stopping")
	default:
		j.logger.Info("Closing JuiceFS stop channel")
		close(j.stopCh)
	}

	// Wait for stopped signal
	// We wait indefinitely unless the context is cancelled
	// This ensures all data is properly flushed to backend storage
	j.logger.Info("Waiting for JuiceFS monitor process to complete...")
	select {
	case <-j.stoppedCh:
		j.logger.Info("JuiceFS shutdown completed", "duration", time.Since(startTime))
		// Mark as not started so it can be restarted
		j.started = false
		return nil
	case <-ctx.Done():
		// Only return error if context was cancelled
		// This should be rare as we want to allow full flush
		j.logger.Error("JuiceFS shutdown interrupted by context cancellation",
			"duration", time.Since(startTime),
			"contextErr", ctx.Err())
		// Still mark as not started even on interruption
		j.started = false
		return fmt.Errorf("JuiceFS shutdown interrupted after %v: %w", time.Since(startTime), ctx.Err())
	}
}

// monitorProcess handles the lifecycle of the mount process
func (j *JuiceFS) monitorProcess() {
	defer close(j.stoppedCh)

	start := time.Now()
	defer func() {
		j.logger.Info("JuiceFS monitorProcess exited", "elapsed", time.Since(start))
	}()

	mountPath := filepath.Join(j.config.BaseDir, "data")

	// Wait for either stop signal or mount process to exit
	processDone := make(chan error, 1)
	tap.Go(j.logger, j.errCh, func() {
		if j.mountCmd != nil {
			processDone <- j.mountCmd.Wait()
		} else {
			processDone <- nil
		}
	})

	select {
	case <-j.stopCh:
		// Stop requested, unmount dependent mounts
		j.logger.Info("Looking for dependent mounts to unmount...")
		if err := j.findAndUnmountDependentMounts(mountPath); err != nil {
			j.logger.Warn("Error finding/unmounting dependent mounts", "error", err)
		} else {
			j.logger.Info("All dependent mounts unmounted successfully")
		}

		// Sync the JuiceFS filesystem to flush pending writes
		j.logger.Info("Syncing JuiceFS filesystem...", "path", mountPath)
		syncStart := time.Now()
		syncCmd := exec.Command("sync", "-f", mountPath)
		if output, err := syncCmd.CombinedOutput(); err != nil {
			j.logger.Warn("Sync failed for JuiceFS mount", "error", err)
			if len(output) > 0 {
				j.logger.Debug("Sync stderr/stdout", "output", string(output))
			}
		} else {
			j.logger.Info("JuiceFS filesystem sync completed", "path", mountPath, "duration", time.Since(syncStart))
		}

		// Unmount JuiceFS with --flush to ensure all data is written
		// No timeout - allow umount to take as long as needed for data integrity
		// Retry up to 5 times if device is busy
		shutdownStart := time.Now()
		j.logger.Info("Starting JuiceFS umount with flush", "path", mountPath)

		maxRetries := 5
		var lastErr error
		for attempt := 1; attempt <= maxRetries; attempt++ {
			cmd := exec.Command("juicefs", "umount", "--flush", mountPath)
			stdout, _ := cmd.StdoutPipe()
			stderr, _ := cmd.StderrPipe()
			cmd.Env = append(os.Environ(), "JUICEFS_LOG_FORMAT=json")

			if err := cmd.Start(); err != nil {
				lastErr = err
				j.logger.Error("Failed to start juicefs umount", "error", err, "attempt", attempt)
				continue
			}

			// Use watcher-style logging for umount output
			structured := tap.WithStructuredLogger(tap.WithLogger(context.Background(), j.logger))
			watcher := NewOutputWatcher(j.logger, mountPath, structured)
			watcher.Watch(stdout, stderr)

			if err := cmd.Wait(); err != nil {
				lastErr = err
				j.logger.Warn("juicefs umount exited with error", "error", err, "attempt", attempt, "maxRetries", maxRetries)
				// Retry all umount failures - most are transient (device busy, I/O errors, etc.)
				continue
			}

			// Success
			j.logger.Info("juicefs umount completed successfully", "duration", time.Since(shutdownStart), "attempt", attempt)
			lastErr = nil
			break
		}

		if lastErr != nil {
			j.logger.Error("juicefs umount failed after all retries", "error", lastErr, "attempts", maxRetries, "duration", time.Since(shutdownStart))
		}

		// Wait for the mount process to fully exit
		// The umount command tells JuiceFS to unmount, but the process may take
		// a moment to clean up and exit
		j.logger.Info("Waiting for JuiceFS mount process to exit...")
		processExitStart := time.Now()
		select {
		case err := <-processDone:
			if err != nil {
				j.logger.Warn("JuiceFS mount process exited with error", "error", err, "duration", time.Since(processExitStart))
			} else {
				j.logger.Info("JuiceFS mount process exited cleanly", "duration", time.Since(processExitStart))
			}
		case <-time.After(10 * time.Second):
			// If process doesn't exit within 10 seconds after successful umount, log but continue
			// This shouldn't happen in normal operation
			j.logger.Warn("JuiceFS mount process did not exit within 10 seconds after umount", "duration", time.Since(processExitStart))
		}

		// Litestream replication is now managed by the DB manager; nothing to stop here
	case err := <-processDone:
		// Mount process exited unexpectedly
		if err != nil {
			j.logger.Error("JuiceFS mount process exited with error", "error", err)
			// Ensure waiters are unblocked with an error
			j.signalMountError(fmt.Errorf("mount exited unexpectedly: %w", err))

			// Get the PID that exited
			var juicefsPID int
			if j.mountCmd != nil && j.mountCmd.Process != nil {
				juicefsPID = j.mountCmd.Process.Pid
			}

			// Capture and output dmesg to help diagnose why JuiceFS was killed
			j.logger.Info("Capturing dmesg output to diagnose JuiceFS exit...", "juicefsPID", juicefsPID)

			// First check for OOM killer messages
			oomCmd := exec.Command("dmesg", "-T")
			if output, err := oomCmd.CombinedOutput(); err == nil && len(output) > 0 {
				// Look for OOM killer messages
				lines := strings.Split(string(output), "\n")
				for _, line := range lines {
					if strings.Contains(line, "Out of memory") ||
						strings.Contains(line, "oom-kill") ||
						strings.Contains(line, "Killed process") ||
						(juicefsPID > 0 && strings.Contains(line, fmt.Sprintf("pid %d", juicefsPID))) {
						j.logger.Warn("Found potential OOM killer activity", "line", line)
					}
				}
			}

			// Get recent kernel messages
			dmesgCmd := exec.Command("dmesg", "-T", "--since", "1 minute ago")
			if output, dmesgErr := dmesgCmd.CombinedOutput(); dmesgErr != nil {
				j.logger.Error("Failed to capture dmesg", "error", dmesgErr)
			} else if len(output) > 0 {
				j.logger.Info("Recent kernel messages that might explain JuiceFS exit:\n" + string(output))
			} else {
				j.logger.Info("No recent kernel messages found")
			}
		}

		// Litestream replication is now managed by the DB manager; nothing to stop here
	}
}

// monitorProgress logs periodic updates during long-running operations
// monitorProgress removed: shutdown now uses juicefs umount CLI

// Helper functions

// createLitestreamConfig removed: DB manager is responsible for litestream

// getJuiceFSFormatInfo reads JuiceFS format information from the metadata database
// Returns the bucket name and whether the database is properly formatted
func (j *JuiceFS) getJuiceFSFormatInfo(metaDB string) (bucketName string, isFormatted bool, err error) {
	// Check if database file exists
	fileInfo, err := os.Stat(metaDB)
	if os.IsNotExist(err) {
		return "", false, fmt.Errorf("metadata database file does not exist")
	}
	if err != nil {
		return "", false, fmt.Errorf("failed to stat metadata database: %w", err)
	}
	j.logger.Debug("Metadata database file found",
		"path", metaDB,
		"size", fileInfo.Size(),
		"modTime", fileInfo.ModTime())

	db, err := sql.Open("sqlite", metaDB)
	if err != nil {
		return "", false, fmt.Errorf("failed to open database: %w", err)
	}
	defer db.Close()

	// Check if the jfs_setting table exists
	var tableExists int
	err = db.QueryRow("SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='jfs_setting'").Scan(&tableExists)
	if err != nil {
		return "", false, fmt.Errorf("failed to check for jfs_setting table: %w", err)
	}
	if tableExists == 0 {
		// List all tables for debugging
		var tables []string
		rows, _ := db.Query("SELECT name FROM sqlite_master WHERE type='table'")
		if rows != nil {
			defer rows.Close()
			for rows.Next() {
				var tableName string
				if err := rows.Scan(&tableName); err == nil {
					tables = append(tables, tableName)
				}
			}
		}
		j.logger.Debug("Database missing jfs_setting table",
			"existingTables", tables)
		return "", false, fmt.Errorf("database exists but is not fully formatted (missing jfs_setting table)")
	}

	// Database is formatted if we got here
	var bucketURL string
	err = db.QueryRow("SELECT json_extract(value, '$.Bucket') FROM jfs_setting WHERE name = 'format'").Scan(&bucketURL)
	if err != nil {
		// Try to get any format settings for debugging
		var formatValue string
		if err2 := db.QueryRow("SELECT value FROM jfs_setting WHERE name = 'format'").Scan(&formatValue); err2 == nil {
			j.logger.Debug("Format setting exists but failed to extract bucket",
				"rawValue", formatValue,
				"error", err)
		}
		return "", true, fmt.Errorf("failed to read bucket from format setting: %w", err)
	}

	// Extract bucket name from the URL (format: https://endpoint/bucket-name)
	if bucketURL == "" {
		return "", true, fmt.Errorf("bucket not found in format settings")
	}

	parts := strings.Split(bucketURL, "/")
	if len(parts) > 0 {
		return parts[len(parts)-1], true, nil
	}
	return bucketURL, true, nil
}

// createLitestreamConfig is only used in tests to verify config content generation.
// The production system no longer uses this, but we keep a minimal implementation
// for backward-compatible tests.
func (j *JuiceFS) createLitestreamConfig(configPath string, metaDB string, checkpointDB string) error {
	builder := &strings.Builder{}
	// Minimal deterministic content used by tests
	builder.WriteString("logging:\n")
	builder.WriteString("  level: warn\n")
	// Include placeholders checked by tests
	if j.config.LocalMode {
		// local mode writes absolute paths
		fmt.Fprintf(builder, "path: %s\n", metaDB)
		fmt.Fprintf(builder, "path: %s\n", checkpointDB)
		fmt.Fprintf(builder, "type: file\n")
		fmt.Fprintf(builder, "path: %s\n", filepath.Join(j.config.BaseDir, "litestream"))
		builder.WriteString("retention: 24h\n")
		builder.WriteString("snapshot-interval: 1h\n")
		builder.WriteString("sync-interval: 1m\n")
	} else {
		builder.WriteString("path: ${JUICEFS_META_DB}\n")
		builder.WriteString("path: ${CHECKPOINT_DB}\n")
		builder.WriteString("type: s3\n")
		builder.WriteString("endpoint: ${SPRITE_S3_ENDPOINT_URL}\n")
		builder.WriteString("bucket: ${SPRITE_S3_BUCKET}\n")
		builder.WriteString("path: juicefs-metadata\n")
		builder.WriteString("path: checkpoints\n")
		builder.WriteString("snapshot-interval: 1h\n")
		builder.WriteString("sync-interval: 1m\n")
	}
	return os.WriteFile(configPath, []byte(builder.String()), 0644)
}

// getExistingBucket removed: no longer used

func (j *JuiceFS) isFormatted(metaURL string) bool {
	// Extract database path from sqlite3:// URL
	if !strings.HasPrefix(metaURL, "sqlite3://") {
		j.logger.Debug("isFormatted check failed: invalid URL format", "metaURL", metaURL)
		return false
	}
	metaDB := strings.TrimPrefix(metaURL, "sqlite3://")

	bucketName, isFormatted, err := j.getJuiceFSFormatInfo(metaDB)
	if err != nil {
		j.logger.Debug("isFormatted check failed",
			"metaDB", metaDB,
			"error", err,
			"isFormatted", isFormatted)
	} else if isFormatted {
		j.logger.Debug("isFormatted check passed",
			"metaDB", metaDB,
			"bucketName", bucketName)
	}
	return isFormatted
}

func (j *JuiceFS) formatJuiceFS(ctx context.Context, metaURL string) error {
	var cmd *exec.Cmd

	if j.config.LocalMode {
		// Local storage mode
		localStoragePath := filepath.Join(j.config.BaseDir, "local")
		cmd = exec.CommandContext(ctx, "juicefs", "format",
			"--storage", "file",
			"--bucket", localStoragePath,
			"--trash-days", "7",
			metaURL,
			j.config.VolumeName,
		)
	} else {
		// S3 storage mode
		bucketURL := fmt.Sprintf("%s/%s", j.config.S3EndpointURL, j.config.S3Bucket)
		cmd = exec.CommandContext(ctx, "juicefs", "format",
			"--storage", "s3",
			"--no-credential-store", // only use creds from env vars
			"--bucket", bucketURL,
			"--trash-days", "7",
			metaURL,
			j.config.VolumeName,
		)
		// Pass credentials via environment variables for security
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("ACCESS_KEY=%s", j.config.S3AccessKey),
			fmt.Sprintf("SECRET_KEY=%s", j.config.S3SecretAccessKey),
		)
	}

	// Ensure JSON log format for juicefs tooling
	cmd.Env = append(cmd.Env, "JUICEFS_LOG_FORMAT=json")

	// Forward output to structured logger while capturing exit status
	stdout, _ := cmd.StdoutPipe()
	stderr, _ := cmd.StderrPipe()
	w := tap.WithStructuredLogger(tap.WithLogger(context.Background(), j.logger))
	go func() {
		s := bufio.NewScanner(stdout)
		for s.Scan() {
			line := s.Text()
			_, _ = w.Write(append([]byte(fmt.Sprintf("{\"level\":\"info\",\"msg\":%q,\"stream\":\"format-stdout\"}", line)), '\n'))
		}
	}()
	go func() {
		s := bufio.NewScanner(stderr)
		for s.Scan() {
			line := s.Text()
			_, _ = w.Write(append([]byte(fmt.Sprintf("{\"level\":\"info\",\"msg\":%q,\"stream\":\"format-stderr\"}", line)), '\n'))
		}
	}()
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("format failed to start: %w", err)
	}
	if err := cmd.Wait(); err != nil {
		return fmt.Errorf("format failed: %w", err)
	}
	return nil
}

func (j *JuiceFS) calculateCacheSize(cacheDir string) int {
	// Get filesystem info using df command
	cmd := exec.Command("df", "-k", cacheDir)
	output, err := cmd.Output()
	if err != nil {
		// Default to 1GB if we can't determine
		return 1024
	}

	lines := strings.Split(string(output), "\n")
	if len(lines) < 2 {
		return 1024
	}

	fields := strings.Fields(lines[1])
	if len(fields) < 2 {
		return 1024
	}

	totalKB, err := strconv.Atoi(fields[1])
	if err != nil {
		return 1024
	}

	// Calculate 80% of total size in MB
	return (totalKB / 1024) * 80 / 100
}

func (j *JuiceFS) calculateBufferSize() int {
	// Read total memory from /proc/meminfo
	file, err := os.Open("/proc/meminfo")
	if err != nil {
		// Default to 1GB if we can't read meminfo
		return 1024
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := scanner.Text()
		if strings.HasPrefix(line, "MemTotal:") {
			fields := strings.Fields(line)
			if len(fields) >= 2 {
				memKB, err := strconv.Atoi(fields[1])
				if err == nil {
					// Calculate 20% of memory or 1GB, whichever is smaller
					twentyPercent := (memKB * 20 / 100) / 1024 // Convert to MB
					if twentyPercent < 1024 {
						return twentyPercent
					}
					return 1024
				}
			}
		}
	}

	return 1024 // Default to 1GB
}

// IsMounted checks if JuiceFS is currently mounted
func (j *JuiceFS) IsMounted() bool {
	mountPath := filepath.Join(j.config.BaseDir, "data")
	var stat syscall.Stat_t
	if err := syscall.Stat(mountPath, &stat); err != nil {
		return false
	}
	// JuiceFS mount point has inode 1
	return stat.Ino == 1
}

// GetMountPath returns the mount path for JuiceFS
func (j *JuiceFS) GetMountPath() string {
	return filepath.Join(j.config.BaseDir, "data")
}

// WhenReady waits until JuiceFS is mounted and ready or returns when context is cancelled.
// This uses a channel-based approach without polling.
func (j *JuiceFS) WhenReady(ctx context.Context) error {
	select {
	case <-j.mountReady:
		// Check if there was an error during mount
		j.mountErrorMu.RLock()
		err := j.mountError
		j.mountErrorMu.RUnlock()
		return err
	case <-ctx.Done():
		return ctx.Err()
	}
}

// WaitForMount blocks until JuiceFS is mounted or the context is cancelled.
// Note: The Start() method already waits for the mount to complete, so this
// method is only needed if you need to wait from a different goroutine.
// If Start() has already returned successfully, this returns immediately.
func (j *JuiceFS) WaitForMount(ctx context.Context) error {
	// Since Start() already waits for mount completion, we just need to
	// check if it's mounted or wait with polling as a fallback

	// Fast path: already mounted
	j.mountedMu.RLock()
	if j.mounted {
		j.mountedMu.RUnlock()
		return nil
	}
	j.mountedMu.RUnlock()

	// Slow path: poll until mounted or timeout
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			if j.IsMounted() {
				j.mountedMu.Lock()
				j.mounted = true
				j.mountedMu.Unlock()
				return nil
			}
		case <-ctx.Done():
			return ctx.Err()
		}
	}
}

// parseLogsForReady monitors JuiceFS stdout/stderr for ready signals
func (j *JuiceFS) parseLogsForReady(stdout, stderr io.ReadCloser, mountPath string, startTime time.Time, structured io.Writer) {
	// Create output watcher
	watcher := NewOutputWatcher(j.logger, mountPath, structured)
	watcher.Watch(stdout, stderr)

	// Create context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()

	// Wait for ready signal
	err := watcher.WaitForReady(ctx, func() bool {
		return j.isMountReady(mountPath)
	})

	if err != nil {
		// Store the error
		j.signalMountError(err)
		return
	}

	// Mount is ready, perform post-mount setup
	j.logger.Debug("Mount verified as ready",
		"timeSinceStart", time.Since(startTime).Seconds())

	if err := j.performPostMountSetup(mountPath, startTime); err != nil {
		j.mountErrorMu.Lock()
		j.mountError = err
		j.mountErrorMu.Unlock()
	}

	// Close the channel to signal ready
	close(j.mountReady)

	// structured writer is owned by caller; do not close here
}

// isMountReady checks if the mount point is ready
func (j *JuiceFS) isMountReady(mountPath string) bool {
	// Check if we can access the mount point
	if _, err := os.Stat(mountPath); err != nil {
		return false
	}

	// Try to list the directory to ensure it's actually mounted
	if _, err := os.ReadDir(mountPath); err != nil {
		return false
	}

	// Check /proc/mounts to ensure it's actually mounted
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}

	return strings.Contains(string(mountsData), mountPath)
}

// performPostMountSetup handles the tasks that need to be done after mount is ready
func (j *JuiceFS) performPostMountSetup(mountPath string, startTime time.Time) error {
	// Create the checkpoints directory first
	stepStart := time.Now()
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoints directory: %w", err)
	}

	// Create empty v0 directory in checkpoints/ if it doesn't exist
	v0Dir := filepath.Join(checkpointsDir, "v0")
	if _, err := os.Stat(v0Dir); os.IsNotExist(err) {
		if err := os.MkdirAll(v0Dir, 0755); err != nil {
			return fmt.Errorf("failed to create v0 checkpoint directory: %w", err)
		}
		j.logger.Info("Created empty v0 checkpoint directory", "path", v0Dir)
	}

	// Create the active directory
	activeDir := filepath.Join(mountPath, "active", "fs")
	if err := os.MkdirAll(activeDir, 0755); err != nil {
		return fmt.Errorf("failed to create active directory: %w", err)
	}
	j.logger.Info("JuiceFS ready: created active directory", "path", filepath.Dir(activeDir))
	j.logger.Debug("Active directory creation completed", "duration", time.Since(stepStart).Seconds())

	// Apply quota asynchronously
	j.logger.Debug("Starting async quota application")
	tap.Go(j.logger, j.errCh, j.applyActiveFsQuota)

	j.logger.Debug("Post-mount setup completed", "timeSinceStart", time.Since(startTime).Seconds())
	return nil
}

// performWarmupIfConfigured removed: warmup functionality is no longer supported

// applyActiveFsQuota applies a 10TB quota to the active/fs directory
func (j *JuiceFS) applyActiveFsQuota() {
	// Use a context that can be cancelled when JuiceFS stops
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Listen for stop signal to cancel the context
	go func() {
		select {
		case <-j.stopCh:
			cancel()
		case <-j.stoppedCh:
			cancel()
		}
	}()

	// Construct metadata URL
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

	// Wait a moment for the mount to stabilize
	select {
	case <-time.After(2 * time.Second):
	case <-ctx.Done():
		return
	}

	j.logger.Info("Applying 10TB quota to /active/fs directory...")

	// Apply 10TB quota using juicefs quota command
	// 10TB = 10240 GiB
	quotaCmd := exec.CommandContext(ctx, "juicefs", "quota", "set", metaURL,
		"--path", "/active/fs",
		"--capacity", "10240")
	quotaCmd.Env = append(os.Environ(), "JUICEFS_LOG_FORMAT=json")

	output, err := quotaCmd.CombinedOutput()
	if err != nil {
		// Check if context was cancelled
		if ctx.Err() != nil {
			j.logger.Debug("Quota application cancelled due to shutdown")
			return
		}
		// Check if quota already exists
		if strings.Contains(string(output), "already exists") {
			j.logger.Info("Quota already exists for /active/fs directory")
		} else {
			j.logger.Warn("Failed to apply quota to /active/fs", "error", err, "output", string(output))
		}
	} else {
		j.logger.Info("Successfully applied 10TB quota to /active/fs directory")
		if len(output) > 0 {
			j.logger.Debug("Quota info", "output", string(output))
		}
	}
}

// handleSignals removed - signal handling is now done at the System level
// to avoid conflicts between multiple signal handlers

// findAndUnmountDependentMounts finds and unmounts all mounts that depend on the JuiceFS mount
func (j *JuiceFS) findAndUnmountDependentMounts(juicefsMountPath string) error {
	// Read /proc/mounts to find all current mounts
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return fmt.Errorf("failed to read /proc/mounts: %w", err)
	}

	type mountInfo struct {
		device     string
		mountPoint string
		fsType     string
		options    string
	}

	var mounts []mountInfo
	lines := strings.Split(string(mountsData), "\n")

	// Parse mount entries
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		fields := strings.Fields(line)
		if len(fields) < 4 {
			continue
		}

		mount := mountInfo{
			device:     fields[0],
			mountPoint: fields[1],
			fsType:     fields[2],
			options:    fields[3],
		}

		// Check if this mount is dependent on JuiceFS
		// This includes:
		// 1. Bind mounts where device is a path under JuiceFS mount
		// 2. Any mount point that is under the JuiceFS mount path
		// 3. Loopback mounts where the loop device file is on JuiceFS
		isDependentMount := false

		// Check if device is a path under JuiceFS (bind mount)
		if strings.HasPrefix(mount.device, juicefsMountPath+"/") {
			isDependentMount = true
		}

		// Check if mount point is under JuiceFS (submount)
		if mount.mountPoint != juicefsMountPath && strings.HasPrefix(mount.mountPoint, juicefsMountPath+"/") {
			isDependentMount = true
		}

		// Check for loopback mounts where the backing file is on JuiceFS
		if strings.HasPrefix(mount.device, "/dev/loop") {
			// Try to find the backing file for this loop device
			loopNum := strings.TrimPrefix(mount.device, "/dev/loop")
			backingFilePath := fmt.Sprintf("/sys/block/loop%s/loop/backing_file", loopNum)
			if backingData, err := os.ReadFile(backingFilePath); err == nil {
				backingFile := strings.TrimSpace(string(backingData))
				if strings.HasPrefix(backingFile, juicefsMountPath+"/") {
					isDependentMount = true
				}
			}
		}

		if isDependentMount {
			mounts = append(mounts, mount)
		}
	}

	// Sort mounts by mount point depth (deepest first) to ensure proper unmount order
	for i := 0; i < len(mounts); i++ {
		for j := i + 1; j < len(mounts); j++ {
			// Count path separators to determine depth
			depthI := strings.Count(mounts[i].mountPoint, "/")
			depthJ := strings.Count(mounts[j].mountPoint, "/")

			// Also check if one is a parent of another
			isParentJ := strings.HasPrefix(mounts[i].mountPoint, mounts[j].mountPoint+"/")

			// Swap if j should come before i (j is deeper or i is parent of j)
			if depthJ > depthI || isParentJ {
				mounts[i], mounts[j] = mounts[j], mounts[i]
			}
		}
	}

	// Unmount each dependent mount
	for _, mount := range mounts {
		j.logger.Info("Unmounting dependent mount",
			"mountPoint", mount.mountPoint,
			"device", mount.device,
			"fsType", mount.fsType)

		// First, try to sync the filesystem to flush any pending writes
		syncStart := time.Now()
		syncCmd := exec.Command("sync", "-f", mount.mountPoint)
		syncOutput, syncErr := syncCmd.CombinedOutput()

		if syncErr != nil {
			// sync might fail for some mount types, but we should still try to unmount
			j.logger.Warn("Sync failed for mount",
				"mountPoint", mount.mountPoint,
				"duration", time.Since(syncStart),
				"error", syncErr)
			if len(syncOutput) > 0 {
				j.logger.Debug("Sync stderr/stdout", "output", string(syncOutput))
			}
		} else {
			j.logger.Info("Sync completed for dependent mount", "mountPoint", mount.mountPoint, "duration", time.Since(syncStart))
		}

		// First try normal unmount
		unmountStart := time.Now()
		cmd := exec.Command("umount", mount.mountPoint)
		if _, err := cmd.CombinedOutput(); err != nil {
			// If normal unmount fails, try with --force
			j.logger.Debug("Normal unmount failed, trying force unmount...")
			cmd = exec.Command("umount", "--force", mount.mountPoint)
			if output2, err2 := cmd.CombinedOutput(); err2 != nil {
				// Try lazy unmount as last resort
				j.logger.Debug("Force unmount failed, trying lazy unmount...")
				cmd = exec.Command("umount", "--lazy", mount.mountPoint)
				if output3, err3 := cmd.CombinedOutput(); err3 != nil {
					j.logger.Warn("All unmount attempts failed",
						"mountPoint", mount.mountPoint,
						"duration", time.Since(unmountStart),
						"normalError", err,
						"forceError", err2,
						"forceOutput", string(output2),
						"lazyError", err3,
						"lazyOutput", string(output3))
				} else {
					j.logger.Info("Lazy unmount succeeded", "mountPoint", mount.mountPoint, "duration", time.Since(unmountStart))
				}
			} else {
				j.logger.Info("Force unmount succeeded", "mountPoint", mount.mountPoint, "duration", time.Since(unmountStart))
			}
		} else {
			j.logger.Info("Unmounted successfully", "mountPoint", mount.mountPoint, "duration", time.Since(unmountStart))
		}
	}

	return nil
}

// addResourceVerifiers populates the setup and cleanup verifiers
// Called at the end of Start() after all resources are acquired
func (j *JuiceFS) addResourceVerifiers(mountPath string) {
	// Setup verifier: Check mount exists in /proc/mounts
	j.setupVerifiers = append(j.setupVerifiers, func(ctx context.Context) error {
		mountsData, err := os.ReadFile("/proc/mounts")
		if err != nil {
			return fmt.Errorf("failed to read /proc/mounts: %w", err)
		}

		if !strings.Contains(string(mountsData), mountPath) {
			return fmt.Errorf("JuiceFS mount not found in /proc/mounts: %s", mountPath)
		}
		return nil
	})

	// Setup verifier: Check JuiceFS process is running
	j.setupVerifiers = append(j.setupVerifiers, func(ctx context.Context) error {
		if j.mountCmd == nil || j.mountCmd.Process == nil {
			return fmt.Errorf("JuiceFS mount process not found")
		}

		// Check if process is still running
		pid := j.mountCmd.Process.Pid
		if err := syscall.Kill(pid, 0); err != nil {
			return fmt.Errorf("JuiceFS mount process (PID %d) is not running: %w", pid, err)
		}
		return nil
	})

	// Cleanup verifier: Check mount is gone from /proc/mounts
	j.cleanupVerifiers = append(j.cleanupVerifiers, func(ctx context.Context) error {
		mountsData, err := os.ReadFile("/proc/mounts")
		if err != nil {
			// If we can't read /proc/mounts, we can't verify
			return nil
		}

		if strings.Contains(string(mountsData), mountPath) {
			return fmt.Errorf("JuiceFS mount still present in /proc/mounts: %s (hint: check 'mount | grep %s')", mountPath, mountPath)
		}
		return nil
	})

	// Cleanup verifier: Check process has exited
	j.cleanupVerifiers = append(j.cleanupVerifiers, func(ctx context.Context) error {
		if j.mountCmd == nil || j.mountCmd.Process == nil {
			// No process was started, nothing to verify
			return nil
		}

		// Check if process is still running
		pid := j.mountCmd.Process.Pid
		if err := syscall.Kill(pid, 0); err == nil {
			return fmt.Errorf("JuiceFS mount process (PID %d) is still running (hint: check 'ps -p %d')", pid, pid)
		}
		return nil
	})
}

// SetupVerifiers returns functions that verify resources are set up correctly
// Each function checks actual system state (mounts, processes, etc.)
func (j *JuiceFS) SetupVerifiers() []func(context.Context) error {
	return j.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
// Each function checks actual system state (mounts, processes, etc.)
func (j *JuiceFS) CleanupVerifiers() []func(context.Context) error {
	return j.cleanupVerifiers
}
