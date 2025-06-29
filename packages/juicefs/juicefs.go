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
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"

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

// LeaseManager interface defines the lease management operations needed by JuiceFS
type LeaseManager interface {
	// Wait blocks until the lease is successfully acquired
	Wait(ctx context.Context) error
	// LeaseAttemptCount returns the number of times lease acquisition has been attempted
	LeaseAttemptCount() int
	// Stop stops the lease manager
	Stop()
}

type JuiceFS struct {
	config        Config
	litestreamCmd *exec.Cmd
	mountCmd      *exec.Cmd
	mountReady    chan error
	stopCh        chan struct{}
	stoppedCh     chan struct{}
	signalCh      chan os.Signal
	overlayMgr    *OverlayManager
	checkpointDB  *CheckpointDB
	leaseMgr      LeaseManager
	logger        *slog.Logger
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

	// Overlay configuration
	OverlayEnabled       bool   // Enable root overlay mounting
	OverlayImageSize     string // Size of the overlay image (e.g., "100G")
	OverlayLowerPath     string // Path to lower directory (read-only base layer)
	OverlayTargetPath    string // Where to mount the final overlay
	OverlaySkipOverlayFS bool   // Skip overlayfs, only mount loopback

	// LeaseManager for distributed coordination (optional, only used if not LocalMode)
	LeaseManager LeaseManager

	// Logger for logging (optional, defaults to no-op logger)
	Logger *slog.Logger
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

	j := &JuiceFS{
		config:     config,
		mountReady: make(chan error, 1),
		stopCh:     make(chan struct{}),
		stoppedCh:  make(chan struct{}),
		signalCh:   make(chan os.Signal, 1),
		logger:     logger,
	}

	// Use provided lease manager for non-local mode
	if !config.LocalMode && config.LeaseManager != nil {
		j.leaseMgr = config.LeaseManager
	}

	// Initialize the overlay manager if enabled
	if config.OverlayEnabled {
		j.overlayMgr = NewOverlay(j, logger)

		// Apply overlay configuration
		if config.OverlayImageSize != "" {
			j.overlayMgr.imageSize = config.OverlayImageSize
		}
		if config.OverlayLowerPath != "" {
			j.overlayMgr.SetAppImagePath(config.OverlayLowerPath)
		}
		if config.OverlayTargetPath != "" {
			j.overlayMgr.SetOverlayTargetPath(config.OverlayTargetPath)
		}
		j.overlayMgr.SetSkipOverlayFS(config.OverlaySkipOverlayFS)
	}

	// checkpointDB will be initialized after mount is ready

	return j, nil
}

// GetOverlay returns the overlay manager instance
func (j *JuiceFS) GetOverlay() *OverlayManager {
	return j.overlayMgr
}

// Start initializes and starts JuiceFS with Litestream replication
func (j *JuiceFS) Start(ctx context.Context) error {
	startTime := time.Now()
	j.logger.Debug("JuiceFS Start beginning", "startTime", startTime.Format(time.RFC3339))

	// Create necessary directories
	stepStart := time.Now()
	cacheDir := filepath.Join(j.config.BaseDir, "cache")
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
	checkpointDB := filepath.Join(j.config.BaseDir, "checkpoints.db")
	mountPath := filepath.Join(j.config.BaseDir, "data")

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

	// Create litestream configuration
	stepStart = time.Now()
	litestreamConfigPath := filepath.Join(os.TempDir(), "litestream-juicefs.yml")
	if err := j.createLitestreamConfig(litestreamConfigPath, metaDB, checkpointDB); err != nil {
		return fmt.Errorf("failed to create litestream config: %w", err)
	}
	j.logger.Debug("Litestream config creation completed", "duration", time.Since(stepStart).Seconds())

	// Handle lease acquisition and determine if we need to restore
	stepStart = time.Now()
	needsRestore := false
	if j.config.LocalMode {
		// In local mode, check if litestream backup exists
		backupPath := filepath.Join(j.config.BaseDir, "litestream", "generations")
		if _, err := os.Stat(backupPath); err == nil {
			needsRestore = true
		}
		j.logger.Debug("Local mode backup check completed", "duration", time.Since(stepStart).Seconds(), "needsRestore", needsRestore)
	} else if j.leaseMgr != nil {
		// S3 mode - use lease manager
		j.logger.Info("Acquiring JuiceFS database lease...")
		err := j.leaseMgr.Wait(ctx)
		if err != nil {
			return fmt.Errorf("failed to acquire lease: %w", err)
		}

		// Check if this was a slow start (multiple attempts)
		if j.leaseMgr.LeaseAttemptCount() > 1 {
			// We had to wait or retry, need to restore
			needsRestore = true
			j.logger.Info("Acquired lease after multiple attempts, will restore from litestream", "attempts", j.leaseMgr.LeaseAttemptCount())
		} else {
			// We got the lease immediately, check if we can use existing data
			existingBucket, err := j.getExistingBucket(metaDB)
			if err != nil {
				j.logger.Info("Acquired lease but no existing metadata DB found, will restore", "error", err)
				needsRestore = true
			} else if existingBucket != j.config.S3Bucket {
				j.logger.Info("Acquired lease but bucket mismatch, will restore", "existingBucket", existingBucket, "currentBucket", j.config.S3Bucket)
				needsRestore = true
			} else {
				j.logger.Info("Acquired lease on first attempt and bucket matches, using existing databases on disk", "bucket", existingBucket)
				needsRestore = false
			}
		}
		j.logger.Debug("Lease acquisition completed",
			"duration", time.Since(stepStart).Seconds(),
			"attempts", j.leaseMgr.LeaseAttemptCount(),
			"needsRestore", needsRestore)
	}

	// Perform restore if needed
	if needsRestore {
		stepStart = time.Now()
		if j.config.LocalMode {
			j.logger.Info("Restoring from local litestream backup")
		} else {
			// Remove existing databases and cache before restore
			os.Remove(metaDB)
			os.Remove(checkpointDB)
			os.RemoveAll(cacheDir)
			j.logger.Info("Restoring databases from S3", "bucket", j.config.S3Bucket)
		}

		// Restore metadata database
		metaRestoreStart := time.Now()
		restoreCmd := exec.CommandContext(ctx, "litestream", "restore",
			"-config", litestreamConfigPath,
			"-if-replica-exists",
			metaDB)

		if !j.config.LocalMode {
			restoreCmd.Env = append(os.Environ(),
				fmt.Sprintf("JUICEFS_META_DB=%s", metaDB),
				fmt.Sprintf("CHECKPOINT_DB=%s", checkpointDB),
				fmt.Sprintf("SPRITE_S3_ACCESS_KEY=%s", j.config.S3AccessKey),
				fmt.Sprintf("SPRITE_S3_SECRET_ACCESS_KEY=%s", j.config.S3SecretAccessKey),
				fmt.Sprintf("SPRITE_S3_ENDPOINT_URL=%s", j.config.S3EndpointURL),
				fmt.Sprintf("SPRITE_S3_BUCKET=%s", j.config.S3Bucket),
			)
		}

		if output, err := restoreCmd.CombinedOutput(); err != nil {
			// If restore fails, it's okay - we'll format a new filesystem
			j.logger.Debug("Litestream restore output for metadata", "output", string(output))
		}
		j.logger.Debug("Metadata database restore completed", "duration", time.Since(metaRestoreStart).Seconds())

		// Restore checkpoint database
		checkpointRestoreStart := time.Now()
		restoreCheckpointCmd := exec.CommandContext(ctx, "litestream", "restore",
			"-config", litestreamConfigPath,
			"-if-replica-exists",
			checkpointDB)

		if !j.config.LocalMode {
			restoreCheckpointCmd.Env = restoreCmd.Env // Use same environment
		}

		if output, err := restoreCheckpointCmd.CombinedOutput(); err != nil {
			// If restore fails, it's okay - checkpoint DB will be created fresh
			j.logger.Debug("Litestream restore output for checkpoints", "output", string(output))
		}
		j.logger.Debug("Checkpoint database restore completed", "duration", time.Since(checkpointRestoreStart).Seconds())
		j.logger.Debug("Total restore process completed", "duration", time.Since(stepStart).Seconds())
	}

	// Ensure cache directory exists (might have been removed)
	stepStart = time.Now()
	os.MkdirAll(cacheDir, 0755)
	j.logger.Debug("Cache directory recreation completed", "duration", time.Since(stepStart).Seconds())

	// Format JuiceFS if needed
	stepStart = time.Now()
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)
	if !j.isFormatted(metaURL) {
		j.logger.Debug("JuiceFS not formatted, formatting...")
		if err := j.formatJuiceFS(ctx, metaURL); err != nil {
			return fmt.Errorf("failed to format JuiceFS: %w", err)
		}
		j.logger.Debug("JuiceFS formatting completed", "duration", time.Since(stepStart).Seconds())
	} else {
		j.logger.Debug("JuiceFS already formatted, skipped formatting", "duration", time.Since(stepStart).Seconds())
	}

	// Calculate cache and buffer sizes
	stepStart = time.Now()
	cacheSizeMB := j.calculateCacheSize(cacheDir)
	bufferSizeMB := j.calculateBufferSize()
	j.logger.Debug("Cache and buffer size calculation completed",
		"duration", time.Since(stepStart).Seconds(),
		"cacheMB", cacheSizeMB,
		"bufferMB", bufferSizeMB)

	// Start litestream replication in parallel
	stepStart = time.Now()
	j.litestreamCmd = exec.Command("litestream", "replicate", "-config", litestreamConfigPath)

	// Only set environment variables for S3 mode
	if !j.config.LocalMode {
		j.litestreamCmd.Env = append(os.Environ(),
			fmt.Sprintf("JUICEFS_META_DB=%s", metaDB),
			fmt.Sprintf("CHECKPOINT_DB=%s", checkpointDB),
			fmt.Sprintf("SPRITE_S3_ACCESS_KEY=%s", j.config.S3AccessKey),
			fmt.Sprintf("SPRITE_S3_SECRET_ACCESS_KEY=%s", j.config.S3SecretAccessKey),
			fmt.Sprintf("SPRITE_S3_ENDPOINT_URL=%s", j.config.S3EndpointURL),
			fmt.Sprintf("SPRITE_S3_BUCKET=%s", j.config.S3Bucket),
		)
	}

	if err := j.litestreamCmd.Start(); err != nil {
		return fmt.Errorf("failed to start litestream: %w", err)
	}
	j.logger.Debug("Litestream startup completed", "duration", time.Since(stepStart).Seconds())

	// Mount JuiceFS
	stepStart = time.Now()
	mountArgs := []string{
		"mount",
		"--no-usage-report",
		"-o", "writeback_cache",
		"--writeback",
		"--upload-delay=1m",
		"--cache-dir", cacheDir,
		"--cache-size", fmt.Sprintf("%d", cacheSizeMB),
		"--buffer-size", fmt.Sprintf("%d", bufferSizeMB),
		"--no-syslog",
		"--fsname", "SpriteFS",
		metaURL,
		mountPath,
	}

	j.mountCmd = exec.CommandContext(ctx, "juicefs", mountArgs...)
	j.mountCmd.Env = append(os.Environ(),
		"FSTAB_NAME_PREFIX=\"sprite:\"",
	)

	// Send JuiceFS output directly to our stdout/stderr
	j.mountCmd.Stdout = os.Stdout
	j.mountCmd.Stderr = os.Stderr

	// Start the mount command
	if err := j.mountCmd.Start(); err != nil {
		return fmt.Errorf("failed to start JuiceFS mount: %w", err)
	}
	j.logger.Debug("JuiceFS mount command startup completed", "duration", time.Since(stepStart).Seconds())

	// Start watching for ready signal
	go j.watchForReady(mountPath, time.Now())
	// Set up signal handling
	stepStart = time.Now()
	signal.Notify(j.signalCh, syscall.SIGTERM, syscall.SIGINT)
	go j.handleSignals()

	// Start the process monitor
	go j.monitorProcess()
	j.logger.Debug("Signal handling and process monitor setup completed", "duration", time.Since(stepStart).Seconds())

	// Wait for mount to be ready or timeout
	j.logger.Debug("Waiting for JuiceFS mount to be ready...")
	waitStart := time.Now()
	select {
	case err := <-j.mountReady:
		if err != nil {
			// Kill mount process if it's still running
			j.mountCmd.Process.Kill()
			// Don't call Wait() here - monitorProcess will handle it
			return err
		}
		j.logger.Debug("JuiceFS mount ready", "duration", time.Since(waitStart).Seconds())
		j.logger.Debug("Total JuiceFS Start completed", "duration", time.Since(startTime).Seconds())
		return nil
	case <-ctx.Done():
		// Kill mount process
		j.mountCmd.Process.Kill()
		// Don't call Wait() here - monitorProcess will handle it
		return ctx.Err()
	case <-time.After(2 * time.Minute):
		// Kill mount process
		j.mountCmd.Process.Kill()
		// Don't call Wait() here - monitorProcess will handle it
		return fmt.Errorf("timeout waiting for JuiceFS to be ready (2 minutes)")
	}
}

// Stop cleanly shuts down JuiceFS and Litestream
// The context timeout should be set appropriately (recommended: 5+ minutes) to allow
// for flushing all cached writes to the backend storage.
func (j *JuiceFS) Stop(ctx context.Context) error {
	startTime := time.Now()

	// Stop lease manager if present
	if j.leaseMgr != nil {
		j.leaseMgr.Stop()
	}

	// Stop signal handling
	signal.Stop(j.signalCh)

	// Signal stop
	select {
	case <-j.stopCh:
		// Already stopping
	default:
		close(j.stopCh)
	}

	// Wait for stopped signal
	// Note: We rely on the context timeout instead of a hard-coded timeout
	// to allow for proper flushing of all writes
	select {
	case <-j.stoppedCh:
		j.logger.Info("JuiceFS shutdown completed", "duration", time.Since(startTime))
		return nil
	case <-ctx.Done():
		return fmt.Errorf("shutdown timed out after %v: %w", time.Since(startTime), ctx.Err())
	}
}

// monitorProcess handles the lifecycle of the mount process
func (j *JuiceFS) monitorProcess() {
	defer close(j.stoppedCh)

	// Ensure checkpoint database is closed on exit
	defer func() {
		if j.checkpointDB != nil {
			if err := j.checkpointDB.Close(); err != nil {
				j.logger.Warn("Failed to close checkpoint database", "error", err)
			}
		}
	}()

	mountPath := filepath.Join(j.config.BaseDir, "data")

	// Wait for either stop signal or mount process to exit
	processDone := make(chan error, 1)
	go func() {
		if j.mountCmd != nil {
			processDone <- j.mountCmd.Wait()
		} else {
			processDone <- nil
		}
	}()

	select {
	case <-j.stopCh:
		// Stop requested, first unmount the overlay
		if j.overlayMgr != nil {
			j.logger.Info("Unmounting root overlay...")
			ctx := context.Background()
			if err := j.overlayMgr.Unmount(ctx); err != nil {
				j.logger.Warn("Error unmounting overlay", "error", err)
			}
		}

		// Then unmount dependent mounts
		j.logger.Info("Looking for dependent mounts to unmount...")
		if err := j.findAndUnmountDependentMounts(mountPath); err != nil {
			j.logger.Warn("Error finding/unmounting dependent mounts", "error", err)
		}

		// Sync the JuiceFS filesystem to flush pending writes
		j.logger.Info("Syncing JuiceFS filesystem...")
		syncStart := time.Now()
		syncCmd := exec.Command("sync", "-f", mountPath)
		if output, err := syncCmd.CombinedOutput(); err != nil {
			j.logger.Warn("Sync failed for JuiceFS mount", "error", err)
			if len(output) > 0 {
				j.logger.Debug("Sync stderr/stdout", "output", string(output))
			}
		} else {
			j.logger.Info("Sync completed", "duration", time.Since(syncStart))
		}

		// First try graceful unmount without --force to allow JuiceFS to flush its cache
		// JuiceFS may need time to:
		// - Flush write-back cache
		// - Complete pending uploads (up to --upload-delay=1m)
		// - Close file handles properly
		j.logger.Info("Attempting graceful JuiceFS unmount (this may take several minutes)...")
		unmountStart := time.Now()

		// Create a context with a generous timeout for graceful unmount
		// We use 3 minutes to account for the 1-minute upload delay plus overhead
		gracefulCtx, gracefulCancel := context.WithTimeout(context.Background(), 3*time.Minute)
		defer gracefulCancel()

		unmountCmd := exec.CommandContext(gracefulCtx, "juicefs", "umount", mountPath)
		if output, err := unmountCmd.CombinedOutput(); err != nil {
			j.logger.Warn("Graceful unmount failed", "duration", time.Since(unmountStart), "error", err)

			// If graceful unmount fails or times out, try with --force
			j.logger.Info("Attempting force unmount...")
			forceCmd := exec.Command("juicefs", "umount", "--force", mountPath)
			if output2, err2 := forceCmd.CombinedOutput(); err2 != nil {
				// Check if it's exit status 3 (not mounted) - this is OK
				if exitErr, ok := err2.(*exec.ExitError); ok && exitErr.ExitCode() == 3 {
					j.logger.Info("JuiceFS already unmounted", "path", mountPath)
				} else {
					// Log but don't fail on other unmount errors
					j.logger.Warn("Failed to unmount JuiceFS",
						"error", err2,
						"gracefulOutput", string(output),
						"forceOutput", string(output2))
				}
			} else {
				j.logger.Info("Force unmount succeeded", "duration", time.Since(unmountStart))
			}
		} else {
			j.logger.Info("Graceful unmount succeeded", "duration", time.Since(unmountStart))
		}

		// Wait for mount process to exit
		select {
		case <-processDone:
			// Process exited after unmount
		case <-time.After(2 * time.Second):
			// If mount process doesn't exit after unmount, kill it
			if j.mountCmd != nil && j.mountCmd.Process != nil {
				j.mountCmd.Process.Kill()
				<-processDone
			}
		}

		// Stop litestream
		if j.litestreamCmd != nil && j.litestreamCmd.Process != nil {
			// Try graceful shutdown first with SIGTERM
			j.litestreamCmd.Process.Signal(syscall.SIGTERM)

			// Give it a moment to shut down gracefully
			done := make(chan error, 1)
			go func() {
				done <- j.litestreamCmd.Wait()
			}()

			select {
			case <-done:
				// Process exited gracefully
			case <-time.After(5 * time.Second):
				// Force kill if it doesn't exit in time
				j.litestreamCmd.Process.Kill()
				<-done
			}
		}

	case err := <-processDone:
		// Mount process exited unexpectedly
		if err != nil {
			j.logger.Error("JuiceFS mount process exited with error", "error", err)
		}

		// Stop litestream
		if j.litestreamCmd != nil && j.litestreamCmd.Process != nil {
			// Try graceful shutdown first with SIGTERM
			j.litestreamCmd.Process.Signal(syscall.SIGTERM)

			// Give it a moment to shut down gracefully
			done := make(chan error, 1)
			go func() {
				done <- j.litestreamCmd.Wait()
			}()

			select {
			case <-done:
				// Process exited gracefully
			case <-time.After(5 * time.Second):
				// Force kill if it doesn't exit in time
				j.litestreamCmd.Process.Kill()
				<-done
			}
		}
	}
}

// Helper functions

func (j *JuiceFS) createLitestreamConfig(configPath, metaDB, checkpointDB string) error {
	var config string

	if j.config.LocalMode {
		// Local file-based replication
		localBackupPath := filepath.Join(j.config.BaseDir, "litestream")
		config = fmt.Sprintf(`logging:
  level: warn
dbs:
  - path: %s
    replicas:
      - type: file
        path: %s
        retention: 24h
        snapshot-interval: 1m
        sync-interval: 1s
  - path: %s
    replicas:
      - type: file
        path: %s
        retention: 24h
        snapshot-interval: 1m
        sync-interval: 1s
`, metaDB, localBackupPath, checkpointDB, localBackupPath)
	} else {
		// S3-based replication
		config = `logging:
  level: warn
dbs:
  - path: ${JUICEFS_META_DB}
    replicas:
      - type: s3
        endpoint: ${SPRITE_S3_ENDPOINT_URL}
        bucket: ${SPRITE_S3_BUCKET}
        path: juicefs-metadata
        access-key-id: ${SPRITE_S3_ACCESS_KEY}
        secret-access-key: ${SPRITE_S3_SECRET_ACCESS_KEY}
        sync-interval: 1s
  - path: ${CHECKPOINT_DB}
    replicas:
      - type: s3
        endpoint: ${SPRITE_S3_ENDPOINT_URL}
        bucket: ${SPRITE_S3_BUCKET}
        path: checkpoints
        access-key-id: ${SPRITE_S3_ACCESS_KEY}
        secret-access-key: ${SPRITE_S3_SECRET_ACCESS_KEY}
        sync-interval: 1s
`
	}

	return os.WriteFile(configPath, []byte(config), 0644)
}

// getJuiceFSFormatInfo reads JuiceFS format information from the metadata database
// Returns the bucket name and whether the database is properly formatted
func (j *JuiceFS) getJuiceFSFormatInfo(metaDB string) (bucketName string, isFormatted bool, err error) {
	// Check if database file exists
	if _, err := os.Stat(metaDB); os.IsNotExist(err) {
		return "", false, fmt.Errorf("metadata database file does not exist")
	}

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
		return "", false, fmt.Errorf("database exists but is not fully formatted (missing jfs_setting table)")
	}

	// Database is formatted if we got here
	var bucketURL string
	err = db.QueryRow("SELECT json_extract(value, '$.Bucket') FROM jfs_setting WHERE name = 'format'").Scan(&bucketURL)
	if err != nil {
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

func (j *JuiceFS) getExistingBucket(metaDB string) (string, error) {
	bucketName, _, err := j.getJuiceFSFormatInfo(metaDB)
	return bucketName, err
}

func (j *JuiceFS) isFormatted(metaURL string) bool {
	// Extract database path from sqlite3:// URL
	if !strings.HasPrefix(metaURL, "sqlite3://") {
		return false
	}
	metaDB := strings.TrimPrefix(metaURL, "sqlite3://")

	_, isFormatted, _ := j.getJuiceFSFormatInfo(metaDB)
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
			"--trash-days", "0",
			metaURL,
			j.config.VolumeName,
		)
	} else {
		// S3 storage mode
		bucketURL := fmt.Sprintf("%s/%s", j.config.S3EndpointURL, j.config.S3Bucket)
		cmd = exec.CommandContext(ctx, "juicefs", "format",
			"--storage", "s3",
			"--bucket", bucketURL,
			"--trash-days", "0",
			metaURL,
			j.config.VolumeName,
		)
		// Pass credentials via environment variables for security
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("ACCESS_KEY=%s", j.config.S3AccessKey),
			fmt.Sprintf("SECRET_KEY=%s", j.config.S3SecretAccessKey),
		)
	}

	output, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("format failed: %w, output: %s", err, string(output))
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

// watchForReady polls the mount point until it's ready and then performs post-mount setup
func (j *JuiceFS) watchForReady(mountPath string, startTime time.Time) {
	timeout := 2 * time.Minute
	interval := 10 * time.Millisecond
	deadline := time.Now().Add(timeout)

	j.logger.Debug("Starting mount readiness polling",
		"intervalMs", interval.Seconds()*1000,
		"timeSinceStart", time.Since(startTime).Seconds())

	for time.Now().Before(deadline) {
		var stat syscall.Stat_t
		if err := syscall.Stat(mountPath, &stat); err == nil {
			if stat.Ino == 1 {
				j.logger.Debug("Mount detected as ready (inode=1)",
					"pollingDuration", time.Since(deadline.Add(-timeout)).Seconds(),
					"timeSinceStart", time.Since(startTime).Seconds())

				// Now perform post-mount setup tasks
				if err := j.performPostMountSetup(mountPath, startTime); err != nil {
					j.mountReady <- err
					return
				}
				j.mountReady <- nil
				return
			}
		}
		time.Sleep(interval)
	}

	j.mountReady <- fmt.Errorf("timeout waiting for mount at %s after %.0fs", mountPath, timeout.Seconds())
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

	// Initialize checkpoint database using the base directory (where metadata.db is located)
	stepStart = time.Now()
	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: j.config.BaseDir,
		Logger:  j.logger,
	})
	if err != nil {
		return fmt.Errorf("failed to initialize checkpoint database: %w", err)
	}
	j.checkpointDB = db
	j.logger.Info("Checkpoint database initialized")
	j.logger.Debug("Checkpoint database initialization completed", "duration", time.Since(stepStart).Seconds())

	// Apply quota asynchronously
	j.logger.Debug("Starting async quota application")
	go j.applyActiveFsQuota()

	// Mount the overlay
	if j.overlayMgr != nil {
		stepStart = time.Now()
		j.logger.Debug("Starting overlay mount")
		ctx := context.Background()
		if err := j.overlayMgr.Mount(ctx); err != nil {
			return fmt.Errorf("failed to mount overlay: %w", err)
		}
		j.logger.Debug("Overlay mount completed", "duration", time.Since(stepStart).Seconds())
	}

	j.logger.Debug("Post-mount setup completed", "timeSinceStart", time.Since(startTime).Seconds())
	return nil
}

// applyActiveFsQuota applies a 10TB quota to the active/fs directory
func (j *JuiceFS) applyActiveFsQuota() {
	ctx := context.Background()

	// Construct metadata URL
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

	// Wait a moment for the mount to stabilize
	time.Sleep(2 * time.Second)

	j.logger.Info("Applying 10TB quota to /active/fs directory...")

	// Apply 10TB quota using juicefs quota command
	// 10TB = 10240 GiB
	quotaCmd := exec.CommandContext(ctx, "juicefs", "quota", "set", metaURL,
		"--path", "/active/fs",
		"--capacity", "10240")

	output, err := quotaCmd.CombinedOutput()
	if err != nil {
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

func (j *JuiceFS) handleSignals() {
	select {
	case sig := <-j.signalCh:
		j.logger.Info("Received signal, stopping JuiceFS...", "signal", sig)
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		j.Stop(ctx)
	case <-j.stoppedCh:
		// Already stopped, clean up signal handler
		signal.Stop(j.signalCh)
		return
	}
}

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
		syncCtx, syncCancel := context.WithTimeout(context.Background(), 30*time.Second)
		syncCmd := exec.CommandContext(syncCtx, "sync", "-f", mount.mountPoint)
		syncOutput, syncErr := syncCmd.CombinedOutput()
		syncCancel()

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
			j.logger.Debug("Sync completed", "duration", time.Since(syncStart))
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
					j.logger.Debug("Lazy unmount succeeded", "duration", time.Since(unmountStart))
				}
			} else {
				j.logger.Debug("Force unmount succeeded", "duration", time.Since(unmountStart))
			}
		} else {
			j.logger.Debug("Unmounted successfully", "duration", time.Since(unmountStart))
		}
	}

	return nil
}
