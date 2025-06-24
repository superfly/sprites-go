package juicefs

import (
	"bufio"
	"context"
	"database/sql"
	"fmt"
	"io"
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
	leaseMgr      *LeaseManager
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

	j := &JuiceFS{
		config:     config,
		mountReady: make(chan error, 1),
		stopCh:     make(chan struct{}),
		stoppedCh:  make(chan struct{}),
		signalCh:   make(chan os.Signal, 1),
	}

	// Initialize lease manager for non-local mode
	if !config.LocalMode {
		j.leaseMgr = NewLeaseManager(config)
	}

	// Initialize the overlay manager if enabled
	if config.OverlayEnabled {
		j.overlayMgr = NewOverlay(j)

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
	// Create necessary directories
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

	// Create litestream configuration
	litestreamConfigPath := filepath.Join(os.TempDir(), "litestream-juicefs.yml")
	if err := j.createLitestreamConfig(litestreamConfigPath, metaDB, checkpointDB); err != nil {
		return fmt.Errorf("failed to create litestream config: %w", err)
	}

	// Handle lease acquisition and determine if we need to restore
	needsRestore := false
	if j.config.LocalMode {
		// In local mode, check if litestream backup exists
		backupPath := filepath.Join(j.config.BaseDir, "litestream", "generations")
		if _, err := os.Stat(backupPath); err == nil {
			needsRestore = true
		}
	} else {
		// S3 mode - use lease manager
		fmt.Println("Acquiring JuiceFS database lease...")
		leaseAcquired, err := j.leaseMgr.AcquireLease(ctx)
		if err != nil {
			// If we got an error after waiting (meaning we eventually acquired the lease)
			// we need to restore
			needsRestore = true
			fmt.Println("Acquired lease after waiting, will restore from litestream")
		} else if leaseAcquired {
			// We got the lease immediately
			existingBucket, err := j.getExistingBucket(metaDB)
			if err != nil {
				fmt.Printf("Acquired lease but no existing metadata DB found (%v), will restore\n", err)
				needsRestore = true
			} else if existingBucket != j.config.S3Bucket {
				fmt.Printf("Acquired lease but bucket mismatch (existing: %s, current: %s), will restore\n", existingBucket, j.config.S3Bucket)
				needsRestore = true
			} else {
				fmt.Printf("Acquired lease and bucket matches (%s), using existing databases on disk\n", existingBucket)
				needsRestore = false
			}
		}
	}

	// Perform restore if needed
	if needsRestore {
		if j.config.LocalMode {
			fmt.Println("Restoring from local litestream backup")
		} else {
			// Remove existing databases and cache before restore
			os.Remove(metaDB)
			os.Remove(checkpointDB)
			os.RemoveAll(cacheDir)
			fmt.Printf("Restoring databases from %s\n", j.config.S3Bucket)
		}

		// Restore metadata database
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
			fmt.Printf("Litestream restore output for metadata: %s\n", string(output))
		}

		// Restore checkpoint database
		restoreCheckpointCmd := exec.CommandContext(ctx, "litestream", "restore",
			"-config", litestreamConfigPath,
			"-if-replica-exists",
			checkpointDB)

		if !j.config.LocalMode {
			restoreCheckpointCmd.Env = restoreCmd.Env // Use same environment
		}

		if output, err := restoreCheckpointCmd.CombinedOutput(); err != nil {
			// If restore fails, it's okay - checkpoint DB will be created fresh
			fmt.Printf("Litestream restore output for checkpoints: %s\n", string(output))
		}
	}

	// Ensure cache directory exists (might have been removed)
	os.MkdirAll(cacheDir, 0755)

	// Format JuiceFS if needed
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)
	if !j.isFormatted(metaURL) {
		if err := j.formatJuiceFS(ctx, metaURL); err != nil {
			return fmt.Errorf("failed to format JuiceFS: %w", err)
		}
	}

	// Calculate cache and buffer sizes
	cacheSizeMB := j.calculateCacheSize(cacheDir)
	bufferSizeMB := j.calculateBufferSize()

	// Start litestream replication in parallel
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

	// Mount JuiceFS
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
		metaURL,
		mountPath,
	}

	j.mountCmd = exec.CommandContext(ctx, "juicefs", mountArgs...)

	// Set up stderr pipe to watch for ready message
	stderrPipe, err := j.mountCmd.StderrPipe()
	if err != nil {
		return fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	// Start watching for ready message
	go j.watchForReady(stderrPipe, mountPath)

	// Start the mount command
	if err := j.mountCmd.Start(); err != nil {
		return fmt.Errorf("failed to start JuiceFS mount: %w", err)
	}

	// Set up signal handling
	signal.Notify(j.signalCh, syscall.SIGTERM, syscall.SIGINT)
	go j.handleSignals()

	// Start the process monitor
	go j.monitorProcess()

	// Wait for mount to be ready or timeout
	select {
	case err := <-j.mountReady:
		if err != nil {
			// Kill mount process if it's still running
			j.mountCmd.Process.Kill()
			// Don't call Wait() here - monitorProcess will handle it
			return err
		}
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
		fmt.Printf("JuiceFS shutdown completed in %v\n", time.Since(startTime))
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
				fmt.Printf("Warning: failed to close checkpoint database: %v\n", err)
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
			fmt.Println("Unmounting root overlay...")
			ctx := context.Background()
			if err := j.overlayMgr.Unmount(ctx); err != nil {
				fmt.Printf("Warning: error unmounting overlay: %v\n", err)
			}
		}

		// Then unmount dependent mounts
		fmt.Println("Looking for dependent mounts to unmount...")
		if err := j.findAndUnmountDependentMounts(mountPath); err != nil {
			fmt.Printf("Warning: error finding/unmounting dependent mounts: %v\n", err)
		}

		// Sync the JuiceFS filesystem to flush pending writes
		fmt.Println("Syncing JuiceFS filesystem...")
		syncStart := time.Now()
		syncCmd := exec.Command("sync", "-f", mountPath)
		if output, err := syncCmd.CombinedOutput(); err != nil {
			fmt.Printf("Warning: sync failed for JuiceFS mount: %v\n", err)
			if len(output) > 0 {
				fmt.Printf("  Sync stderr/stdout: %s\n", string(output))
			}
		} else {
			fmt.Printf("Sync completed in %v\n", time.Since(syncStart))
		}

		// First try graceful unmount without --force to allow JuiceFS to flush its cache
		// JuiceFS may need time to:
		// - Flush write-back cache
		// - Complete pending uploads (up to --upload-delay=1m)
		// - Close file handles properly
		fmt.Println("Attempting graceful JuiceFS unmount (this may take several minutes)...")
		unmountStart := time.Now()

		// Create a context with a generous timeout for graceful unmount
		// We use 3 minutes to account for the 1-minute upload delay plus overhead
		gracefulCtx, gracefulCancel := context.WithTimeout(context.Background(), 3*time.Minute)
		defer gracefulCancel()

		unmountCmd := exec.CommandContext(gracefulCtx, "juicefs", "umount", mountPath)
		if output, err := unmountCmd.CombinedOutput(); err != nil {
			fmt.Printf("Graceful unmount failed after %v: %v\n", time.Since(unmountStart), err)

			// If graceful unmount fails or times out, try with --force
			fmt.Println("Attempting force unmount...")
			forceCmd := exec.Command("juicefs", "umount", "--force", mountPath)
			if output2, err2 := forceCmd.CombinedOutput(); err2 != nil {
				// Check if it's exit status 3 (not mounted) - this is OK
				if exitErr, ok := err2.(*exec.ExitError); ok && exitErr.ExitCode() == 3 {
					fmt.Printf("JuiceFS already unmounted at %s\n", mountPath)
				} else {
					// Log but don't fail on other unmount errors
					fmt.Printf("Warning: failed to unmount JuiceFS: %v (graceful output: %s, force output: %s)\n",
						err2, string(output), string(output2))
				}
			} else {
				fmt.Printf("Force unmount succeeded after %v\n", time.Since(unmountStart))
			}
		} else {
			fmt.Printf("Graceful unmount succeeded after %v\n", time.Since(unmountStart))
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
			fmt.Printf("JuiceFS mount process exited with error: %v\n", err)
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

func (j *JuiceFS) getExistingBucket(metaDB string) (string, error) {
	// Check if database file exists
	if _, err := os.Stat(metaDB); os.IsNotExist(err) {
		return "", fmt.Errorf("metadata database file does not exist")
	}

	db, err := sql.Open("sqlite", metaDB)
	if err != nil {
		return "", fmt.Errorf("failed to open database: %w", err)
	}
	defer db.Close()

	// Check if the jfs_setting table exists
	var tableExists int
	err = db.QueryRow("SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='jfs_setting'").Scan(&tableExists)
	if err != nil {
		return "", fmt.Errorf("failed to check for jfs_setting table: %w", err)
	}
	if tableExists == 0 {
		return "", fmt.Errorf("database exists but is not fully formatted (missing jfs_setting table)")
	}

	var bucketURL string
	err = db.QueryRow("SELECT json_extract(value, '$.Bucket') FROM jfs_setting WHERE name = 'format'").Scan(&bucketURL)
	if err != nil {
		return "", fmt.Errorf("failed to read bucket from format setting: %w", err)
	}

	// Extract bucket name from the URL (format: https://endpoint/bucket-name)
	if bucketURL == "" {
		return "", fmt.Errorf("bucket not found in format settings")
	}

	parts := strings.Split(bucketURL, "/")
	if len(parts) > 0 {
		return parts[len(parts)-1], nil
	}
	return bucketURL, nil
}

func (j *JuiceFS) isFormatted(metaURL string) bool {
	cmd := exec.Command("juicefs", "status", metaURL)
	return cmd.Run() == nil
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

func (j *JuiceFS) watchForReady(stderr io.Reader, mountPath string) {
	scanner := bufio.NewScanner(stderr)
	for scanner.Scan() {
		line := scanner.Text()
		fmt.Println(line) // Echo the line for transparency

		// Check for both possible ready messages
		if strings.Contains(line, "juicefs is ready") || strings.Contains(line, "is ready at") {
			// Create the active directory
			activeDir := filepath.Join(mountPath, "active", "fs")
			if err := os.MkdirAll(activeDir, 0755); err != nil {
				j.mountReady <- fmt.Errorf("failed to create active directory: %w", err)
				return
			}
			fmt.Printf("JuiceFS ready: created active directory at %s\n", filepath.Dir(activeDir))

			// Initialize checkpoint database using the base directory (where metadata.db is located)
			db, err := NewCheckpointDB(j.config.BaseDir)
			if err != nil {
				j.mountReady <- fmt.Errorf("failed to initialize checkpoint database: %w", err)
				return
			}
			j.checkpointDB = db
			fmt.Println("Checkpoint database initialized")

			// Apply quota asynchronously
			go j.applyActiveFsQuota()

			// Mount the overlay
			if j.overlayMgr != nil {
				ctx := context.Background()
				if err := j.overlayMgr.Mount(ctx); err != nil {
					j.mountReady <- fmt.Errorf("failed to mount overlay: %w", err)
					return
				}
			}

			j.mountReady <- nil
			return
		}
	}

	// If we get here, we didn't see the ready message
	j.mountReady <- fmt.Errorf("did not receive 'juicefs is ready' message")
}

// applyActiveFsQuota applies a 10TB quota to the active/fs directory
func (j *JuiceFS) applyActiveFsQuota() {
	ctx := context.Background()

	// Construct metadata URL
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

	// Wait a moment for the mount to stabilize
	time.Sleep(2 * time.Second)

	fmt.Println("Applying 10TB quota to /active/fs directory...")

	// Apply 10TB quota using juicefs quota command
	// 10TB = 10240 GiB
	quotaCmd := exec.CommandContext(ctx, "juicefs", "quota", "set", metaURL,
		"--path", "/active/fs",
		"--capacity", "10240")

	output, err := quotaCmd.CombinedOutput()
	if err != nil {
		// Check if quota already exists
		if strings.Contains(string(output), "already exists") {
			fmt.Println("Quota already exists for /active/fs directory")
		} else {
			fmt.Printf("Warning: failed to apply quota to /active/fs: %v, output: %s\n", err, string(output))
		}
	} else {
		fmt.Printf("Successfully applied 10TB quota to /active/fs directory\n")
		if len(output) > 0 {
			fmt.Printf("Quota info: %s\n", string(output))
		}
	}
}

func (j *JuiceFS) handleSignals() {
	select {
	case sig := <-j.signalCh:
		fmt.Printf("Received signal %v, stopping JuiceFS...\n", sig)
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
		fmt.Printf("Unmounting dependent mount: %s (device: %s, type: %s)\n",
			mount.mountPoint, mount.device, mount.fsType)

		// First, try to sync the filesystem to flush any pending writes
		syncStart := time.Now()
		syncCtx, syncCancel := context.WithTimeout(context.Background(), 30*time.Second)
		syncCmd := exec.CommandContext(syncCtx, "sync", "-f", mount.mountPoint)
		syncOutput, syncErr := syncCmd.CombinedOutput()
		syncCancel()

		if syncErr != nil {
			// sync might fail for some mount types, but we should still try to unmount
			fmt.Printf("  Warning: sync failed for %s after %v: %v\n",
				mount.mountPoint, time.Since(syncStart), syncErr)
			if len(syncOutput) > 0 {
				fmt.Printf("    Sync stderr/stdout: %s\n", string(syncOutput))
			}
		} else {
			fmt.Printf("  Sync completed in %v\n", time.Since(syncStart))
		}

		// First try normal unmount
		unmountStart := time.Now()
		cmd := exec.Command("umount", mount.mountPoint)
		if _, err := cmd.CombinedOutput(); err != nil {
			// If normal unmount fails, try with --force
			fmt.Printf("  Normal unmount failed, trying force unmount...\n")
			cmd = exec.Command("umount", "--force", mount.mountPoint)
			if output2, err2 := cmd.CombinedOutput(); err2 != nil {
				// Try lazy unmount as last resort
				fmt.Printf("  Force unmount failed, trying lazy unmount...\n")
				cmd = exec.Command("umount", "--lazy", mount.mountPoint)
				if output3, err3 := cmd.CombinedOutput(); err3 != nil {
					fmt.Printf("  Warning: all unmount attempts failed for %s after %v\n    Normal: %v\n    Force: %v (output: %s)\n    Lazy: %v (output: %s)\n",
						mount.mountPoint, time.Since(unmountStart), err, err2, string(output2), err3, string(output3))
				} else {
					fmt.Printf("  Lazy unmount succeeded after %v\n", time.Since(unmountStart))
				}
			} else {
				fmt.Printf("  Force unmount succeeded after %v\n", time.Since(unmountStart))
			}
		} else {
			fmt.Printf("  Unmounted successfully in %v\n", time.Since(unmountStart))
		}
	}

	return nil
}
