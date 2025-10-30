package juicefs

import (
	"bufio"
	"context"
	"database/sql"
	"encoding/binary"
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

	// Writeback watcher for monitoring pending uploads
	writebackWatcher *WritebackWatcher

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

	// UploadDelay sets JuiceFS writeback upload delay (e.g., 2m, 30s). If zero, defaults to 1m.
	UploadDelay time.Duration

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

	// Start writeback watcher BEFORE mount so it can detect rawstaging directory creation
	stepStart = time.Now()
	watcher, err := NewWritebackWatcher(ctx, cacheDir)
	if err != nil {
		j.logger.Warn("Failed to create writeback watcher", "error", err)
	} else {
		j.writebackWatcher = watcher
		if err := j.writebackWatcher.Start(ctx); err != nil {
			j.logger.Warn("Failed to start writeback watcher", "error", err)
			j.writebackWatcher = nil
		} else {
			j.logger.Info("Started writeback watcher before mount for directory detection")
		}
	}
	j.logger.Info("Writeback watcher setup completed", "duration", time.Since(stepStart).Seconds())

	// Mount JuiceFS
	stepStart = time.Now()

	// Determine upload delay
	uploadDelay := j.config.UploadDelay
	if uploadDelay == 0 {
		uploadDelay = time.Minute
	}
	// uploadDelay configured

	mountArgs := []string{
		"mount",
		"--no-usage-report",
		"-o", "writeback_cache",
		"--writeback",
		"--upload-delay", uploadDelay.String(),
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

	// Forward JuiceFS stdout/stderr directly to structured logger
	structured := tap.WithStructuredLogger(tap.WithLogger(context.Background(), j.logger))
	j.mountCmd.Stdout = structured
	j.mountCmd.Stderr = structured

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
		j.logger.Error("Failed to start JuiceFS mount command", "error", err)
		return fmt.Errorf("failed to start JuiceFS mount: %w", err)
	}
	j.logger.Debug("JuiceFS mount command started", "pid", j.mountCmd.Process.Pid, "elapsed", time.Since(stepStart))

	// Logs are forwarded via Stdout/Stderr to the structured writer; no analysis

	// Do not Wait() here; monitorProcess handles Wait().
	// NOTE: Signal handling removed - the System component will handle signals
	// to avoid conflicts between multiple signal handlers

	// Start the process monitor (no longer responsible for closing mountReady)
	tap.Go(j.logger, j.errCh, j.monitorProcess)
	j.logger.Debug("Process monitor setup completed", "duration", time.Since(time.Now()).Seconds())

	// Start readiness polling without timeouts; will honor ctx cancellation and emit warnings
	tap.Go(j.logger, j.errCh, func() {
		j.waitForJuiceFSReady(ctx, mountPath, time.Now())
	})

	j.logger.Debug("Waiting for JuiceFS mount to be ready...")
	waitStart := time.Now()

	// Wait indefinitely for readiness (bounded only by ctx)
	if err := j.WhenReady(ctx); err != nil {
		// Kill mount process if it's still running
		if j.mountCmd != nil && j.mountCmd.Process != nil {
			j.mountCmd.Process.Kill()
		}
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

	// Writeback watcher was already started before mount

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
	j.logger.Debug("JuiceFS.Stop() called", "contextErr", ctx.Err())

	// NOTE: Signal handling removed from JuiceFS to avoid conflicts

	// If we're still starting up, wait for startup to complete before shutting down
	// This prevents race conditions where shutdown happens during mount initialization
	if j.started {
		j.logger.Debug("JuiceFS is still starting up, waiting for startup to complete before shutdown...")

		// Wait for mount to be ready with a reasonable timeout
		// Use a shorter timeout for shutdown context to avoid hanging
		startupCtx, startupCancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer startupCancel()

		if err := j.WhenReady(startupCtx); err != nil {
			j.logger.Warn("Startup did not complete before shutdown", "error", err)
			// Continue with shutdown even if startup didn't complete
		} else {
			j.logger.Debug("Startup completed, proceeding with shutdown")
		}
	}

	// Signal stop
	select {
	case <-j.stopCh:
		// Already stopping
		j.logger.Debug("JuiceFS already stopping")
	default:
		j.logger.Debug("Closing JuiceFS stop channel")
		close(j.stopCh)
	}

	// Wait for stopped signal
	// We wait indefinitely unless the context is cancelled
	// This ensures all data is properly flushed to backend storage
	j.logger.Debug("Waiting for JuiceFS monitor process to complete...")
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
			err := j.mountCmd.Wait()
			if err != nil {
				j.logger.Error("JuiceFS mount process exited with error", "error", err, "exitCode", j.mountCmd.ProcessState.ExitCode())
			} else {
				j.logger.Info("JuiceFS mount process exited cleanly", "exitCode", j.mountCmd.ProcessState.ExitCode())
			}
			processDone <- err
		} else {
			processDone <- nil
		}
	})

	select {
	case err := <-processDone:
		// Process exited unexpectedly before stop signal
		j.logger.Error("JuiceFS mount process exited unexpectedly, exiting immediately", "error", err, "elapsed", time.Since(start), "exit_code", 1)
		j.signalMountError(fmt.Errorf("mount process exited unexpectedly: %w", err))
		os.Exit(1)
	case <-j.stopCh:
		// Stop requested, check for dependent mounts
		j.logger.Debug("Checking for dependent mounts before JuiceFS umount")
		dependentMounts, err := j.findDependentMounts(mountPath)
		if err != nil {
			j.logger.Warn("Error checking for dependent mounts", "error", err, "mountPath", mountPath)
		} else if len(dependentMounts) > 0 {
			// Cannot stop JuiceFS while dependent mounts exist
			mountList := make([]string, len(dependentMounts))
			for i, mount := range dependentMounts {
				mountList[i] = fmt.Sprintf("%s (type: %s, device: %s)", mount.mountPoint, mount.fsType, mount.device)
			}
			err := fmt.Errorf("cannot stop JuiceFS, there are %d mount(s) relying on it:\n  - %s",
				len(dependentMounts), strings.Join(mountList, "\n  - "))
			j.logger.Error("Cannot stop JuiceFS with dependent mounts", "error", err, "mounts", mountList, "mountPath", mountPath)

			// Set mount error and signal failure
			j.mountErrorMu.Lock()
			j.mountError = err
			j.mountErrorMu.Unlock()

			// Signal error through errCh
			select {
			case j.errCh <- err:
			default:
			}

			return
		} else {
			j.logger.Debug("No dependent mounts found")
		}

		// If mount was never ready, skip umount; kill process if running
		select {
		case <-j.mountReady:
			// mountReady closed (ready or failed) - proceed to umount path below
		default:
			j.logger.Info("Stop received before mount was ready; skipping juicefs umount and terminating mount process")
			if j.mountCmd != nil && j.mountCmd.Process != nil {
				_ = j.mountCmd.Process.Kill()
			}
			// Unblock Start waiters with cancellation
			j.signalMountError(context.Canceled)
			// Stop watcher if it was started
			if j.writebackWatcher != nil {
				j.logger.Info("Stopping writeback watcher (pre-ready)")
				_ = j.writebackWatcher.Stop()
			}
			// Wait for process exit quickly
			select {
			case err := <-processDone:
				if err != nil {
					j.logger.Warn("JuiceFS mount process exited with error after pre-ready stop", "error", err)
				}
			case <-time.After(3 * time.Second):
				j.logger.Warn("Timeout waiting for JuiceFS process to exit after pre-ready stop")
			}
			return
		}

		// Sync the JuiceFS filesystem to flush pending writes
		j.logger.Debug("Syncing JuiceFS filesystem before umount", "path", mountPath)
		syncStart := time.Now()
		syncCmd := exec.Command("sync", "-f", mountPath)
		if output, err := syncCmd.CombinedOutput(); err != nil {
			j.logger.Warn("Sync failed for JuiceFS mount", "error", err)
			if len(output) > 0 {
				j.logger.Debug("Sync stderr/stdout", "output", string(output))
			}
		} else {
			j.logger.Debug("JuiceFS filesystem sync completed", "path", mountPath, "duration", time.Since(syncStart))
		}

		// Log writeback watcher status for diagnostics, but don't wait for flush
		// The umount --flush command below will handle flushing all pending data
		if j.writebackWatcher != nil {
			j.logger.Debug("Checking writeback watcher status (for diagnostics only)")
			readyCtx, readyCancel := context.WithTimeout(context.Background(), 1*time.Second)
			defer readyCancel()
			if err := j.writebackWatcher.WaitUntilReady(readyCtx); err == nil {
				initialPending := j.writebackWatcher.GetPendingCount()
				initialNonZero := j.writebackWatcher.GetNonZeroPendingCount()
				j.logger.Debug("Writeback watcher status before unmount",
					"totalPending", initialPending,
					"nonZeroPending", initialNonZero)
			} else {
				j.logger.Debug("Writeback watcher not ready yet", "error", err)
			}
		}

		// Trigger a cache flush via the JuiceFS control file before unmounting
		// This blocks until JuiceFS acknowledges the FlushNow command
		controlFile := filepath.Join(mountPath, ".control")
		if err := j.flushCacheViaControl(controlFile); err != nil {
			j.logger.Warn("Failed to flush cache via control file before umount", "error", err)
		}

		// Unmount JuiceFS with --flush to ensure all data is written
		// No timeout - allow umount to take as long as needed for data integrity
		// Retry indefinitely until success; failure to unmount is a stop-the-world condition
		shutdownStart := time.Now()
		j.logger.Debug("Starting JuiceFS umount with --flush", "path", mountPath)

		for attempt := 1; ; attempt++ {
			cmd := exec.Command("juicefs", "umount", "--flush", mountPath)
			stdout, _ := cmd.StdoutPipe()
			stderr, _ := cmd.StderrPipe()
			cmd.Env = append(os.Environ(), "JUICEFS_LOG_FORMAT=json")

			j.logger.Debug("Launching juicefs umount process", "attempt", attempt)
			if err := cmd.Start(); err != nil {
				j.logger.Error("Failed to start juicefs umount", "error", err, "attempt", attempt, "path", mountPath)
				continue
			}

			// Use watcher-style logging for umount output
			structured := tap.WithStructuredLogger(tap.WithLogger(context.Background(), j.logger))
			watcher := NewOutputWatcher(j.logger, mountPath, structured)
			watcher.Watch(stdout, stderr)

			if err := cmd.Wait(); err != nil {
				j.logger.Warn("juicefs umount exited with error", "error", err, "attempt", attempt, "path", mountPath)
				// Retry all umount failures - most are transient (device busy, I/O errors, etc.)
				continue
			}

			// Success
			j.logger.Debug("juicefs umount completed successfully", "duration", time.Since(shutdownStart), "attempt", attempt, "path", mountPath)
			break
		}

		// Verify the mount is actually gone from /proc/mounts before proceeding
		j.logger.Debug("Verifying JuiceFS mount removal from /proc/mounts", "path", mountPath)
		for {
			if !isMountPresent(mountPath) {
				j.logger.Debug("Confirmed JuiceFS mount removed from /proc/mounts", "path", mountPath)
				break
			}
			// Sleep briefly to avoid busy loop; no upper timeout by design
			time.Sleep(200 * time.Millisecond)
		}

		// Log writeback stats after unmount to see if any files were left behind
		if j.writebackWatcher != nil {
			j.writebackWatcher.LogStats()

			// Now stop the watcher
			j.logger.Info("Stopping writeback watcher...")
			if err := j.writebackWatcher.Stop(); err != nil {
				j.logger.Warn("Error stopping writeback watcher", "error", err)
			}
		}

		// Wait for the mount process to fully exit (no timeout)
		// The umount command tells JuiceFS to unmount, but the process may take
		// a moment to clean up and exit; do not proceed until it does
		j.logger.Debug("Waiting for JuiceFS mount process to exit after umount (no timeout)...")
		processExitStart := time.Now()
		if err := <-processDone; err != nil {
			j.logger.Warn("JuiceFS mount process exited with error", "error", err, "duration", time.Since(processExitStart))
		} else {
			j.logger.Debug("JuiceFS mount process exited cleanly", "duration", time.Since(processExitStart))
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

		// Process exited unexpectedly after mount was ready - exit immediately
		j.logger.Error("JuiceFS mount process exited unexpectedly, exiting immediately", "error", err, "exit_code", 1)
		os.Exit(1)

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

// GetPid returns the PID of the JuiceFS mount process, or 0 if not running
func (j *JuiceFS) GetPid() int {
	if j.mountCmd != nil && j.mountCmd.Process != nil {
		return j.mountCmd.Process.Pid
	}
	return 0
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

// WaitForWritebackFlush waits for all pending writeback uploads to complete
// Returns the number of files that were pending and the error if any
func (j *JuiceFS) WaitForWritebackFlush(ctx context.Context) (int64, error) {
	mountPath := j.GetMountPath()
	controlFile := filepath.Join(mountPath, ".control")

	// First, trigger immediate cache flush via JuiceFS control file
	if err := j.flushCacheViaControl(controlFile); err != nil {
		j.logger.Warn("Failed to flush cache via control file", "error", err)
		// Continue with writeback watcher even if control flush fails
	}

	if j.writebackWatcher == nil {
		return 0, nil
	}
	return j.writebackWatcher.WaitForUploads(ctx)
}

// flushCacheViaControl triggers an immediate cache flush via JuiceFS control file
// Writes command 1009 (flush cache) to the .control file and reads back the response
func (j *JuiceFS) flushCacheViaControl(controlFile string) error {
	startTime := time.Now()
	j.logger.Info("Starting cache flush via control file", "controlFile", controlFile)

	// Check if control file exists
	fileInfo, err := os.Stat(controlFile)
	if err != nil {
		j.logger.Error("Control file stat failed", "controlFile", controlFile, "error", err)
		return fmt.Errorf("failed to stat control file: %w", err)
	}
	j.logger.Debug("Control file info", "size", fileInfo.Size(), "mode", fileInfo.Mode(), "modTime", fileInfo.ModTime())

	// Open the control file for read/write (FIFO-like behavior)
	j.logger.Debug("Opening control file for read/write", "controlFile", controlFile, "flags", "O_RDWR")
	file, err := os.OpenFile(controlFile, os.O_RDWR, 0)
	if err != nil {
		j.logger.Error("Failed to open control file", "controlFile", controlFile, "error", err)
		return fmt.Errorf("failed to open control file: %w", err)
	}
	defer file.Close()
	j.logger.Debug("Control file opened for read/write")

	// Write 8-byte big-endian message: cmd (1009) and size (0)
	command := uint32(1009)
	size := uint32(0)
	j.logger.Debug("Writing flush command to control file", "command", command, "size", size, "bytes", 8)
	if err := binary.Write(file, binary.BigEndian, command); err != nil {
		j.logger.Error("Failed to write flush command", "command", command, "error", err)
		return fmt.Errorf("failed to write flush command: %w", err)
	}
	if err := binary.Write(file, binary.BigEndian, size); err != nil {
		j.logger.Error("Failed to write flush size", "size", size, "error", err)
		return fmt.Errorf("failed to write flush size: %w", err)
	}
	j.logger.Debug("Flush command written successfully, syncing to ensure write is flushed")

	// Sync to ensure write is flushed
	if err := file.Sync(); err != nil {
		j.logger.Warn("Failed to sync control file", "error", err)
		// Continue anyway - sync might not be supported on FIFO
	}

	j.logger.Debug("Flush command sent to JuiceFS, attempting to read response")

	// Read 1 byte response (should be 1 for success per FlushNow contract)
	response := make([]byte, 1)
	j.logger.Debug("Reading response from control file", "expectedBytes", 1)

	// Some environments can briefly return EOF if the response isn't ready yet.
	// Retry a few times with short backoff before failing. Track attempts and wait time.
	var n int
	var readErr error
	attempts := 0
	readStart := time.Now()
	for attempt := 1; attempt <= 20; attempt++ { // up to ~200ms total
		attempts = attempt
		n, readErr = file.Read(response)
		if readErr == nil && n == 1 {
			break
		}
		if readErr == io.EOF {
			time.Sleep(10 * time.Millisecond)
			continue
		}
		// Non-EOF error: fail fast
		j.logger.Error("Failed to read control file response",
			"bytesRead", n,
			"error", readErr,
			"errorType", fmt.Sprintf("%T", readErr))
		return fmt.Errorf("failed to read control file response: %w", readErr)
	}
	if readErr != nil {
		j.logger.Error("Failed to read control file response after retries",
			"bytesRead", n,
			"error", readErr,
			"errorType", fmt.Sprintf("%T", readErr),
			"attempts", attempts,
			"waitDuration", time.Since(readStart))
		return fmt.Errorf("failed to read control file response: %w", readErr)
	}
	j.logger.Debug("Control file response received",
		"bytesRead", n,
		"response", response[0],
		"attempts", attempts,
		"waitDuration", time.Since(readStart))

	if response[0] != 1 {
		j.logger.Error("Control file returned unexpected response", "response", response[0])
		return fmt.Errorf("control file returned unexpected response: %d", response[0])
	}

	duration := time.Since(startTime)
	j.logger.Info("Successfully triggered cache flush via control file", "duration", duration)
	return nil
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
	// No-op: logs are already wired via Cmd.Stdout/Stderr to structured writer
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

// isJuiceFSMounted checks /proc/self/mountinfo for a JuiceFS mount at mountPath
func (j *JuiceFS) isJuiceFSMounted(mountPath string) bool {
	data, err := os.ReadFile("/proc/self/mountinfo")
	if err != nil {
		return false
	}
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		if strings.TrimSpace(line) == "" {
			continue
		}
		parts := strings.Split(line, " - ")
		if len(parts) != 2 {
			continue
		}
		left := strings.Fields(parts[0])
		right := strings.Fields(parts[1])
		if len(left) < 5 || len(right) < 2 {
			continue
		}
		mp := left[4]
		fstype := right[0]
		// source := right[1] // may be "SpriteFS" depending on fuse version
		// superopts := strings.Join(right[2:], " ")
		if mp == mountPath && (fstype == "fuse.juicefs" || fstype == "juicefs") {
			return true
		}
	}
	return false
}

// verifyMountReadiness performs minimal, decisive checks:
// 1) kernel reports a JuiceFS mount at mountPath (via /proc/self/mountinfo)
// 2) the JuiceFS control file exists and opens RW
func (j *JuiceFS) verifyMountReadiness(mountPath string) bool {
	if !j.isJuiceFSMounted(mountPath) {
		return false
	}
	controlFile := filepath.Join(mountPath, ".control")
	if _, err := os.Stat(controlFile); err != nil {
		return false
	}
	f, err := os.OpenFile(controlFile, os.O_RDWR, 0)
	if err != nil {
		return false
	}
	_ = f.Close()
	return true
}

// waitForJuiceFSReady polls for mount readiness every 100ms, emits periodic warnings,
// and signals readiness when thorough verification passes.
func (j *JuiceFS) waitForJuiceFSReady(ctx context.Context, mountPath string, startTime time.Time) {
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	firstWarn10s := false
	firstWarn30s := false
	lastMinuteWarn := time.Time{}

	for {
		select {
		case <-ticker.C:
			if j.verifyMountReadiness(mountPath) {
				j.logger.Debug("Mount verified as ready", "timeSinceStart", time.Since(startTime).Seconds())
				if err := j.performPostMountSetup(mountPath, startTime); err != nil {
					j.mountErrorMu.Lock()
					j.mountError = err
					j.mountErrorMu.Unlock()
				}
				close(j.mountReady)
				return
			}
			elapsed := time.Since(startTime)
			if !firstWarn10s && elapsed >= 10*time.Second {
				j.logger.Warn("JuiceFS mount is taking longer than expected (10s)... waiting")
				firstWarn10s = true
			} else if !firstWarn30s && elapsed >= 30*time.Second {
				j.logger.Warn("JuiceFS mount is taking longer than expected (30s)... waiting")
				firstWarn30s = true
			} else if elapsed >= 30*time.Second {
				if lastMinuteWarn.IsZero() || time.Since(lastMinuteWarn) >= time.Minute {
					j.logger.Warn("JuiceFS mount still not ready... continuing to wait", "elapsed", elapsed.String())
					lastMinuteWarn = time.Now()
				}
			}
		case <-ctx.Done():
			j.signalMountError(ctx.Err())
			return
		}
	}
}

// performPostMountSetup handles the tasks that need to be done after mount is ready
func (j *JuiceFS) performPostMountSetup(mountPath string, startTime time.Time) error {
	// Create the active directory
	stepStart := time.Now()
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

type mountInfo struct {
	device     string
	mountPoint string
	fsType     string
	options    string
}

// findDependentMounts finds all mounts that depend on the JuiceFS mount but does not unmount them
func (j *JuiceFS) findDependentMounts(juicefsMountPath string) ([]mountInfo, error) {
	// Read /proc/mounts to find all current mounts
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return nil, fmt.Errorf("failed to read /proc/mounts: %w", err)
	}

	var dependentMounts []mountInfo
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
			dependentMounts = append(dependentMounts, mount)
		}
	}

	return dependentMounts, nil
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

// isMountPresent checks /proc/mounts for the given mount path
func isMountPresent(mountPath string) bool {
	mountsData, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}
	return strings.Contains(string(mountsData), mountPath)
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
