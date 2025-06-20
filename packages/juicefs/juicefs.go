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

	_ "github.com/mattn/go-sqlite3"
)

// JuiceFS manages the JuiceFS filesystem and Litestream replication
type JuiceFS struct {
	config        Config
	litestreamCmd *exec.Cmd
	mountCmd      *exec.Cmd
	mountReady    chan error
	stopCh        chan struct{}
	stoppedCh     chan struct{}
	signalCh      chan os.Signal
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

	return &JuiceFS{
		config:     config,
		mountReady: make(chan error, 1),
		stopCh:     make(chan struct{}),
		stoppedCh:  make(chan struct{}),
		signalCh:   make(chan os.Signal, 1),
	}, nil
}

// Start initializes and starts JuiceFS with Litestream replication
func (j *JuiceFS) Start(ctx context.Context) error {
	// Create necessary directories
	cacheDir := filepath.Join(j.config.BaseDir, "cache")
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
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
	if err := j.createLitestreamConfig(litestreamConfigPath, metaDB); err != nil {
		return fmt.Errorf("failed to create litestream config: %w", err)
	}

	// Check if we need to restore
	if j.config.LocalMode {
		// In local mode, check if litestream backup exists
		backupPath := filepath.Join(j.config.BaseDir, "litestream", "generations")
		if _, err := os.Stat(backupPath); err == nil {
			fmt.Println("Restoring from local litestream backup")
			restoreCmd := exec.CommandContext(ctx, "litestream", "restore",
				"-config", litestreamConfigPath,
				"-if-replica-exists",
				metaDB)

			if output, err := restoreCmd.CombinedOutput(); err != nil {
				fmt.Printf("Litestream restore output: %s\n", string(output))
			}
		}
	} else {
		// S3 mode - original logic
		if existingBucket, err := j.getExistingBucket(metaDB); err == nil && existingBucket == j.config.S3Bucket {
			fmt.Println("Using sqlite db on disk (bucket matches)")
		} else {
			// Remove existing metadata and cache
			os.Remove(metaDB)
			os.RemoveAll(cacheDir)

			fmt.Printf("Restoring juicefs db from %s\n", j.config.S3Bucket)
			// Restore from S3 using litestream
			restoreCmd := exec.CommandContext(ctx, "litestream", "restore",
				"-config", litestreamConfigPath,
				"-if-replica-exists",
				metaDB)

			restoreCmd.Env = append(os.Environ(),
				fmt.Sprintf("JUICEFS_META_DB=%s", metaDB),
				fmt.Sprintf("SPRITE_S3_ACCESS_KEY=%s", j.config.S3AccessKey),
				fmt.Sprintf("SPRITE_S3_SECRET_ACCESS_KEY=%s", j.config.S3SecretAccessKey),
				fmt.Sprintf("SPRITE_S3_ENDPOINT_URL=%s", j.config.S3EndpointURL),
				fmt.Sprintf("SPRITE_S3_BUCKET=%s", j.config.S3Bucket),
			)

			if output, err := restoreCmd.CombinedOutput(); err != nil {
				// If restore fails, it's okay - we'll format a new filesystem
				fmt.Printf("Litestream restore output: %s\n", string(output))
			}
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
	case <-time.After(30 * time.Second):
		// Kill mount process
		j.mountCmd.Process.Kill()
		// Don't call Wait() here - monitorProcess will handle it
		return fmt.Errorf("timeout waiting for JuiceFS to be ready")
	}
}

// Stop cleanly shuts down JuiceFS and Litestream
func (j *JuiceFS) Stop(ctx context.Context) error {
	// Stop signal handling
	signal.Stop(j.signalCh)

	// Signal stop
	select {
	case <-j.stopCh:
		// Already stopping
	default:
		close(j.stopCh)
	}

	// Wait for stopped signal or timeout
	select {
	case <-j.stoppedCh:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	case <-time.After(10 * time.Second):
		return fmt.Errorf("timeout waiting for JuiceFS to stop")
	}
}

// monitorProcess handles the lifecycle of the mount process
func (j *JuiceFS) monitorProcess() {
	defer close(j.stoppedCh)

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
		// Stop requested, unmount JuiceFS
		unmountCmd := exec.Command("juicefs", "umount", "--force", mountPath)
		if output, err := unmountCmd.CombinedOutput(); err != nil {
			// Check if it's exit status 3 (not mounted) - this is OK
			if exitErr, ok := err.(*exec.ExitError); ok && exitErr.ExitCode() == 3 {
				fmt.Printf("JuiceFS already unmounted at %s\n", mountPath)
			} else {
				// Log but don't fail on other unmount errors
				fmt.Printf("Warning: failed to unmount JuiceFS: %v (output: %s)\n", err, string(output))
			}
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

// Checkpoint creates a checkpoint of the active directory
func (j *JuiceFS) Checkpoint(ctx context.Context, checkpointID string) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	mountPath := filepath.Join(j.config.BaseDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	checkpointPath := filepath.Join(checkpointsDir, checkpointID)

	// Ensure checkpoints directory exists
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoints directory: %w", err)
	}

	// Check if active directory exists
	if _, err := os.Stat(activeDir); os.IsNotExist(err) {
		return fmt.Errorf("active directory does not exist at %s", activeDir)
	}

	// Check if checkpoint already exists
	if _, err := os.Stat(checkpointPath); err == nil {
		return fmt.Errorf("checkpoint %s already exists at %s", checkpointID, checkpointPath)
	}

	// Clone active directory to checkpoint
	fmt.Printf("Creating checkpoint %s...\n", checkpointID)
	cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", activeDir, checkpointPath)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to create checkpoint: %w, output: %s", err, string(output))
	}

	fmt.Printf("Checkpoint created successfully at %s\n", checkpointPath)
	return nil
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

	// If active directory exists, back it up
	if _, err := os.Stat(activeDir); err == nil {
		timestamp := time.Now().Unix()
		backupName := fmt.Sprintf("pre-restore-%s-%d", checkpointID, timestamp)
		backupPath := filepath.Join(checkpointsDir, backupName)

		fmt.Printf("Backing up current active directory to %s...\n", backupPath)
		if err := os.Rename(activeDir, backupPath); err != nil {
			return fmt.Errorf("failed to backup active directory: %w", err)
		}
		fmt.Println("Backup completed")
	}

	// Clone checkpoint to active directory
	fmt.Printf("Restoring from checkpoint %s...\n", checkpointID)
	cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", checkpointPath, activeDir)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to restore from checkpoint: %w, output: %s", err, string(output))
	}

	fmt.Printf("Restore completed successfully from %s to %s\n", checkpointPath, activeDir)
	return nil
}

// Helper functions

func (j *JuiceFS) createLitestreamConfig(configPath, metaDB string) error {
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
`, metaDB, localBackupPath)
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
`
	}

	return os.WriteFile(configPath, []byte(config), 0644)
}

func (j *JuiceFS) getExistingBucket(metaDB string) (string, error) {
	db, err := sql.Open("sqlite3", metaDB)
	if err != nil {
		return "", err
	}
	defer db.Close()

	var bucket string
	err = db.QueryRow("SELECT value FROM setting WHERE name = 'bucket'").Scan(&bucket)
	if err != nil {
		return "", err
	}

	// Extract bucket name from the stored value (format: endpoint/bucket)
	parts := strings.Split(bucket, "/")
	if len(parts) > 0 {
		return parts[len(parts)-1], nil
	}
	return bucket, nil
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
			j.mountReady <- nil
			return
		}
	}

	// If we get here, we didn't see the ready message
	j.mountReady <- fmt.Errorf("did not receive 'juicefs is ready' message")
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
