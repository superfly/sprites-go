package overlay

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
)

// Manager manages the root overlay loopback mount
//
// The overlay provides a writable filesystem layer that can be:
// - Frozen during checkpoints to ensure consistency
// - Unmounted and remounted during restore operations
// - Automatically managed alongside the JuiceFS lifecycle
//
// The overlay uses a 100GB sparse ext4 image stored at:
// ${JUICEFS_BASE}/data/active/root-upper.img
//
// And is mounted at:
// /mnt/user-data
type Manager struct {
	baseDir   string
	imagePath string
	mountPath string
	imageSize string
	logger    *slog.Logger

	// Overlayfs configuration
	lowerPaths        []string // Lower directories (e.g., ["/mnt/base1", "/mnt/base2", "/mnt/system-base"])
	overlayTargetPath string   // Where to mount the overlay (e.g., /mnt/newroot)
	skipOverlayFS     bool     // Skip overlayfs mounting (for testing)

	// Readiness tracking
	mountReady   chan struct{} // Closed when mount is complete
	mountError   error         // Error if mount fails
	mountErrorMu sync.RWMutex  // Protect mountError
	mountOnce    sync.Once     // Ensure mount ready is only signaled once

	// Lifecycle channels
	stopCh    chan struct{} // Signals shutdown request
	stoppedCh chan struct{} // Closed when shutdown complete
	errCh     chan error    // Reports panics from goroutines
	started   bool          // Track if Start() has been called

	// Loop device path used for the root image when attached explicitly
	loopDevice string

	// Checkpoint infrastructure
	checkpointBasePath     string                          // Path to checkpoints directory (e.g., /juicefs/mount/data/checkpoints)
	checkpointMountPath    string                          // Base path for checkpoint mounts (/.sprite/checkpoints)
	checkpointMounts       map[string]string               // Map of checkpoint name to mount path
	checkpointLoopDevices  map[string]string               // Map of checkpoint name to loop device
	checkpointMu           sync.Mutex                      // Protects checkpoint mount state
	activeCheckpointMount  string                          // Path where active upper dir is mounted (/.sprite/checkpoints/active)
	checkpointDB           *checkpointDB                   // Checkpoint database
	checkpointFS           *filesystemOps                  // Filesystem operations for checkpoints
	checkpointPrepare      PrepFunc                        // Prepare function for checkpoints
	restorePrepare         PrepFunc                        // Prepare function for restores
	onCheckpointCreated    func(ctx context.Context) error // Callback when checkpoint is created
	juicefsBasePath        string                          // JuiceFS base path for checkpoint operations
	restoreContainerPrep   func(ctx context.Context) error // Callback to shutdown container before restore
	restoreContainerResume func(ctx context.Context) error // Callback to boot container after restore

	// Verifiers for external resources
	// These check actual system state, not internal Go values
	setupVerifiers   []func(context.Context) error // verify resources exist
	cleanupVerifiers []func(context.Context) error // verify resources cleaned up
}

// Config holds configuration for the overlay manager
type Config struct {
	BaseDir             string
	ImageSize           string   // Default: "100G"
	MountPath           string   // Default: "/mnt/user-data"
	LowerPaths          []string // Lower directories for overlayfs
	OverlayTargetPath   string   // Default: "/mnt/newroot"
	CheckpointMountPath string   // Default: "/.sprite/checkpoints"
	SkipOverlayFS       bool     // Skip overlayfs mounting
	Logger              *slog.Logger
}

// New creates a new overlay manager instance
func New(config Config) *Manager {
	if config.Logger == nil {
		config.Logger = slog.Default()
	}
	if config.ImageSize == "" {
		config.ImageSize = "100G"
	}
	if config.MountPath == "" {
		config.MountPath = "/mnt/user-data"
	}
	if config.OverlayTargetPath == "" {
		config.OverlayTargetPath = "/mnt/newroot"
	}
	if config.CheckpointMountPath == "" {
		config.CheckpointMountPath = "/.sprite/checkpoints"
	}
	if len(config.LowerPaths) == 0 {
		config.LowerPaths = []string{"/mnt/system-base"}
	}

	dataPath := filepath.Join(config.BaseDir, "data")
	checkpointMountBase := config.CheckpointMountPath
	return &Manager{
		baseDir:               config.BaseDir,
		imagePath:             filepath.Join(dataPath, "active", "root-upper.img"),
		mountPath:             config.MountPath,
		imageSize:             config.ImageSize,
		lowerPaths:            config.LowerPaths,
		overlayTargetPath:     config.OverlayTargetPath,
		skipOverlayFS:         config.SkipOverlayFS,
		logger:                config.Logger,
		mountReady:            make(chan struct{}),
		stopCh:                make(chan struct{}),
		stoppedCh:             make(chan struct{}),
		errCh:                 make(chan error, 1),
		checkpointBasePath:    filepath.Join(dataPath, "checkpoints"),
		checkpointMountPath:   checkpointMountBase,
		checkpointMounts:      make(map[string]string),
		checkpointLoopDevices: make(map[string]string),
		activeCheckpointMount: filepath.Join(checkpointMountBase, "active"),
		juicefsBasePath:       filepath.Join(config.BaseDir, "data"),
	}
}

// GetMountPath returns the path where the overlay is mounted
func (m *Manager) GetMountPath() string {
	return m.mountPath
}

// GetImagePath returns the path to the overlay image file
func (m *Manager) GetImagePath() string {
	return m.imagePath
}

// SetLowerPaths sets the paths to the lower directories for overlay
func (m *Manager) SetLowerPaths(paths []string) {
	m.lowerPaths = paths
}

// GetLowerPaths returns the configured lower directory paths
func (m *Manager) GetLowerPaths() []string {
	return m.lowerPaths
}

// GetOverlayTargetPath returns the configured overlay target path
func (m *Manager) GetOverlayTargetPath() string {
	return m.overlayTargetPath
}

// SetRestoreContainerCallbacks sets callbacks for container shutdown/boot during restore
func (m *Manager) SetRestoreContainerCallbacks(prep func(ctx context.Context) error, resume func(ctx context.Context) error) {
	m.restoreContainerPrep = prep
	m.restoreContainerResume = resume
}

// Start mounts the overlay and initializes checkpoint infrastructure
// This is the main entry point for starting the overlay manager
func (m *Manager) Start(ctx context.Context, checkpointDBPath string) error {
	if m.started {
		return fmt.Errorf("overlay manager already started")
	}
	m.started = true

	// Clear verifiers from any previous run
	m.setupVerifiers = nil
	m.cleanupVerifiers = nil

	// Recreate channels if they were closed by a previous Unmount()
	// This enables restart after Unmount()
	select {
	case <-m.stopCh:
		m.stopCh = make(chan struct{})
	default:
	}
	select {
	case <-m.stoppedCh:
		m.stoppedCh = make(chan struct{})
	default:
	}
	select {
	case <-m.mountReady:
		m.mountReady = make(chan struct{})
	default:
	}

	// Prepare and mount the overlay filesystem (creates image if needed)
	if err := m.PrepareAndMount(ctx); err != nil {
		// PrepareAndMount already handles cleanup via Mount() error handling
		// Close channels to signal completion
		// Keep started=true to prevent double-start attempts
		select {
		case <-m.stopCh:
			// Already closed
		default:
			close(m.stopCh)
		}
		select {
		case <-m.stoppedCh:
			// Already closed
		default:
			close(m.stoppedCh)
		}
		return fmt.Errorf("failed to mount overlay: %w", err)
	}

	// Set up checkpoint mount directory
	if err := m.SetupCheckpointMountBase(ctx); err != nil {
		m.logger.Warn("Failed to setup checkpoint mount base", "error", err)
	}

	// Initialize checkpoint manager (must be ready for checkpoint operations)
	if err := m.InitializeCheckpointManager(ctx, checkpointDBPath); err != nil {
		m.logger.Warn("Failed to initialize checkpoint manager", "error", err)
	}

	// Mount existing checkpoints - this blocks until all parallel mounts complete
	// Individual checkpoint mounts run in parallel internally
	if err := m.MountCheckpoints(ctx); err != nil {
		m.logger.Error("Failed to mount checkpoints", "error", err)
		// Cleanup: unmount the overlay we just mounted
		m.logger.Info("Cleaning up overlay mount after checkpoint mount failure")
		cleanupCtx := context.Background()
		if unmountErr := m.Unmount(cleanupCtx); unmountErr != nil {
			m.logger.Error("Failed to cleanup overlay after checkpoint mount failure", "error", unmountErr)
		}
		return fmt.Errorf("failed to mount checkpoints: %w", err)
	}

	// Add verifiers for external resources now that setup is complete
	// These check ONLY system state, not internal Go values
	m.addResourceVerifiers()

	return nil
}

// Wait blocks until Unmount completes or a panic occurs in any goroutine
func (m *Manager) Wait() error {
	select {
	case <-m.stoppedCh:
		return nil
	case err := <-m.errCh:
		return err
	}
}

// UpdateImagePath updates the image path after a restore operation
func (m *Manager) UpdateImagePath() {
	dataPath := filepath.Join(m.baseDir, "data")
	m.imagePath = filepath.Join(dataPath, "active", "root-upper.img")
}

// InitializeCheckpointManager creates the checkpoint manager after filesystem is mounted
func (m *Manager) InitializeCheckpointManager(ctx context.Context, checkpointDBPath string) error {
	if checkpointDBPath == "" {
		m.logger.Debug("Checkpoint database path not configured, skipping checkpoint manager initialization")
		return nil
	}

	m.logger.Info("Initializing checkpoint manager", "dbPath", checkpointDBPath, "fsBaseDir", m.juicefsBasePath)

	// Create the checkpoint database
	db, err := newCheckpointDB(checkpointDBConfig{
		DBPath: checkpointDBPath,
		Logger: m.logger,
	})
	if err != nil {
		return fmt.Errorf("init checkpoint db: %w", err)
	}
	m.checkpointDB = db

	// Query existing checkpoints before initialization
	existingCheckpoints, err := db.listAll()
	if err != nil {
		db.Close()
		return fmt.Errorf("list existing checkpoints: %w", err)
	}

	m.logger.Info("Checkpoint database initialized", "existingCheckpoints", len(existingCheckpoints))

	// Create v0 directory if it doesn't exist
	v0Path := filepath.Join(m.juicefsBasePath, "checkpoints", "v0")
	if _, err := os.Stat(v0Path); os.IsNotExist(err) {
		if err := os.MkdirAll(v0Path, 0755); err != nil {
			db.Close()
			return fmt.Errorf("create v0 checkpoint directory: %w", err)
		}
		m.logger.Info("Created empty v0 checkpoint directory", "path", v0Path)
	}

	// Create filesystem ops
	m.checkpointFS = newFilesystemOps(m.juicefsBasePath, []string{"juicefs", "clone"}, m.logger)

	// Check for orphaned checkpoint directories on disk
	if err := renameOrphanedCheckpoints(m.juicefsBasePath, existingCheckpoints, m.logger); err != nil {
		m.logger.Warn("Failed to clean up orphaned checkpoints", "error", err)
	}

	// Compose checkpoint preparation chain: overlay freeze wraps noop
	final := NoopPrep()
	m.checkpointPrepare = prepareCheckpoint(m, final)

	// Compose restore preparation chain: overlay unmount/mount
	m.restorePrepare = prepareRestore(m, final)

	// Set up callback to update overlay checkpoint mounts when new checkpoints are created
	m.onCheckpointCreated = func(ctx context.Context) error {
		return m.OnCheckpointCreated(ctx)
	}

	m.logger.Info("Checkpoint manager initialized successfully")
	return nil
}

// addResourceVerifiers populates the setup and cleanup verifiers
// Called at the end of Start() after all resources are acquired
func (m *Manager) addResourceVerifiers() {
	// Setup verifier: Check loop device is attached
	m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
		if m.loopDevice == "" {
			// No loop device was attached (might be using direct mount)
			return nil
		}

		// Check if loop device exists using losetup -a
		cmd := exec.Command("losetup", "-a")
		output, err := cmd.Output()
		if err != nil {
			return fmt.Errorf("failed to run losetup -a: %w", err)
		}

		if !strings.Contains(string(output), m.loopDevice) {
			return fmt.Errorf("loop device not found: %s (hint: check 'losetup -a')", m.loopDevice)
		}
		return nil
	})

	// Setup verifier: Check loopback mount exists in /proc/mounts
	m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
		mountsData, err := os.ReadFile("/proc/mounts")
		if err != nil {
			return fmt.Errorf("failed to read /proc/mounts: %w", err)
		}

		if !strings.Contains(string(mountsData), m.mountPath) {
			return fmt.Errorf("loopback mount not found in /proc/mounts: %s", m.mountPath)
		}
		return nil
	})

	// Setup verifier: Check overlayfs mount exists in /proc/mounts (if not skipped)
	if !m.skipOverlayFS {
		m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
			mountsData, err := os.ReadFile("/proc/mounts")
			if err != nil {
				return fmt.Errorf("failed to read /proc/mounts: %w", err)
			}

			if !strings.Contains(string(mountsData), m.overlayTargetPath) {
				return fmt.Errorf("overlayfs mount not found in /proc/mounts: %s", m.overlayTargetPath)
			}
			return nil
		})
	}

	// Cleanup verifier: Check loop device is detached
	m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
		if m.loopDevice == "" {
			// No loop device was used
			return nil
		}

		// Check if loop device still exists using losetup -a
		cmd := exec.Command("losetup", "-a")
		output, err := cmd.Output()
		if err != nil {
			// If losetup fails, we can't verify but that's OK
			return nil
		}

		if strings.Contains(string(output), m.loopDevice) {
			return fmt.Errorf("loop device still attached: %s (hint: check 'losetup -a')", m.loopDevice)
		}
		return nil
	})

	// Cleanup verifier: Check loopback mount is gone from /proc/mounts
	m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
		mountsData, err := os.ReadFile("/proc/mounts")
		if err != nil {
			// If we can't read /proc/mounts, we can't verify
			return nil
		}

		if strings.Contains(string(mountsData), m.mountPath) {
			return fmt.Errorf("loopback mount still present in /proc/mounts: %s (hint: check 'mount | grep %s')", m.mountPath, m.mountPath)
		}
		return nil
	})

	// Cleanup verifier: Check overlayfs mount is gone from /proc/mounts
	if !m.skipOverlayFS {
		m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
			mountsData, err := os.ReadFile("/proc/mounts")
			if err != nil {
				// If we can't read /proc/mounts, we can't verify
				return nil
			}

			if strings.Contains(string(mountsData), m.overlayTargetPath) {
				return fmt.Errorf("overlayfs mount still present in /proc/mounts: %s (hint: check 'mount | grep %s')", m.overlayTargetPath, m.overlayTargetPath)
			}
			return nil
		})
	}
}

// SetupVerifiers returns functions that verify resources are set up correctly
// Each function checks actual system state (loop devices, mounts, etc.)
func (m *Manager) SetupVerifiers() []func(context.Context) error {
	return m.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
// Each function checks actual system state (loop devices, mounts, etc.)
func (m *Manager) CleanupVerifiers() []func(context.Context) error {
	return m.cleanupVerifiers
}

// Close closes the checkpoint database
func (m *Manager) Close() error {
	if m.checkpointDB != nil {
		return m.checkpointDB.Close()
	}
	return nil
}
