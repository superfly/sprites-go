package overlay

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
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
}

// Config holds configuration for the overlay manager
type Config struct {
	BaseDir           string
	ImageSize         string   // Default: "100G"
	MountPath         string   // Default: "/mnt/user-data"
	LowerPaths        []string // Lower directories for overlayfs
	OverlayTargetPath string   // Default: "/mnt/newroot"
	SkipOverlayFS     bool     // Skip overlayfs mounting
	Logger            *slog.Logger
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
	if len(config.LowerPaths) == 0 {
		config.LowerPaths = []string{"/mnt/system-base"}
	}

	dataPath := filepath.Join(config.BaseDir, "data")
	// Checkpoint mounts go on the host at /.sprite/checkpoints
	checkpointMountBase := "/.sprite/checkpoints"
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
	m.onCheckpointCreated = m.OnCheckpointCreated

	m.logger.Info("Checkpoint manager initialized successfully")
	return nil
}

// Close closes the checkpoint database
func (m *Manager) Close() error {
	if m.checkpointDB != nil {
		return m.checkpointDB.Close()
	}
	return nil
}
