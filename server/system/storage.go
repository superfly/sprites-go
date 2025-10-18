package system

import (
	"context"
	"fmt"
	"os"
	"path/filepath"

	"github.com/superfly/sprite-env/pkg/db"
	"github.com/superfly/sprite-env/pkg/fly"
	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/overlay"
)

// initializeStorage initializes storage components in order: DB → JuiceFS → Overlay
// Note: Checkpoint manager is initialized by overlay manager during Mount()
func (s *System) initializeStorage() error {
	// 1. Initialize DB manager
	if err := s.initializeDBManager(); err != nil {
		return fmt.Errorf("failed to initialize DB manager: %w", err)
	}

	// 2. Initialize JuiceFS (depends on DB)
	if err := s.initializeJuiceFS(); err != nil {
		return fmt.Errorf("failed to initialize JuiceFS: %w", err)
	}

	// 3. Initialize Overlay (depends on JuiceFS)
	// Overlay will initialize checkpoint manager during Mount() when filesystem is ready
	if s.config.OverlayEnabled {
		if err := s.initializeOverlay(); err != nil {
			return fmt.Errorf("failed to initialize overlay: %w", err)
		}
	}

	return nil
}

// initializeDBManager creates the database manager
func (s *System) initializeDBManager() error {
	// Determine database paths to manage
	var dbPaths []string

	// JuiceFS metadata database if configured
	if s.config.JuiceFSDataPath != "" {
		juicefsDBPath := filepath.Join(s.config.JuiceFSDataPath, "metadata.db")
		dbPaths = append(dbPaths, juicefsDBPath)
	}

	// Checkpoints database (used by checkpoint manager)
	checkpointDBDir := filepath.Join(s.config.WriteDir, "checkpoints")
	checkpointDBPath := filepath.Join(checkpointDBDir, "checkpoints.db")
	if err := os.MkdirAll(checkpointDBDir, 0755); err == nil {
		dbPaths = append(dbPaths, checkpointDBPath)
	} else {
		// If directory can't be created now, still add intended path
		dbPaths = append(dbPaths, checkpointDBPath)
	}

	// Sprite database (stores sprite assignment info)
	// Stored in WriteDir like checkpoints, not in JuiceFS
	spriteDBPath := filepath.Join(s.config.WriteDir, "sprite.db")
	dbPaths = append(dbPaths, spriteDBPath)

	// Get HostID from environment
	var hostID string
	if s.Environment.AppName() != "" {
		// On Fly, use machine ID
		hostID = fly.Environment().MachineID
	} else {
		// Not on Fly, require HOST_ID environment variable
		hostID = os.Getenv("HOST_ID")
		if hostID == "" {
			return fmt.Errorf("HOST_ID environment variable is required for non-Fly environments")
		}
	}

	dbConfig := db.Config{
		BaseDir:           s.config.WriteDir,
		S3AccessKey:       s.config.S3AccessKey,
		S3SecretAccessKey: s.config.S3SecretAccessKey,
		S3EndpointURL:     s.config.S3EndpointURL,
		S3Bucket:          s.config.S3Bucket,
		HostID:            hostID,
		Logger:            s.logger,
		DatabasePaths:     dbPaths,
	}

	dbManager, err := db.New(dbConfig)
	if err != nil {
		return err
	}

	s.DBManager = dbManager
	return nil
}

// initializeJuiceFS creates the JuiceFS instance
func (s *System) initializeJuiceFS() error {
	s.logger.Info("Checking JuiceFS configuration",
		"JuiceFSDataPath", s.config.JuiceFSDataPath,
		"JuiceFSBaseDir", s.config.JuiceFSBaseDir,
		"WriteDir", s.config.WriteDir)

	// Only skip if truly not configured
	if s.config.JuiceFSDataPath == "" {
		s.logger.Info("JuiceFS not configured, skipping (JuiceFSDataPath is empty)")
		// TODO: Create a no-op JuiceFS implementation to avoid nil checks
		return nil
	}

	juicefsConfig := juicefs.Config{
		BaseDir:           s.config.JuiceFSDataPath,
		LocalMode:         s.config.JuiceFSLocalMode,
		S3AccessKey:       s.config.S3AccessKey,
		S3SecretAccessKey: s.config.S3SecretAccessKey,
		S3EndpointURL:     s.config.S3EndpointURL,
		S3Bucket:          s.config.S3Bucket,
		Logger:            s.logger.With("source", "juicefs"),
	}

	juiceFS, err := juicefs.New(juicefsConfig)
	if err != nil {
		return err
	}

	s.JuiceFS = juiceFS
	s.logger.Info("JuiceFS instance created", "juiceFS_ptr", fmt.Sprintf("%p", s.JuiceFS))
	return nil
}

// initializeOverlay creates the overlay manager
func (s *System) initializeOverlay() error {
	// Only check if overlay is enabled but JuiceFS is not configured
	if s.JuiceFS == nil && s.config.JuiceFSDataPath != "" {
		return fmt.Errorf("overlay requires JuiceFS but JuiceFS is not configured")
	} else if s.JuiceFS == nil {
		// Skip overlay if JuiceFS is not configured
		s.logger.Info("Skipping overlay initialization - JuiceFS not configured")
		return nil
	}

	overlayConfig := overlay.Config{
		BaseDir:             s.config.JuiceFSDataPath,
		ImageSize:           s.config.OverlayImageSize,
		MountPath:           "/mnt/user-data",
		LowerPaths:          s.config.GetOverlayLowerPaths(),
		OverlayTargetPath:   s.config.OverlayTargetPath,
		CheckpointMountPath: s.config.CheckpointMountPath,
		SkipOverlayFS:       s.config.OverlaySkipOverlayFS,
		Logger:              s.logger,
	}

	overlayMgr := overlay.New(overlayConfig)

	// Set restore container callbacks for checkpoint restore operations
	overlayMgr.SetRestoreContainerCallbacks(
		func(ctx context.Context) error {
			s.logger.Info("Restore prep: shutting down container")
			return s.ShutdownContainer(ctx)
		},
		func(ctx context.Context) error {
			s.logger.Info("Restore resume: booting container")
			return s.BootContainer(ctx)
		},
	)

	s.OverlayManager = overlayMgr

	return nil
}

// initializeCheckpointInfrastructure sets up checkpoint manager and mounts after overlay is ready
func (s *System) initializeCheckpointInfrastructure(ctx context.Context) error {
	if s.OverlayManager == nil {
		return nil
	}

	// Determine checkpoint database path
	checkpointDBDir := filepath.Join(s.config.WriteDir, "checkpoints")
	checkpointDBPath := filepath.Join(checkpointDBDir, "checkpoints.db")

	// Set up checkpoint mount directory with shared propagation
	if err := s.OverlayManager.SetupCheckpointMountBase(ctx); err != nil {
		s.logger.Warn("Failed to setup checkpoint mount base", "error", err)
		// Non-fatal - continue
	}

	// Initialize checkpoint manager
	if err := s.OverlayManager.InitializeCheckpointManager(ctx, checkpointDBPath); err != nil {
		s.logger.Warn("Failed to initialize checkpoint manager", "error", err)
		// Non-fatal - continue
	}

	// Mount checkpoints readonly at /.sprite/checkpoints/
	if err := s.OverlayManager.MountCheckpoints(ctx); err != nil {
		s.logger.Warn("Failed to mount checkpoints", "error", err)
		// Non-fatal - continue
	}

	return nil
}
