package system

import (
	"context"
	"fmt"
	"os"
	"path/filepath"

	"github.com/superfly/sprite-env/pkg/checkpoint"
	"github.com/superfly/sprite-env/pkg/db"
	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/overlay"
)

// initializeStorage initializes storage components in order: DB → JuiceFS → Overlay
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
	if s.config.OverlayEnabled {
		if err := s.initializeOverlay(); err != nil {
			return fmt.Errorf("failed to initialize overlay: %w", err)
		}
	}

	// 4. Initialize checkpoint manager (wraps all storage components)
	if err := s.initializeCheckpointManager(); err != nil {
		return fmt.Errorf("failed to initialize checkpoint manager: %w", err)
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

	dbConfig := db.Config{
		BaseDir:           s.config.WriteDir,
		S3AccessKey:       s.config.S3AccessKey,
		S3SecretAccessKey: s.config.S3SecretAccessKey,
		S3EndpointURL:     s.config.S3EndpointURL,
		S3Bucket:          s.config.S3Bucket,
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
		BaseDir:           s.config.JuiceFSDataPath,
		ImageSize:         s.config.OverlayImageSize,
		MountPath:         "/mnt/user-data",
		LowerPaths:        s.config.GetOverlayLowerPaths(),
		OverlayTargetPath: s.config.OverlayTargetPath,
		SkipOverlayFS:     s.config.OverlaySkipOverlayFS,
		Logger:            s.logger,
	}

	overlayMgr := overlay.New(overlayConfig)

	s.OverlayManager = overlayMgr

	return nil
}

// initializeCheckpointManager creates the checkpoint manager
func (s *System) initializeCheckpointManager() error {
	// Require JuiceFS to be configured, since checkpoint operations require it
	if s.JuiceFS == nil {
		return fmt.Errorf("checkpoint manager requires JuiceFS to be configured")
	}

	// Build checkpoint manager with DB path, filesystem base, and juicefs clone command
	checkpointDBDir := filepath.Join(s.config.WriteDir, "checkpoints")
	if err := os.MkdirAll(checkpointDBDir, 0755); err != nil {
		return fmt.Errorf("ensure checkpoint db dir: %w", err)
	}
	dbPath := filepath.Join(checkpointDBDir, "checkpoints.db")
	fsBaseDir := s.JuiceFS.GetMountPath()
	copyCommand := []string{"juicefs", "clone"}

	// Compose checkpoint preparation chain: overlay wraps final
	final := checkpoint.NoopPrep()
	var checkpointPrep checkpoint.PrepFunc
	if s.OverlayManager != nil {
		checkpointPrep = overlay.PrepareCheckpoint(s.OverlayManager, final)
	} else {
		checkpointPrep = final
	}

	// Compose restore preparation chain: shutdown container, then overlay, then boot back
	restorePrep := func(ctx context.Context) (func() error, error) {
		// Shutdown container before restore
		s.logger.Info("Restore prep: shutting down container")
		if err := s.ShutdownContainer(ctx); err != nil {
			return nil, fmt.Errorf("shutdown container for restore: %w", err)
		}

		// Then run overlay restore prep if available
		var overlayResume func() error
		if s.OverlayManager != nil {
			overlayPrepRestore := overlay.PrepareRestore(s.OverlayManager, final)
			resume, err := overlayPrepRestore(ctx)
			if err != nil {
				return nil, fmt.Errorf("overlay restore prep: %w", err)
			}
			overlayResume = resume
		}

		// Return resume function that boots container back
		return func() error {
			// First resume overlay if needed
			if overlayResume != nil {
				if err := overlayResume(); err != nil {
					s.logger.Error("Failed to resume overlay after restore", "error", err)
				}
			}

			// Then boot container back
			s.logger.Info("Restore resume: booting container")
			if err := s.BootContainer(ctx); err != nil {
				return fmt.Errorf("boot container after restore: %w", err)
			}
			return nil
		}, nil
	}

	// Create the Manager and attach to System
	mgr, err := checkpoint.NewManager(dbPath, fsBaseDir, copyCommand, s.logger, checkpointPrep, restorePrep)
	if err != nil {
		return fmt.Errorf("init checkpoint manager: %w", err)
	}
	s.CheckpointManager = mgr
	s.logger.Info("Checkpoint manager initialized", "manager_ptr", fmt.Sprintf("%p", s.CheckpointManager))
	return nil
}
