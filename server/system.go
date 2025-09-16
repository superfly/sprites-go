package main

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/leaser"
	"github.com/superfly/sprite-env/pkg/tap"
)

// SystemConfig holds configuration for the System
type SystemConfig struct {
	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessGracefulShutdownTimeout time.Duration

	// JuiceFS configuration
	JuiceFSBaseDir    string
	JuiceFSLocalMode  bool
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string

	// Overlay configuration
	OverlayEnabled       bool
	OverlayImageSize     string
	OverlayLowerPath     string   // Deprecated, use OverlayLowerPaths
	OverlayLowerPaths    []string // Preferred over OverlayLowerPath
	OverlayTargetPath    string
	OverlaySkipOverlayFS bool
}

// systemState holds the mutable state of the system
type systemState struct {
	processRunning bool
	restoringNow   bool
	juicefsReady   bool
}

// stateOp represents state operations
type stateOp struct {
	typ      stateOpType
	field    string
	value    interface{}
	response chan interface{}
}

type stateOpType int

const (
	stateOpGet stateOpType = iota
	stateOpSet
)

// System encapsulates the JuiceFS and supervised process management
type System struct {
	config             SystemConfig
	logger             *slog.Logger
	leaserInstance     *leaser.Leaser
	juicefs            *juicefs.JuiceFS
	processCmd         *exec.Cmd
	processStartTime   time.Time
	processMu          sync.Mutex
	reaper             *Reaper
	execProcessTracker interface{} // Will be *execProcessTracker, avoiding import issues
	crashReporter      *tap.CrashReporter
	adminChannel       *AdminChannel

	// Channels for monitoring
	processDoneCh chan error

	// State management via channels
	stateCh  chan stateOp
	stopCh   chan struct{}
	stateMgr *systemState

	// Channels for notifying when components become ready
	processReadyCh chan struct{}
	juicefsReadyCh chan struct{}
}

// NewSystem creates a new System instance
func NewSystem(config SystemConfig, logger *slog.Logger, reaper *Reaper, adminChannel *AdminChannel) (*System, error) {
	s := &System{
		config:         config,
		logger:         logger,
		reaper:         reaper,
		adminChannel:   adminChannel,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		juicefsReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr:       &systemState{},
	}

	// Start state manager goroutine
	go s.runStateManager()

	// Initialize crash reporter
	s3Config := (*tap.S3Config)(nil)
	if config.S3AccessKey != "" && config.S3SecretAccessKey != "" && config.S3EndpointURL != "" && config.S3Bucket != "" {
		s3Config = &tap.S3Config{
			AccessKey:   config.S3AccessKey,
			SecretKey:   config.S3SecretAccessKey,
			EndpointURL: config.S3EndpointURL,
			Bucket:      config.S3Bucket,
		}
	}

	localDir := "/tmp/sprite-env"
	if config.JuiceFSBaseDir != "" {
		localDir = config.JuiceFSBaseDir
	}

	crashReporter, err := tap.NewCrashReporter(logger, localDir, s3Config)
	if err != nil {
		logger.Error("Failed to initialize crash reporter", "error", err)
		// Non-fatal, continue without crash reporting
	} else {
		s.crashReporter = crashReporter
	}

	// Log process configuration
	logger.Info("Process configuration",
		"command", config.ProcessCommand,
		"working_dir", config.ProcessWorkingDir,
		"env_count", len(config.ProcessEnvironment),
		"graceful_shutdown_timeout", config.ProcessGracefulShutdownTimeout)

	// Set up JuiceFS if base directory is configured
	if config.JuiceFSBaseDir != "" {
		juicefsConfig := juicefs.Config{
			BaseDir:           config.JuiceFSBaseDir,
			LocalMode:         config.JuiceFSLocalMode,
			S3AccessKey:       config.S3AccessKey,
			S3SecretAccessKey: config.S3SecretAccessKey,
			S3EndpointURL:     config.S3EndpointURL,
			S3Bucket:          config.S3Bucket,
			VolumeName:        "sprite-juicefs",
			// Overlay configuration
			OverlayEnabled:       config.OverlayEnabled,
			OverlayImageSize:     config.OverlayImageSize,
			OverlayLowerPath:     config.OverlayLowerPath,
			OverlayLowerPaths:    config.OverlayLowerPaths,
			OverlayTargetPath:    config.OverlayTargetPath,
			OverlaySkipOverlayFS: config.OverlaySkipOverlayFS,
			Logger:               logger,
		}

		// Create leaser for S3 mode (non-local mode)
		if !config.JuiceFSLocalMode && config.S3AccessKey != "" && config.S3SecretAccessKey != "" &&
			config.S3EndpointURL != "" && config.S3Bucket != "" {
			leaserConfig := leaser.Config{
				S3AccessKey:       config.S3AccessKey,
				S3SecretAccessKey: config.S3SecretAccessKey,
				S3EndpointURL:     config.S3EndpointURL,
				S3Bucket:          config.S3Bucket,
				BaseDir:           config.JuiceFSBaseDir,
				Logger:            logger,
			}

			leaserInstance := leaser.New(leaserConfig)
			s.leaserInstance = leaserInstance
			juicefsConfig.LeaseManager = leaserInstance
		}

		jfs, err := juicefs.New(juicefsConfig)
		if err != nil {
			close(s.stopCh)
			return nil, fmt.Errorf("failed to create JuiceFS instance: %w", err)
		}
		s.juicefs = jfs
	}

	return s, nil
}

// runStateManager manages state access via channels
func (s *System) runStateManager() {
	for {
		select {
		case <-s.stopCh:
			return
		case op := <-s.stateCh:
			switch op.typ {
			case stateOpGet:
				var result interface{}
				switch op.field {
				case "processRunning":
					result = s.stateMgr.processRunning
				case "restoringNow":
					result = s.stateMgr.restoringNow
				case "juicefsReady":
					result = s.stateMgr.juicefsReady

				}
				op.response <- result
			case stateOpSet:
				switch op.field {
				case "processRunning":
					s.stateMgr.processRunning = op.value.(bool)
				case "restoringNow":
					s.stateMgr.restoringNow = op.value.(bool)
				case "juicefsReady":
					s.stateMgr.juicefsReady = op.value.(bool)

				}
				close(op.response)
			}
		}
	}
}

// getState retrieves a state field value
func (s *System) getState(field string) interface{} {
	op := stateOp{
		typ:      stateOpGet,
		field:    field,
		response: make(chan interface{}),
	}
	s.stateCh <- op
	return <-op.response
}

// setState updates a state field value
func (s *System) setState(field string, value interface{}) {
	op := stateOp{
		typ:      stateOpSet,
		field:    field,
		value:    value,
		response: make(chan interface{}),
	}
	s.stateCh <- op
	<-op.response
}

// Boot handles the boot sequence for the system
func (s *System) Boot(ctx context.Context) error {
	bootStart := time.Now()
	s.logger.Info("=== Starting system boot sequence ===", "timestamp", bootStart.Format(time.RFC3339Nano))

	// Start JuiceFS if configured
	if s.juicefs != nil {
		juicefsStart := time.Now()
		s.logger.Info("Boot: Starting JuiceFS...", "step", "juicefs_start", "timestamp", juicefsStart.Format(time.RFC3339Nano))

		if err := s.juicefs.Start(ctx); err != nil {
			s.logger.Error("Boot: JuiceFS start failed",
				"error", err,
				"duration_seconds", time.Since(juicefsStart).Seconds(),
				"step", "juicefs_start_failed")

			// Send notification to admin channel
			if s.adminChannel != nil {
				s.adminChannel.SendActivityEvent("juicefs_start_failed", map[string]interface{}{
					"error":            err.Error(),
					"timestamp":        time.Now().Unix(),
					"duration_seconds": time.Since(juicefsStart).Seconds(),
				})
			}

			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		s.logger.Info("Boot: JuiceFS started successfully",
			"duration_seconds", time.Since(juicefsStart).Seconds(),
			"step", "juicefs_ready")

		// Mark JuiceFS as ready
		s.setState("juicefsReady", true)
		close(s.juicefsReadyCh)
		s.juicefsReadyCh = make(chan struct{})
	} else {
		s.logger.Info("Boot: JuiceFS not configured, skipping", "step", "juicefs_skip")
	}

	// Start supervised process if configured
	if len(s.config.ProcessCommand) > 0 {
		processStart := time.Now()
		s.logger.Info("Boot: Starting supervised process...",
			"command", s.config.ProcessCommand,
			"step", "process_start",
			"timestamp", processStart.Format(time.RFC3339Nano))

		if err := s.StartProcess(); err != nil {
			s.logger.Error("Boot: Process start failed",
				"error", err,
				"duration_seconds", time.Since(processStart).Seconds(),
				"step", "process_start_failed")

			// If process fails to start, stop JuiceFS
			if s.juicefs != nil {
				s.logger.Info("Boot: Stopping JuiceFS due to process start failure", "step", "cleanup_juicefs")
				stopCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				defer cancel()
				if stopErr := s.juicefs.Stop(stopCtx); stopErr != nil {
					s.logger.Error("Boot: Failed to stop JuiceFS during cleanup", "error", stopErr)
				}
			}
			return fmt.Errorf("failed to start process: %w", err)
		}
		s.logger.Info("Boot: Supervised process started successfully",
			"duration_seconds", time.Since(processStart).Seconds(),
			"step", "process_ready")
	} else {
		s.logger.Info("Boot: No process command configured, skipping process start", "step", "process_skip")
	}

	totalBootTime := time.Since(bootStart)
	s.logger.Info("=== System boot sequence completed successfully ===",
		"total_duration_seconds", totalBootTime.Seconds(),
		"timestamp", time.Now().Format(time.RFC3339Nano))
	return nil
}

// Shutdown performs graceful shutdown of the system
func (s *System) Shutdown(ctx context.Context) error {
	// Stop supervised process
	if err := s.StopProcess(); err != nil {
		s.logger.Error("Failed to stop process during shutdown", "error", err)
	}

	// Stop JuiceFS
	if s.juicefs != nil {
		s.logger.Info("Stopping JuiceFS...")
		if err := s.juicefs.Stop(ctx); err != nil {
			return fmt.Errorf("failed to stop JuiceFS: %w", err)
		}

		// Mark JuiceFS as not ready
		s.setState("juicefsReady", false)
	}

	// Stop leaser (if it exists and wasn't already stopped by JuiceFS)
	if s.leaserInstance != nil {
		s.logger.Info("Stopping lease manager...")
		s.leaserInstance.Stop()
		s.logger.Info("Lease manager stopped successfully")
	}

	// Stop state manager goroutine
	close(s.stopCh)

	return nil
}

// SyncOverlay flushes overlay writes using JuiceFS overlay manager
// Returns a function that must be called to unfreeze the filesystem.
func (s *System) SyncOverlay(ctx context.Context) (func() error, error) {
	if s.juicefs == nil {
		return func() error { return nil }, nil
	}
	return s.juicefs.SyncOverlay(ctx)
}

// StartProcess starts the configured process
func (s *System) StartProcess() error {
	s.processMu.Lock()
	defer s.processMu.Unlock()

	if s.processCmd != nil && s.processCmd.Process != nil {
		return fmt.Errorf("process already started")
	}

	if len(s.config.ProcessCommand) == 0 {
		return fmt.Errorf("no process command configured")
	}

	// Determine working directory
	workingDir := s.config.ProcessWorkingDir
	if workingDir == "" {
		workingDir = "/dev/fly_vol"
		s.logger.Info("No working directory specified, using default", "workingDir", workingDir)
	}

	// Prepare the command
	cmd := exec.Command(s.config.ProcessCommand[0], s.config.ProcessCommand[1:]...)
	cmd.Dir = workingDir
	cmd.Env = append(os.Environ(), s.config.ProcessEnvironment...)

	// Set process group for signal forwarding
	cmd.SysProcAttr = &syscall.SysProcAttr{
		Setpgid: true,
	}

	// Set up output capturing for crash reporting
	var stdoutBuffer, stderrBuffer *tap.CircularBuffer
	if s.crashReporter != nil {
		// Create circular buffers to capture recent output (32KB each)
		stdoutBuffer = tap.NewCircularBuffer(32 * 1024)
		stderrBuffer = tap.NewCircularBuffer(32 * 1024)
	}

	// Set up stdout - write to parent stdout and optional buffer
	stdoutWriters := []io.Writer{os.Stdout}
	if stdoutBuffer != nil {
		stdoutWriters = append(stdoutWriters, stdoutBuffer)
	}
	cmd.Stdout = io.MultiWriter(stdoutWriters...)

	// Set up stderr - write to parent stderr and optional buffer
	stderrWriters := []io.Writer{os.Stderr}
	if stderrBuffer != nil {
		stderrWriters = append(stderrWriters, stderrBuffer)
	}
	cmd.Stderr = io.MultiWriter(stderrWriters...)

	// Connect stdin
	cmd.Stdin = os.Stdin

	// Start the process
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("failed to start process: %w", err)
	}

	s.processCmd = cmd
	s.processStartTime = time.Now()
	s.setState("processRunning", true)

	// Close the ready channel to unblock waiting requests
	close(s.processReadyCh)
	s.processReadyCh = make(chan struct{})

	s.logger.Info("Process started successfully",
		"pid", cmd.Process.Pid,
		"command", s.config.ProcessCommand)

	// Monitor process in background
	go func() {
		err := cmd.Wait()
		processRuntime := time.Since(s.processStartTime)
		s.logger.Info("Process exited", "error", err, "runtime", processRuntime)

		// Generate crash report if needed
		if err != nil && s.crashReporter != nil {
			report := &tap.CrashReport{
				Command:  s.config.ProcessCommand[0],
				Args:     s.config.ProcessCommand[1:],
				Runtime:  processRuntime,
				ExitCode: -1,
			}

			// Extract exit code and signal if available
			if exitErr, ok := err.(*exec.ExitError); ok {
				if status, ok := exitErr.Sys().(syscall.WaitStatus); ok {
					report.ExitCode = status.ExitStatus()
					if status.Signaled() {
						report.Signal = status.Signal().String()
					}
				}
			}

			report.Error = err.Error()
			if stdoutBuffer != nil {
				report.RecentStdout = stdoutBuffer.GetContents()
			}
			if stderrBuffer != nil {
				report.RecentStderr = stderrBuffer.GetContents()
			}

			// Report the crash
			ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer cancel()
			if reportErr := s.crashReporter.ReportSupervisedProcessCrash(ctx, report); reportErr != nil {
				s.logger.Error("Failed to report process crash", "error", reportErr)
			}

			// Send notification to admin channel
			if s.adminChannel != nil {
				s.adminChannel.SendActivityEvent("supervised_process_crashed", report.ToMap())
			}
		}

		s.processDoneCh <- err
		s.setState("processRunning", false)
	}()

	return nil
}

// StopProcess stops the supervised process gracefully
func (s *System) StopProcess() error {
	s.processMu.Lock()
	defer s.processMu.Unlock()

	if s.processCmd == nil || s.processCmd.Process == nil {
		return nil
	}

	s.logger.Info("Stopping process", "pid", s.processCmd.Process.Pid)

	// Send SIGTERM to process group
	if err := syscall.Kill(-s.processCmd.Process.Pid, syscall.SIGTERM); err != nil {
		s.logger.Warn("Failed to send SIGTERM to process group", "error", err)
		// Try just the process
		if err := s.processCmd.Process.Signal(syscall.SIGTERM); err != nil {
			s.logger.Warn("Failed to send SIGTERM to process", "error", err)
		}
	}

	// Wait for graceful shutdown
	gracePeriod := s.config.ProcessGracefulShutdownTimeout
	if gracePeriod == 0 {
		gracePeriod = 30 * time.Second
	}

	done := make(chan struct{})
	go func() {
		s.processCmd.Wait()
		close(done)
	}()

	select {
	case <-done:
		s.logger.Info("Process stopped gracefully")
		s.processCmd = nil
		return nil
	case <-time.After(gracePeriod):
		s.logger.Warn("Process did not stop within grace period, sending SIGKILL")

		// Send SIGKILL to process group
		if err := syscall.Kill(-s.processCmd.Process.Pid, syscall.SIGKILL); err != nil {
			s.logger.Error("Failed to send SIGKILL to process group", "error", err)
			// Try just the process
			if err := s.processCmd.Process.Kill(); err != nil {
				s.logger.Error("Failed to kill process", "error", err)
			}
		}

		// Wait a bit for the process to die
		select {
		case <-done:
			s.logger.Info("Process killed successfully")
			s.processCmd = nil
			return nil
		case <-time.After(5 * time.Second):
			return fmt.Errorf("process did not exit after SIGKILL")
		}
	}
}

// ForwardSignal forwards a signal to the supervised process
func (s *System) ForwardSignal(sig os.Signal) error {
	s.processMu.Lock()
	defer s.processMu.Unlock()

	if s.processCmd == nil || s.processCmd.Process == nil {
		return fmt.Errorf("no process running")
	}

	s.logger.Debug("Forwarding signal to process", "signal", sig, "pid", s.processCmd.Process.Pid)

	// Forward signal to the process group
	if err := syscall.Kill(-s.processCmd.Process.Pid, sig.(syscall.Signal)); err != nil {
		s.logger.Warn("Failed to forward signal to process group", "signal", sig, "error", err)
		// Try sending to just the process
		if err := s.processCmd.Process.Signal(sig); err != nil {
			return fmt.Errorf("failed to forward signal: %w", err)
		}
	}

	return nil
}

// Wait waits for the process to exit
func (s *System) Wait() error {
	if s.processDoneCh == nil {
		return fmt.Errorf("no process to wait for")
	}
	return <-s.processDoneCh
}

// MonitorExecProcess monitors an exec session
func (s *System) MonitorExecProcess(execID string, execFunc func() error) error {
	// Just run the function - exec process tracking not implemented
	return execFunc()
}

// StartExecProcessTracking starts tracking an exec process
func (s *System) StartExecProcessTracking(execID string, pid int) error {
	// Exec process tracking not implemented
	return nil
}

// StopExecProcessTracking stops tracking an exec process
func (s *System) StopExecProcessTracking(execID string) {
	// Exec process tracking not implemented
}

// GetCrashReporter returns the crash reporter instance
func (s *System) GetCrashReporter() *tap.CrashReporter {
	return s.crashReporter
}
