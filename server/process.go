package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"

	"github.com/sprite-env/packages/supervisor"
	"github.com/superfly/sprite-env/packages/container"
)

// StartProcess starts the supervised process
func (s *System) StartProcess() error {
	s.mu.Lock()
	defer s.mu.Unlock()

	s.logger.Info("StartProcess: Entering method")

	if len(s.config.ProcessCommand) == 0 {
		s.logger.Error("StartProcess: No process command configured")
		return fmt.Errorf("no process command configured")
	}

	s.logger.Info("StartProcess: Setting up working directory", "command", s.config.ProcessCommand)

	// Set up process working directory
	workingDir := s.config.ProcessWorkingDir
	if s.juicefs != nil && workingDir == "" {
		// Default to JuiceFS active directory if available
		workingDir = filepath.Join(s.config.JuiceFSBaseDir, "data", "active", "fs")
		s.logger.Info("StartProcess: Using JuiceFS default working directory", "workingDir", workingDir)
	}

	s.logger.Info("StartProcess: Final working directory", "workingDir", workingDir)

	// Check if working directory exists
	if workingDir != "" {
		if stat, err := os.Stat(workingDir); err != nil {
			s.logger.Error("StartProcess: Working directory does not exist", "workingDir", workingDir, "error", err)
			return fmt.Errorf("working directory does not exist: %s: %w", workingDir, err)
		} else {
			s.logger.Info("StartProcess: Working directory exists", "workingDir", workingDir, "isDir", stat.IsDir())
		}
	}

	supervisorConfig := supervisor.Config{
		Command:     s.config.ProcessCommand[0],
		Args:        s.config.ProcessCommand[1:],
		GracePeriod: s.config.ProcessGracefulShutdownTimeout,
		Env:         append(os.Environ(), s.config.ProcessEnvironment...),
		Dir:         workingDir,
		Logger:      s.logger,
	}

	s.logger.Info("StartProcess: Creating supervisor",
		"command", supervisorConfig.Command,
		"args", supervisorConfig.Args,
		"gracePeriod", supervisorConfig.GracePeriod,
		"dir", supervisorConfig.Dir,
		"envCount", len(supervisorConfig.Env))

	// Validate that the command exists and is executable
	if _, err := exec.LookPath(supervisorConfig.Command); err != nil {
		s.logger.Error("StartProcess: Command not found in PATH", "command", supervisorConfig.Command, "error", err)
		return fmt.Errorf("command not found: %s: %w", supervisorConfig.Command, err)
	}

	// Check if it's an absolute path that exists
	if filepath.IsAbs(supervisorConfig.Command) {
		if stat, err := os.Stat(supervisorConfig.Command); err != nil {
			s.logger.Error("StartProcess: Command file does not exist", "command", supervisorConfig.Command, "error", err)
			return fmt.Errorf("command file does not exist: %s: %w", supervisorConfig.Command, err)
		} else if stat.Mode()&0111 == 0 {
			s.logger.Error("StartProcess: Command file is not executable", "command", supervisorConfig.Command)
			return fmt.Errorf("command file is not executable: %s", supervisorConfig.Command)
		}
	}

	s.logger.Info("StartProcess: Command validation successful")

	// Use container-wrapped process if containers are enabled, otherwise use basic supervisor
	if s.config.ContainerEnabled {
		s.logger.Info("StartProcess: Creating container-wrapped process")

		processConfig := container.ProcessConfig{
			Config: supervisor.Config{
				Command:     s.config.ProcessCommand[0],
				Args:        s.config.ProcessCommand[1:],
				GracePeriod: s.config.ProcessGracefulShutdownTimeout,
				Env:         append(os.Environ(), s.config.ProcessEnvironment...),
				Dir:         workingDir,
				Logger:      s.logger,
			},
			TTYTimeout: s.config.ContainerTTYTimeout,
			TTYOutput:  os.Stdout, // Forward TTY output to logs
		}

		containerProcess, err := container.NewProcess(processConfig)
		if err != nil {
			s.logger.Error("StartProcess: Failed to create container process", "error", err)
			return fmt.Errorf("failed to create container process: %w", err)
		}

		s.logger.Info("StartProcess: Container process created successfully, starting process")

		pid, err := containerProcess.Start()
		if err != nil {
			s.logger.Error("StartProcess: Failed to start container process", "error", err)
			return fmt.Errorf("failed to start container process: %w", err)
		}

		// Store the container process (which embeds the supervisor)
		s.supervisor = containerProcess.Supervisor
		s.containerProcess = containerProcess
		s.processRunning = true

		s.logger.Info("StartProcess: Container process started successfully", "pid", pid, "command", s.config.ProcessCommand)

	} else {
		s.logger.Info("StartProcess: Creating basic supervisor (containers disabled)")

		sup, err := supervisor.New(supervisorConfig)
		if err != nil {
			s.logger.Error("StartProcess: Failed to create supervisor", "error", err)
			return fmt.Errorf("failed to create supervisor: %w", err)
		}

		s.logger.Info("StartProcess: Supervisor created successfully, starting process")

		pid, err := sup.Start()
		if err != nil {
			s.logger.Error("StartProcess: Failed to start process", "error", err)
			return fmt.Errorf("failed to start process: %w", err)
		}

		s.supervisor = sup
		s.processRunning = true

		s.logger.Info("StartProcess: Process started successfully", "pid", pid, "command", s.config.ProcessCommand)
	}

	// Close the old channel and create a new one for future waits
	close(s.processReadyCh)
	s.processReadyCh = make(chan struct{})

	// Monitor process in background
	go func() {
		s.logger.Info("StartProcess: Starting background process monitor")
		err := s.supervisor.Wait()
		s.logger.Info("StartProcess: Process monitor detected process exit", "error", err)
		s.processDoneCh <- err

		s.mu.Lock()
		s.processRunning = false
		s.mu.Unlock()
		s.logger.Info("StartProcess: Background monitor completed")
	}()

	s.logger.Info("StartProcess: Method completed successfully")
	return nil
}

// StopProcess stops the supervised process
func (s *System) StopProcess() error {
	s.mu.Lock()
	defer s.mu.Unlock()

	if !s.processRunning || s.supervisor == nil {
		return nil
	}

	s.logger.Info("Stopping supervised process...")

	// Stop container process if available, otherwise stop basic supervisor
	if s.containerProcess != nil {
		if err := s.containerProcess.Stop(); err != nil {
			return fmt.Errorf("failed to stop container process: %w", err)
		}
		s.containerProcess = nil
	} else {
		if err := s.supervisor.Stop(); err != nil {
			return fmt.Errorf("failed to stop process: %w", err)
		}
	}

	s.processRunning = false
	s.logger.Info("Process stopped successfully")
	return nil
}

// Wait waits for the supervised process to complete
func (s *System) Wait() error {
	// If no process is running, return immediately
	s.mu.RLock()
	if !s.processRunning {
		s.mu.RUnlock()
		return nil
	}
	s.mu.RUnlock()

	// Wait for process to complete
	err := <-s.processDoneCh
	return err
}

// ForwardSignal forwards a signal to the supervised process
func (s *System) ForwardSignal(sig os.Signal) error {
	s.mu.RLock()
	defer s.mu.RUnlock()

	if s.processRunning && s.supervisor != nil {
		return s.supervisor.Signal(sig)
	}
	return nil
}
