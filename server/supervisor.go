package main

import (
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"syscall"
)

// Supervisor manages long-running processes
type Supervisor struct {
	cmd   *exec.Cmd
	debug bool
}

// NewSupervisor creates a new supervisor
func NewSupervisor(debug bool) *Supervisor {
	return &Supervisor{
		debug: debug,
	}
}

// Start starts a long-running process
func (s *Supervisor) Start(command string) error {
	if s.debug {
		log.Printf("DEBUG: Starting process: %s", command)
	}

	// Execute the script directly instead of using sh -c
	s.cmd = exec.Command(command)

	// Set up pipes for output
	stdout, err := s.cmd.StdoutPipe()
	if err != nil {
		return fmt.Errorf("failed to create stdout pipe: %v", err)
	}
	stderr, err := s.cmd.StderrPipe()
	if err != nil {
		return fmt.Errorf("failed to create stderr pipe: %v", err)
	}

	// Start the process
	if err := s.cmd.Start(); err != nil {
		return fmt.Errorf("failed to start process: %v", err)
	}

	if s.debug {
		log.Printf("DEBUG: Process started with PID: %d", s.cmd.Process.Pid)
	}

	// Forward output
	go func() {
		if _, err := io.Copy(os.Stdout, stdout); err != nil && s.debug {
			log.Printf("DEBUG: Error copying stdout: %v", err)
		}
	}()
	go func() {
		if _, err := io.Copy(os.Stderr, stderr); err != nil && s.debug {
			log.Printf("DEBUG: Error copying stderr: %v", err)
		}
	}()

	// Start a goroutine to wait for the process
	go func() {
		if err := s.cmd.Wait(); err != nil {
			if s.debug {
				log.Printf("DEBUG: Process exited with error: %v", err)
			}
		} else if s.debug {
			log.Printf("DEBUG: Process exited successfully")
		}
	}()

	return nil
}

// Stop stops the process
func (s *Supervisor) Stop() error {
	if s.cmd == nil || s.cmd.Process == nil {
		return nil
	}

	if s.debug {
		log.Printf("DEBUG: Stopping process with PID: %d", s.cmd.Process.Pid)
	}

	// Send SIGTERM (don't wait here since we already have a goroutine waiting)
	return s.cmd.Process.Signal(syscall.SIGTERM)
}
