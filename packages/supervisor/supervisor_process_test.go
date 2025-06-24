package supervisor

import (
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

// TestProcessStartReturnsValidPID verifies that Start returns a valid PID
func TestProcessStartReturnsValidPID(t *testing.T) {
	s, err := New(Config{
		Command: "sleep",
		Args:    []string{"1"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Verify PID is valid
	if pid <= 0 {
		t.Errorf("Invalid PID returned: %d", pid)
	}

	// Verify process exists
	if err := syscall.Kill(pid, 0); err != nil {
		t.Errorf("Process with PID %d does not exist: %v", pid, err)
	}

	// Clean up
	s.Stop()
}

// TestProcessExitZero tests a process that exits cleanly with code 0
func TestProcessExitZero(t *testing.T) {
	scriptPath := filepath.Join("test-scripts", "exit_zero.sh")
	if _, err := os.Stat(scriptPath); os.IsNotExist(err) {
		t.Skip("Test script not found: " + scriptPath)
	}

	s, err := New(Config{
		Command: "bash",
		Args:    []string{scriptPath},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Process should exist initially
	if err := syscall.Kill(pid, 0); err != nil {
		t.Errorf("Process %d doesn't exist immediately after start: %v", pid, err)
	}

	// Wait for process to exit
	err = s.Wait()
	if err != nil {
		t.Errorf("Expected clean exit, got error: %v", err)
	}

	// Process should no longer exist
	if err := syscall.Kill(pid, 0); err == nil {
		t.Errorf("Process %d still exists after Wait()", pid)
	}
}

// TestProcessExitNonZero tests a process that exits with non-zero code
func TestProcessExitNonZero(t *testing.T) {
	scriptPath := filepath.Join("test-scripts", "exit_nonzero.sh")
	if _, err := os.Stat(scriptPath); os.IsNotExist(err) {
		t.Skip("Test script not found: " + scriptPath)
	}

	s, err := New(Config{
		Command: "bash",
		Args:    []string{scriptPath},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for process to exit
	err = s.Wait()
	if err == nil {
		t.Error("Expected error for non-zero exit, got nil")
	}

	// Verify it's an exit error with code 42
	var exitErr *exec.ExitError
	if !errors.As(err, &exitErr) {
		t.Errorf("Expected ExitError, got %T: %v", err, err)
	} else if exitErr.ExitCode() != 42 {
		t.Errorf("Expected exit code 42, got %d", exitErr.ExitCode())
	}

	// Process should no longer exist
	if err := syscall.Kill(pid, 0); err == nil {
		t.Errorf("Process %d still exists after exit", pid)
	}
}

// TestProcessCrashAfter5s tests a process that crashes after 5 seconds
func TestProcessCrashAfter5s(t *testing.T) {
	scriptPath := filepath.Join("test-scripts", "crash_after_5s.sh")
	if _, err := os.Stat(scriptPath); os.IsNotExist(err) {
		t.Skip("Test script not found: " + scriptPath)
	}

	s, err := New(Config{
		Command: "bash",
		Args:    []string{scriptPath},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	// Get stdout to see the countdown
	stdout, _ := s.StdoutPipe()
	defer stdout.Close()

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Process should be running initially
	if err := syscall.Kill(pid, 0); err != nil {
		t.Errorf("Process %d not running after start: %v", pid, err)
	}

	// Read output in background using channel-based communication
	outputCh := make(chan string, 1)

	go func() {
		var output strings.Builder
		buf := make([]byte, 1024)
		for {
			n, err := stdout.Read(buf)
			if err == io.EOF {
				break
			}
			if n > 0 {
				output.Write(buf[:n])
			}
		}
		// Send the complete output through channel when done
		outputCh <- output.String()
	}()

	// Wait for crash
	start := time.Now()
	err = s.Wait()
	duration := time.Since(start)

	// Should take approximately 5 seconds
	if duration < 4*time.Second || duration > 6*time.Second {
		t.Errorf("Process crashed after %v, expected ~5s", duration)
	}

	// Should have exit error
	if err == nil {
		t.Error("Expected error from crash, got nil")
	}

	// Get the output from the channel (safe after process has exited)
	outputStr := <-outputCh

	if !strings.Contains(outputStr, "Will crash in 5 seconds") {
		t.Errorf("Expected countdown message in output, got: %s", outputStr)
	}
}

// TestProcessIgnoreSignals tests a process that ignores SIGTERM
func TestProcessIgnoreSignals(t *testing.T) {
	scriptPath := filepath.Join("test-scripts", "ignore_signals.sh")
	if _, err := os.Stat(scriptPath); os.IsNotExist(err) {
		t.Skip("Test script not found: " + scriptPath)
	}

	s, err := New(Config{
		Command:     "bash",
		Args:        []string{scriptPath},
		GracePeriod: 1 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Give process time to set up signal handlers
	time.Sleep(100 * time.Millisecond)

	// Try to stop - should require force kill
	start := time.Now()
	err = s.Stop()
	duration := time.Since(start)

	if err != nil {
		t.Errorf("Stop returned error: %v", err)
	}

	// Should have taken at least grace period
	if duration < 1*time.Second {
		t.Errorf("Stop took %v, expected at least 1s grace period", duration)
	}

	// Process should be gone
	if err := syscall.Kill(pid, 0); err == nil {
		t.Errorf("Process %d still exists after force kill", pid)
	}

	// Wait should show it was killed
	err = s.Wait()
	if err == nil {
		t.Error("Expected error from force kill")
	}
	if !strings.Contains(err.Error(), "killed after grace period") {
		t.Errorf("Expected 'killed after grace period' error, got: %v", err)
	}
}

// TestProcessRunForever tests stopping a long-running process
func TestProcessRunForever(t *testing.T) {
	scriptPath := filepath.Join("test-scripts", "run_forever.sh")
	if _, err := os.Stat(scriptPath); os.IsNotExist(err) {
		t.Skip("Test script not found: " + scriptPath)
	}

	s, err := New(Config{
		Command: "bash",
		Args:    []string{scriptPath},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	stdout, _ := s.StdoutPipe()
	defer stdout.Close()

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read some output
	buf := make([]byte, 1024)
	n, _ := stdout.Read(buf)
	output := string(buf[:n])
	if !strings.Contains(output, "Entering infinite loop") {
		t.Errorf("Expected 'Entering infinite loop' in output, got: %s", output)
	}

	// Stop the process
	err = s.Stop()
	if err != nil {
		t.Errorf("Failed to stop process: %v", err)
	}

	// Process should be gone
	if err := syscall.Kill(pid, 0); err == nil {
		t.Errorf("Process %d still exists after stop", pid)
	}
}

// TestProcessPrintArgs tests argument passing
func TestProcessPrintArgs(t *testing.T) {
	scriptPath := filepath.Join("test-scripts", "print_args.sh")
	if _, err := os.Stat(scriptPath); os.IsNotExist(err) {
		t.Skip("Test script not found: " + scriptPath)
	}

	s, err := New(Config{
		Command: "bash",
		Args:    []string{scriptPath, "arg1", "arg 2", "arg-3"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	stdout, _ := s.StdoutPipe()
	defer stdout.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read all output
	output, _ := io.ReadAll(stdout)
	outputStr := string(output)

	// Check arguments were passed correctly
	if !strings.Contains(outputStr, "arg1") {
		t.Errorf("Missing arg1 in output: %s", outputStr)
	}
	if !strings.Contains(outputStr, "arg 2") {
		t.Errorf("Missing 'arg 2' in output: %s", outputStr)
	}
	if !strings.Contains(outputStr, "arg-3") {
		t.Errorf("Missing arg-3 in output: %s", outputStr)
	}

	s.Wait()
}

// TestWaitCalledOncePerProcess ensures Wait() can only consume the exit status once
func TestWaitCalledOncePerProcess(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "exit 0"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// First Wait should succeed
	err1 := s.Wait()
	if err1 != nil {
		t.Errorf("First Wait() returned error: %v", err1)
	}

	// Subsequent Waits should return the same result immediately
	err2 := s.Wait()
	if err2 != err1 {
		t.Errorf("Second Wait() returned different error: %v vs %v", err2, err1)
	}

	// Try with a process that exits with error
	s2, _ := New(Config{
		Command: "bash",
		Args:    []string{"-c", "exit 42"},
	})
	s2.Start()

	// Multiple goroutines calling Wait should all get the same result
	var wg sync.WaitGroup
	errs := make([]error, 5)
	for i := 0; i < 5; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			errs[idx] = s2.Wait()
		}(i)
	}
	wg.Wait()

	// All should have the same error
	for i := 1; i < 5; i++ {
		if errs[i] == nil && errs[0] != nil {
			t.Errorf("Wait() %d returned nil, but Wait() 0 returned %v", i, errs[0])
		} else if errs[i] != nil && errs[0] == nil {
			t.Errorf("Wait() %d returned %v, but Wait() 0 returned nil", i, errs[i])
		} else if errs[i] != nil && errs[0] != nil {
			// Both are errors, check they're reporting the same exit code
			var exitErr1, exitErr2 *exec.ExitError
			if errors.As(errs[0], &exitErr1) && errors.As(errs[i], &exitErr2) {
				if exitErr1.ExitCode() != exitErr2.ExitCode() {
					t.Errorf("Wait() returned different exit codes: %d vs %d",
						exitErr1.ExitCode(), exitErr2.ExitCode())
				}
			}
		}
	}
}

// TestProcessNotFound tests starting a non-existent command
func TestProcessNotFound(t *testing.T) {
	s, err := New(Config{
		Command: "/non/existent/command",
		Args:    []string{"arg1"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	pid, err := s.Start()
	if err == nil {
		t.Error("Expected error starting non-existent command")
	}
	if pid != -1 {
		t.Errorf("Expected PID -1 for failed start, got %d", pid)
	}

	// Subsequent operations should fail appropriately
	if err := s.Stop(); err == nil {
		t.Error("Expected error stopping non-started process")
	}
	if err := s.Wait(); err == nil {
		t.Error("Expected error waiting for non-started process")
	}
}

// TestProcessZombiePrevention tests that we don't create zombie processes
func TestProcessZombiePrevention(t *testing.T) {
	// Start multiple short-lived processes
	for i := 0; i < 10; i++ {
		s, err := New(Config{
			Command: "bash",
			Args:    []string{"-c", "sleep 0.1"},
		})
		if err != nil {
			t.Fatalf("Failed to create supervisor %d: %v", i, err)
		}

		pid, err := s.Start()
		if err != nil {
			t.Fatalf("Failed to start process %d: %v", i, err)
		}

		// Don't wait or stop - let it exit naturally
		time.Sleep(200 * time.Millisecond)

		// Check if process became a zombie
		cmd := exec.Command("ps", "-p", fmt.Sprintf("%d", pid), "-o", "stat=")
		output, _ := cmd.Output()
		stat := strings.TrimSpace(string(output))

		if strings.Contains(stat, "Z") {
			t.Errorf("Process %d became a zombie (stat: %s)", pid, stat)
		}

		// Clean up
		s.Wait()
	}
}

// TestProcessStderrCapture tests capturing stderr output
func TestProcessStderrCapture(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "echo 'stdout message'; echo 'stderr message' >&2"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	stdoutPipe, _ := s.StdoutPipe()
	stderrPipe, _ := s.StderrPipe()
	defer stdoutPipe.Close()
	defer stderrPipe.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read both streams
	stdout, _ := io.ReadAll(stdoutPipe)
	stderr, _ := io.ReadAll(stderrPipe)

	// Verify correct routing
	if !strings.Contains(string(stdout), "stdout message") {
		t.Errorf("stdout missing expected message: %s", stdout)
	}
	if strings.Contains(string(stdout), "stderr message") {
		t.Errorf("stdout contains stderr message: %s", stdout)
	}

	if !strings.Contains(string(stderr), "stderr message") {
		t.Errorf("stderr missing expected message: %s", stderr)
	}
	if strings.Contains(string(stderr), "stdout message") {
		t.Errorf("stderr contains stdout message: %s", stderr)
	}

	s.Wait()
}

// TestProcessEnvironmentIsolation tests that supervisor doesn't leak implementation details
func TestProcessEnvironmentIsolation(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "env | grep -E '^(GO|SUPERVISOR)'"},
		Env:     []string{"PATH=/usr/bin:/bin", "TEST_VAR=test"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	stdout, _ := s.StdoutPipe()
	defer stdout.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	output, _ := io.ReadAll(stdout)
	outputStr := string(output)

	// Should not see Go runtime or supervisor-specific variables
	if strings.Contains(outputStr, "GOPATH") || strings.Contains(outputStr, "GOROOT") {
		t.Errorf("Process environment contains Go variables: %s", outputStr)
	}

	s.Wait()
}
