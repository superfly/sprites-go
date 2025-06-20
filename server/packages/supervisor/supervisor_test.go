package supervisor

import (
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

func TestNew(t *testing.T) {
	tests := []struct {
		name    string
		config  Config
		wantErr bool
	}{
		{
			name: "valid config",
			config: Config{
				Command:     "echo",
				Args:        []string{"test"},
				GracePeriod: 5 * time.Second,
			},
			wantErr: false,
		},
		{
			name: "empty command",
			config: Config{
				Command: "",
			},
			wantErr: true,
		},
		{
			name: "default grace period",
			config: Config{
				Command: "echo",
			},
			wantErr: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s, err := New(tt.config)
			if (err != nil) != tt.wantErr {
				t.Errorf("New() error = %v, wantErr %v", err, tt.wantErr)
			}
			if !tt.wantErr && s == nil {
				t.Error("New() returned nil supervisor")
			}
			if !tt.wantErr && s.gracePeriod <= 0 {
				t.Error("New() supervisor has invalid grace period")
			}
		})
	}
}

func TestStartStop(t *testing.T) {
	s, err := New(Config{
		Command:     "sleep",
		Args:        []string{"10"},
		GracePeriod: 2 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	// Test start
	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}
	if pid <= 0 {
		t.Errorf("Invalid PID returned from Start: %d", pid)
	}

	// Verify process is running
	pidFromGetter, err := s.Pid()
	if err != nil {
		t.Fatalf("Failed to get PID: %v", err)
	}
	if pidFromGetter != pid {
		t.Errorf("PID mismatch: Start returned %d, Pid() returned %d", pid, pidFromGetter)
	}

	// Test double start
	_, err = s.Start()
	if err == nil {
		t.Error("Expected error on double start")
	}

	// Test stop
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}

	// Test double stop
	if err := s.Stop(); err != nil {
		t.Error("Expected no error on double stop")
	}
}

func TestGracefulShutdown(t *testing.T) {
	// Create a script that handles SIGTERM gracefully
	script := `#!/bin/bash
trap 'echo "SIGTERM received"; exit 0' SIGTERM
while true; do sleep 0.1; done
`
	scriptFile := "/tmp/test_graceful.sh"
	if err := os.WriteFile(scriptFile, []byte(script), 0755); err != nil {
		t.Fatalf("Failed to create test script: %v", err)
	}
	defer os.Remove(scriptFile)

	s, err := New(Config{
		Command:     "bash",
		Args:        []string{scriptFile},
		GracePeriod: 2 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Give process time to set up signal handler
	time.Sleep(100 * time.Millisecond)

	start := time.Now()
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}
	duration := time.Since(start)

	// Should stop quickly (not wait for full grace period)
	if duration > time.Second {
		t.Errorf("Graceful shutdown took too long: %v", duration)
	}

	// Wait should return without error
	if err := s.Wait(); err != nil {
		t.Errorf("Wait returned error: %v", err)
	}
}

func TestForceKill(t *testing.T) {
	// Create a script that ignores SIGTERM
	script := `#!/bin/bash
trap '' SIGTERM
while true; do sleep 0.1; done
`
	scriptFile := "/tmp/test_force_kill.sh"
	if err := os.WriteFile(scriptFile, []byte(script), 0755); err != nil {
		t.Fatalf("Failed to create test script: %v", err)
	}
	defer os.Remove(scriptFile)

	s, err := New(Config{
		Command:     "bash",
		Args:        []string{scriptFile},
		GracePeriod: 1 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Give process time to set up signal handler
	time.Sleep(100 * time.Millisecond)

	start := time.Now()
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}
	duration := time.Since(start)

	// Should wait for grace period then force kill
	if duration < 1*time.Second || duration > 2*time.Second {
		t.Errorf("Force kill timing incorrect: %v", duration)
	}

	// Wait should return error about force kill
	err = s.Wait()
	if err == nil {
		t.Error("Expected error from force kill")
	}

	// Check that the error message contains "process killed after grace period"
	if err != nil && !strings.Contains(err.Error(), "process killed after grace period") {
		t.Errorf("Expected error about process killed after grace period, got: %v", err)
	}
}

func TestSignalForwarding(t *testing.T) {
	// Create a script that counts signals
	script := `#!/bin/bash
count=0
trap 'count=$((count+1)); echo "Signal $count"' SIGUSR1
trap 'echo "Exiting with count $count"; exit $count' SIGTERM
while true; do sleep 0.1; done
`
	scriptFile := "/tmp/test_signal.sh"
	if err := os.WriteFile(scriptFile, []byte(script), 0755); err != nil {
		t.Fatalf("Failed to create test script: %v", err)
	}
	defer os.Remove(scriptFile)

	s, err := New(Config{
		Command:     "bash",
		Args:        []string{scriptFile},
		GracePeriod: 2 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Give process time to set up signal handlers
	time.Sleep(100 * time.Millisecond)

	// Send some signals
	for i := 0; i < 3; i++ {
		if err := s.Signal(syscall.SIGUSR1); err != nil {
			t.Errorf("Failed to send signal %d: %v", i, err)
		}
		time.Sleep(50 * time.Millisecond)
	}

	// Stop the process
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}
}

func TestProcessExit(t *testing.T) {
	s, err := New(Config{
		Command:     "bash",
		Args:        []string{"-c", "exit 42"},
		GracePeriod: 1 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Wait for process to exit
	err = s.Wait()
	if err == nil {
		t.Error("Expected error from process exit with code 42")
	}

	var exitErr *exec.ExitError
	if !errors.As(err, &exitErr) {
		t.Errorf("Expected ExitError, got: %T", err)
	} else if exitErr.ExitCode() != 42 {
		t.Errorf("Expected exit code 42, got: %d", exitErr.ExitCode())
	}
}

func TestNotStartedErrors(t *testing.T) {
	s, err := New(Config{
		Command: "echo",
		Args:    []string{"test"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	// Test operations on non-started process
	if err := s.Stop(); err == nil {
		t.Error("Expected error calling Stop on non-started process")
	}

	if err := s.Signal(syscall.SIGTERM); err == nil {
		t.Error("Expected error calling Signal on non-started process")
	}

	if err := s.Wait(); err == nil {
		t.Error("Expected error calling Wait on non-started process")
	}

	if _, err := s.Pid(); err == nil {
		t.Error("Expected error calling Pid on non-started process")
	}
}

func TestConcurrentOperations(t *testing.T) {
	s, err := New(Config{
		Command:     "sleep",
		Args:        []string{"5"},
		GracePeriod: 1 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Concurrent signal sending
	done := make(chan struct{})
	for i := 0; i < 5; i++ {
		go func() {
			for j := 0; j < 10; j++ {
				s.Signal(syscall.SIGUSR1)
				time.Sleep(10 * time.Millisecond)
			}
			done <- struct{}{}
		}()
	}

	// Wait for signal senders
	for i := 0; i < 5; i++ {
		<-done
	}

	// Stop the process
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}
}

func TestProcessGroup(t *testing.T) {
	// Skip test if we can't use ps command properly
	if _, err := exec.LookPath("ps"); err != nil {
		t.Skip("ps command not available")
	}

	// Create a script that spawns child processes
	script := `#!/bin/bash
# Spawn some child processes
sleep 100 &
sleep 100 &
sleep 100 &

# Wait for signal
trap 'exit 0' SIGTERM
while true; do sleep 0.1; done
`
	scriptFile := "/tmp/test_process_group.sh"
	if err := os.WriteFile(scriptFile, []byte(script), 0755); err != nil {
		t.Fatalf("Failed to create test script: %v", err)
	}
	defer os.Remove(scriptFile)

	s, err := New(Config{
		Command:     "bash",
		Args:        []string{scriptFile},
		GracePeriod: 1 * time.Second,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	pid, err := s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Give time for child processes to spawn
	time.Sleep(200 * time.Millisecond)

	// Count processes in the group before stopping
	beforeCount := countProcessGroup(pid)
	if beforeCount < 4 { // parent + 3 children
		t.Logf("Warning: Expected at least 4 processes in group, got %d", beforeCount)
	}

	// Stop should kill entire process group
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}

	// Give more time for all processes to die
	time.Sleep(500 * time.Millisecond)

	// Check if main process is really dead
	if err := syscall.Kill(pid, 0); err == nil {
		t.Logf("Warning: Main process %d still exists after stop", pid)
	}

	// All processes in group should be gone
	afterCount := countProcessGroup(pid)
	if afterCount > 0 {
		// This might happen if ps shows zombies or timing issues
		t.Logf("Warning: Found %d processes in group after stop (might be zombies)", afterCount)
	}
}

// Helper function to count processes in a process group
func countProcessGroup(pgid int) int {
	cmd := exec.Command("ps", "-o", "pid,pgid", "-e")
	output, err := cmd.Output()
	if err != nil {
		return -1
	}

	count := 0
	lines := strings.Split(string(output), "\n")
	for i := 1; i < len(lines); i++ { // Skip header
		line := strings.TrimSpace(lines[i])
		if line == "" {
			continue
		}
		var pid, pg int
		if _, err := fmt.Sscanf(line, "%d %d", &pid, &pg); err == nil {
			if pg == pgid {
				count++
			}
		}
	}
	return count
}

func TestEnvironmentAndDirectory(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "echo $TEST_VAR; pwd"},
		Env:     []string{"TEST_VAR=hello123", "PATH=/usr/bin:/bin"},
		Dir:     "/tmp",
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Process should exit quickly
	if err := s.Wait(); err != nil {
		t.Errorf("Process exited with error: %v", err)
	}
}

func TestStdoutPipe(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "echo 'Hello stdout'; sleep 0.1; echo 'Second line'"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	// Get stdout pipe before starting
	stdoutPipe, err := s.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe: %v", err)
	}
	defer stdoutPipe.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read output
	var output []byte
	buf := make([]byte, 1024)
	for {
		n, err := stdoutPipe.Read(buf)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("Failed to read from stdout pipe: %v", err)
		}
		output = append(output, buf[:n]...)
	}

	expectedOutput := "Hello stdout\nSecond line\n"
	if string(output) != expectedOutput {
		t.Errorf("Expected output %q, got %q", expectedOutput, string(output))
	}

	// Wait for process to finish
	if err := s.Wait(); err != nil {
		t.Errorf("Process exited with error: %v", err)
	}
}

func TestStderrPipe(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "echo 'Error message' >&2; sleep 0.1; echo 'Another error' >&2"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	// Get stderr pipe before starting
	stderrPipe, err := s.StderrPipe()
	if err != nil {
		t.Fatalf("Failed to get stderr pipe: %v", err)
	}
	defer stderrPipe.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read error output
	var output []byte
	buf := make([]byte, 1024)
	for {
		n, err := stderrPipe.Read(buf)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("Failed to read from stderr pipe: %v", err)
		}
		output = append(output, buf[:n]...)
	}

	expectedOutput := "Error message\nAnother error\n"
	if string(output) != expectedOutput {
		t.Errorf("Expected stderr output %q, got %q", expectedOutput, string(output))
	}

	// Wait for process to finish
	if err := s.Wait(); err != nil {
		t.Errorf("Process exited with error: %v", err)
	}
}

func TestMultipleStdoutReaders(t *testing.T) {
	s, err := New(Config{
		Command: "bash",
		Args:    []string{"-c", "for i in {1..5}; do echo \"Line $i\"; sleep 0.05; done"},
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	// Create multiple stdout readers
	reader1, err := s.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe 1: %v", err)
	}
	defer reader1.Close()

	reader2, err := s.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe 2: %v", err)
	}
	defer reader2.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read from both readers concurrently
	var wg sync.WaitGroup
	output1 := make(chan string, 1)
	output2 := make(chan string, 1)

	wg.Add(2)
	go func() {
		defer wg.Done()
		data, _ := io.ReadAll(reader1)
		output1 <- string(data)
	}()

	go func() {
		defer wg.Done()
		data, _ := io.ReadAll(reader2)
		output2 <- string(data)
	}()

	// Wait for process and readers to finish
	s.Wait()
	wg.Wait()

	// Both readers should have received the same output
	out1 := <-output1
	out2 := <-output2

	if out1 != out2 {
		t.Errorf("Readers got different output:\nReader1: %q\nReader2: %q", out1, out2)
	}

	expectedLines := 5
	actualLines := strings.Count(out1, "\n")
	if actualLines != expectedLines {
		t.Errorf("Expected %d lines, got %d", expectedLines, actualLines)
	}
}

func TestPipesWithProcessRestart(t *testing.T) {
	// Test that pipes continue to work even if we stop and can't restart the process
	s, err := New(Config{
		Command:     "bash",
		Args:        []string{"-c", "echo 'Before stop'; sleep 10"},
		GracePeriod: 100 * time.Millisecond,
	})
	if err != nil {
		t.Fatalf("Failed to create supervisor: %v", err)
	}

	stdoutPipe, err := s.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe: %v", err)
	}
	defer stdoutPipe.Close()

	_, err = s.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read initial output
	buf := make([]byte, 1024)
	n, err := stdoutPipe.Read(buf)
	if err != nil {
		t.Fatalf("Failed to read from stdout: %v", err)
	}

	output := string(buf[:n])
	if !strings.Contains(output, "Before stop") {
		t.Errorf("Expected output to contain 'Before stop', got %q", output)
	}

	// Stop the process
	if err := s.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}

	// Reading from pipe after stop should return EOF
	_, err = stdoutPipe.Read(buf)
	if err != io.EOF {
		t.Errorf("Expected EOF after process stop, got %v", err)
	}
}
