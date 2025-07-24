package terminal

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"testing"
	"time"
)

func TestNewSession(t *testing.T) {
	s := NewSession()
	if s.path != "bash" {
		t.Errorf("expected default path 'bash', got %q", s.path)
	}
	if len(s.args) != 2 || s.args[0] != "bash" || s.args[1] != "-l" {
		t.Errorf("expected default args ['bash', '-l'], got %v", s.args)
	}
}

func TestSessionWithOptions(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(os.Stderr, nil))
	transcript := NewMemoryTranscript()

	s := NewSession(
		WithCommand("echo", "hello", "world"),
		WithTTY(true),
		WithEnv([]string{"TEST=value"}),
		WithDir("/tmp"),
		WithTerminalSize(80, 24),
		WithTranscript(transcript),
		WithLogger(logger),
	)

	if s.path != "echo" {
		t.Errorf("expected path 'echo', got %q", s.path)
	}
	if len(s.args) != 3 || s.args[0] != "echo" || s.args[1] != "hello" || s.args[2] != "world" {
		t.Errorf("expected args ['echo', 'hello', 'world'], got %v", s.args)
	}
	if !s.tty {
		t.Error("expected TTY to be enabled")
	}
	if len(s.env) != 1 || s.env[0] != "TEST=value" {
		t.Errorf("expected env ['TEST=value'], got %v", s.env)
	}
	if s.dir != "/tmp" {
		t.Errorf("expected dir '/tmp', got %q", s.dir)
	}
	if s.initialCols != 80 || s.initialRows != 24 {
		t.Errorf("expected terminal size 80x24, got %dx%d", s.initialCols, s.initialRows)
	}
	if s.transcript != transcript {
		t.Error("expected transcript to be set")
	}
	if s.logger != logger {
		t.Error("expected logger to be set")
	}
}

func TestRunWithoutTTY(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	transcript := NewMemoryTranscript()
	s := NewSession(
		WithCommand("echo", "hello world"),
		WithTTY(false),
		WithTranscript(transcript),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	output := stdout.String()
	if !strings.Contains(output, "hello world") {
		t.Errorf("expected output to contain 'hello world', got %q", output)
	}

	// Check transcript
	stdoutData := transcript.GetStreamData("stdout")
	if !strings.Contains(string(stdoutData), "hello world") {
		t.Errorf("expected transcript to contain 'hello world', got %q", string(stdoutData))
	}
}

func TestRunWithTTY(t *testing.T) {
	// Skip PTY tests on systems where they might not work
	if os.Getenv("CI") != "" {
		t.Skip("Skipping PTY test in CI environment")
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	transcript := NewMemoryTranscript()
	s := NewSession(
		WithCommand("echo", "hello pty"),
		WithTTY(true),
		WithTerminalSize(80, 24),
		WithTranscript(transcript),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	// In PTY mode, output goes to stdout
	output := stdout.String()
	if !strings.Contains(output, "hello pty") {
		t.Errorf("expected output to contain 'hello pty', got %q", output)
	}

	// Check transcript
	stdoutData := transcript.GetStreamData("stdout")
	if !strings.Contains(string(stdoutData), "hello pty") {
		t.Errorf("expected transcript to contain 'hello pty', got %q", string(stdoutData))
	}
}

func TestRunWithError(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	s := NewSession(
		WithCommand("sh", "-c", "exit 42"),
		WithTTY(false),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 42 {
		t.Errorf("expected exit code 42, got %d", exitCode)
	}
}

func TestRunWithStdinInput(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	transcript := NewMemoryTranscript()
	s := NewSession(
		WithCommand("cat"),
		WithTTY(false),
		WithTranscript(transcript),
	)

	input := "test input line\n"
	stdin := strings.NewReader(input)
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	output := stdout.String()
	if output != input {
		t.Errorf("expected output %q, got %q", input, output)
	}

	// Check transcript recorded both stdin and stdout
	stdinData := transcript.GetStreamData("stdin")
	if string(stdinData) != input {
		t.Errorf("expected stdin transcript %q, got %q", input, string(stdinData))
	}

	stdoutData := transcript.GetStreamData("stdout")
	if string(stdoutData) != input {
		t.Errorf("expected stdout transcript %q, got %q", input, string(stdoutData))
	}
}

func TestRunWithEnvAndDir(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	tempDir := t.TempDir()

	s := NewSession(
		WithCommand("sh", "-c", "echo $TEST_VAR && pwd"),
		WithEnv([]string{"TEST_VAR=test_value"}),
		WithDir(tempDir),
		WithTTY(false),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	output := stdout.String()
	if !strings.Contains(output, "test_value") {
		t.Errorf("expected output to contain 'test_value', got %q", output)
	}
	if !strings.Contains(output, tempDir) {
		t.Errorf("expected output to contain temp dir %q, got %q", tempDir, output)
	}
}

func TestRunWithWrapper(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create a simple wrapper script
	wrapperScript := `#!/bin/sh
echo "wrapper called with: $@"
exec "$@"
`
	wrapperPath := fmt.Sprintf("/tmp/test-wrapper-%d.sh", time.Now().UnixNano())
	defer os.Remove(wrapperPath)

	if err := os.WriteFile(wrapperPath, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("failed to create wrapper script: %v", err)
	}

	s := NewSession(
		WithCommand("echo", "hello from command"),
		WithWrapper([]string{wrapperPath}),
		WithTTY(false),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	output := stdout.String()
	if !strings.Contains(output, "wrapper called") {
		t.Errorf("expected output to contain 'wrapper called', got %q", output)
	}
	if !strings.Contains(output, "hello from command") {
		t.Errorf("expected output to contain 'hello from command', got %q", output)
	}
}

func TestContextCancellation(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	s := NewSession(
		WithCommand("sleep", "10"),
		WithTTY(false),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	start := time.Now()
	exitCode, err := s.Run(ctx, stdin, stdout, stderr)
	elapsed := time.Since(start)

	// Should complete within reasonable time due to context cancellation
	if elapsed > 2*time.Second {
		t.Errorf("command took too long to cancel: %v", elapsed)
	}

	// Exit code should be non-zero due to cancellation
	if exitCode == 0 {
		t.Errorf("expected non-zero exit code due to cancellation, got %d", exitCode)
	}

	// err should be nil even if command was cancelled
	if err != nil {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestBuildCommand(t *testing.T) {
	ctx := context.Background()

	tests := []struct {
		name     string
		session  *Session
		expected []string
	}{
		{
			name:     "simple command",
			session:  NewSession(WithCommand("echo", "hello")),
			expected: []string{"echo", "hello"},
		},
		{
			name:     "with wrapper",
			session:  NewSession(WithCommand("echo", "hello"), WithWrapper([]string{"/bin/sh", "-c"})),
			expected: []string{"/bin/sh", "-c", "echo", "hello"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cmd, err := tt.session.buildCommand(ctx)
			if err != nil {
				t.Fatalf("buildCommand failed: %v", err)
			}

			if len(cmd.Args) != len(tt.expected) {
				t.Errorf("expected %d args, got %d", len(tt.expected), len(cmd.Args))
			}

			for i, expected := range tt.expected {
				if i >= len(cmd.Args) || cmd.Args[i] != expected {
					t.Errorf("expected arg[%d] = %q, got %q", i, expected, cmd.Args[i])
				}
			}
		})
	}
}

// TestRunWithOnProcessStartCallback tests the PID callback functionality
func TestRunWithOnProcessStartCallback(t *testing.T) {
	var receivedPID int
	callbackCalled := make(chan bool, 1)

	// Create session with PID callback
	session := NewSession(
		WithCommand("echo", "test"),
		WithOnProcessStart(func(pid int) {
			receivedPID = pid
			callbackCalled <- true
		}),
	)

	var stdout strings.Builder
	ctx := context.Background()

	// Run the command
	exitCode, err := session.Run(ctx, strings.NewReader(""), &stdout, &strings.Builder{})
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("Expected exit code 0, got %d", exitCode)
	}

	// Wait for callback
	select {
	case <-callbackCalled:
		if receivedPID <= 0 {
			t.Errorf("Expected positive PID, got %d", receivedPID)
		}
		t.Logf("Callback received PID: %d", receivedPID)
	case <-time.After(2 * time.Second):
		t.Error("Callback was not called within timeout")
	}

	// Check output
	output := strings.TrimSpace(stdout.String())
	if output != "test" {
		t.Errorf("Expected output 'test', got %q", output)
	}
}

// TestExecBufferVsPipe demonstrates the difference between using pipes and buffers
func TestExecBufferVsPipe(t *testing.T) {
	// Start CPU load to simulate the race condition
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	for i := 0; i < numCPU-1; i++ {
		go func() {
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	time.Sleep(100 * time.Millisecond)

	// Test with buffer approach (like CombinedOutput)
	t.Run("Buffer", func(t *testing.T) {
		failures := 0
		for i := 0; i < 20; i++ {
			cmd := exec.Command("echo", "hello")
			var stdout bytes.Buffer
			cmd.Stdout = &stdout

			err := cmd.Run()
			if err != nil {
				t.Errorf("iteration %d: command failed: %v", i, err)
				continue
			}

			if strings.TrimSpace(stdout.String()) != "hello" {
				failures++
				t.Logf("iteration %d: missing output", i)
			}
		}
		t.Logf("Buffer approach: %d failures out of 20", failures)
	})

	// Test with pipe approach
	t.Run("Pipe", func(t *testing.T) {
		failures := 0
		for i := 0; i < 20; i++ {
			cmd := exec.Command("echo", "hello")
			stdout, err := cmd.StdoutPipe()
			if err != nil {
				t.Errorf("iteration %d: pipe creation failed: %v", i, err)
				continue
			}

			var output bytes.Buffer
			done := make(chan struct{})

			go func() {
				defer close(done)
				buf := make([]byte, 1024)
				for {
					n, err := stdout.Read(buf)
					if n > 0 {
						output.Write(buf[:n])
					}
					if err != nil {
						break
					}
				}
			}()

			err = cmd.Start()
			if err != nil {
				t.Errorf("iteration %d: start failed: %v", i, err)
				continue
			}

			err = cmd.Wait()
			if err != nil {
				t.Errorf("iteration %d: wait failed: %v", i, err)
			}

			<-done

			if strings.TrimSpace(output.String()) != "hello" {
				failures++
				t.Logf("iteration %d: missing output, got %q", i, output.String())
			}
		}
		t.Logf("Pipe approach: %d failures out of 20", failures)
	})
}

// TestExecWithPipeWriter tests using io.Pipe to create a streaming solution
func TestExecWithPipeWriter(t *testing.T) {
	// Start CPU load
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	for i := 0; i < numCPU-1; i++ {
		go func() {
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	time.Sleep(100 * time.Millisecond)

	failures := 0
	for i := 0; i < 20; i++ {
		// Create a pipe
		reader, writer := io.Pipe()

		cmd := exec.Command("echo", "hello")
		cmd.Stdout = writer // exec package will handle writing to this

		var output bytes.Buffer
		done := make(chan struct{})

		// Start reading from the pipe
		go func() {
			defer close(done)
			io.Copy(&output, reader)
		}()

		// Run the command - this will:
		// 1. Start internal goroutines to copy from process stdout to our writer
		// 2. Wait for the process to exit
		// 3. Wait for the internal goroutines to finish
		// 4. Return
		err := cmd.Run()
		if err != nil {
			t.Errorf("iteration %d: command failed: %v", i, err)
			writer.Close()
			continue
		}

		// Close the writer to signal EOF to our reader
		writer.Close()

		// Wait for our reader to finish
		<-done

		if strings.TrimSpace(output.String()) != "hello" {
			failures++
			t.Logf("iteration %d: missing output, got %q", i, output.String())
		}
	}

	t.Logf("io.Pipe approach: %d failures out of 20", failures)
	if failures > 0 {
		t.Errorf("Failed %d times", failures)
	}
}

// TestRefactoredApproachUnderLoad tests our refactored io.Pipe approach
func TestRefactoredApproachUnderLoad(t *testing.T) {
	// Start CPU load
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	for i := 0; i < numCPU-1; i++ {
		go func() {
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	time.Sleep(100 * time.Millisecond)

	failures := 0
	for i := 0; i < 50; i++ { // More iterations to stress test
		cmd := exec.Command("sh", "-c", "echo hello && echo world >&2")

		// Create pipes
		stdoutReader, stdoutWriter := io.Pipe()
		stderrReader, stderrWriter := io.Pipe()

		cmd.Stdout = stdoutWriter
		cmd.Stderr = stderrWriter

		var stdoutBuf, stderrBuf bytes.Buffer
		done := make(chan struct{})

		// Start readers
		go func() {
			io.Copy(&stdoutBuf, stdoutReader)
			io.Copy(&stderrBuf, stderrReader)
			close(done)
		}()

		// Run command - exec ensures writers receive all data
		err := cmd.Run()
		if err != nil {
			t.Errorf("iteration %d: command failed: %v", i, err)
			stdoutWriter.Close()
			stderrWriter.Close()
			continue
		}

		// Close writers to signal EOF
		stdoutWriter.Close()
		stderrWriter.Close()

		// Wait for readers
		<-done

		// Check results
		gotStdout := strings.TrimSpace(stdoutBuf.String())
		gotStderr := strings.TrimSpace(stderrBuf.String())

		if gotStdout != "hello" || gotStderr != "world" {
			failures++
			t.Logf("iteration %d: stdout=%q, stderr=%q", i, gotStdout, gotStderr)
		}
	}

	t.Logf("Refactored approach: %d failures out of 50", failures)
	if failures > 0 {
		t.Errorf("Failed %d times", failures)
	}
}

// TestTTYModeUnderLoad verifies that TTY mode doesn't suffer from the race condition
func TestTTYModeUnderLoad(t *testing.T) {
	// Skip if not on a system with PTY support
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Start CPU load
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	for i := 0; i < numCPU-1; i++ {
		go func() {
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	time.Sleep(100 * time.Millisecond)

	failures := 0
	for i := 0; i < 20; i++ {
		var output bytes.Buffer

		session := NewSession(
			WithCommand("echo", "hello"),
			WithTTY(true), // Enable TTY mode
		)

		ctx := context.Background()
		exitCode, err := session.Run(ctx, &bytes.Buffer{}, &output, &output)
		if err != nil {
			t.Errorf("iteration %d: session failed: %v", i, err)
			continue
		}

		if exitCode != 0 {
			t.Errorf("iteration %d: unexpected exit code: %d", i, exitCode)
		}

		// Check output - in TTY mode we might get some extra control sequences
		if !strings.Contains(output.String(), "hello") {
			failures++
			t.Logf("iteration %d: missing 'hello' in output: %q", i, output.String())
		}
	}

	t.Logf("TTY mode: %d failures out of 20", failures)
	if failures > 0 {
		t.Errorf("TTY mode had %d failures - this is unexpected", failures)
	}
}
