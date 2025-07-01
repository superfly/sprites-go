package terminal

import (
	"bytes"
	"context"
	"fmt"
	"log/slog"
	"os"
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
