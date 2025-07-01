package terminal

import (
	"bytes"
	"context"
	"log/slog"
	"os"
	"strings"
	"testing"
	"time"
)

// TestIntegrationBasicShellCommands tests basic shell command execution
func TestIntegrationBasicShellCommands(t *testing.T) {
	tests := []struct {
		name     string
		command  []string
		tty      bool
		expected string
	}{
		{
			name:     "echo command no-tty",
			command:  []string{"echo", "hello world"},
			tty:      false,
			expected: "hello world",
		},
		{
			name:     "pwd command no-tty",
			command:  []string{"pwd"},
			tty:      false,
			expected: "/", // Will contain current directory
		},
		{
			name:     "echo command with tty",
			command:  []string{"echo", "hello pty"},
			tty:      true,
			expected: "hello pty",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if tt.tty && os.Getenv("CI") != "" {
				t.Skip("Skipping PTY test in CI environment")
			}

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			transcript := NewMemoryTranscript()
			session := NewSession(
				WithCommand(tt.command[0], tt.command[1:]...),
				WithTTY(tt.tty),
				WithTranscript(transcript),
			)

			stdin := strings.NewReader("")
			stdout := &bytes.Buffer{}
			stderr := &bytes.Buffer{}

			exitCode, err := session.Run(ctx, stdin, stdout, stderr)
			if err != nil {
				t.Fatalf("Run failed: %v", err)
			}

			if exitCode != 0 {
				t.Errorf("expected exit code 0, got %d", exitCode)
			}

			output := stdout.String()
			if !strings.Contains(output, tt.expected) {
				t.Errorf("expected output to contain %q, got %q", tt.expected, output)
			}

			// Verify transcript recording
			stdoutData := transcript.GetStreamData("stdout")
			if !strings.Contains(string(stdoutData), tt.expected) {
				t.Errorf("expected transcript to contain %q, got %q", tt.expected, string(stdoutData))
			}
		})
	}
}

// TestIntegrationComplexPipeline tests a more complex command pipeline
func TestIntegrationComplexPipeline(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Create a temporary directory for testing
	tempDir := t.TempDir()

	// Test a complex shell command with environment and working directory
	transcript := NewMemoryTranscript()
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	session := NewSession(
		WithCommand("sh", "-c", "echo $TEST_VAR > test_file.txt && cat test_file.txt && pwd"),
		WithTTY(false),
		WithEnv([]string{"TEST_VAR=integration_test_value"}),
		WithDir(tempDir),
		WithTranscript(transcript),
		WithLogger(logger),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := session.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	output := stdout.String()

	// Should contain the environment variable value
	if !strings.Contains(output, "integration_test_value") {
		t.Errorf("expected output to contain environment variable value, got %q", output)
	}

	// Should contain the temporary directory path
	if !strings.Contains(output, tempDir) {
		t.Errorf("expected output to contain temp dir %q, got %q", tempDir, output)
	}

	// Verify file was created in the correct directory
	filePath := tempDir + "/test_file.txt"
	if _, err := os.Stat(filePath); os.IsNotExist(err) {
		t.Errorf("expected file %q to be created", filePath)
	}

	// Verify transcript captured everything
	allStreams := transcript.GetAllStreams()
	if len(allStreams) == 0 {
		t.Error("expected transcript to capture streams")
	}

	stdoutData := string(allStreams["stdout"])
	if !strings.Contains(stdoutData, "integration_test_value") {
		t.Errorf("expected transcript stdout to contain environment variable, got %q", stdoutData)
	}
}

// TestIntegrationFileTranscript tests file-based transcript recording
func TestIntegrationFileTranscript(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create temporary transcript file
	transcriptPath := "/tmp/test-integration-transcript.log"
	defer os.Remove(transcriptPath + "*") // Remove generated files

	fileTranscript, err := NewFileTranscript(transcriptPath)
	if err != nil {
		t.Fatalf("failed to create file transcript: %v", err)
	}
	defer fileTranscript.Close()

	session := NewSession(
		WithCommand("echo", "line1"),
		WithTTY(false),
		WithTranscript(fileTranscript),
	)

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	exitCode, err := session.Run(ctx, stdin, stdout, stderr)
	if err != nil {
		t.Fatalf("Run failed: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("expected exit code 0, got %d", exitCode)
	}

	// Close transcript to flush buffers
	fileTranscript.Close()

	// Verify file was created
	files, err := os.ReadDir("/tmp")
	if err != nil {
		t.Fatalf("failed to read temp directory: %v", err)
	}

	found := false
	for _, file := range files {
		if strings.HasPrefix(file.Name(), "test-integration-transcript-") {
			found = true
			break
		}
	}

	if !found {
		t.Error("transcript file was not created")
	}
}

// TestIntegrationErrorHandling tests error scenarios
func TestIntegrationErrorHandling(t *testing.T) {
	tests := []struct {
		name             string
		command          []string
		expectedExitCode int
		expectError      bool
	}{
		{
			name:             "command not found",
			command:          []string{"nonexistent-command-12345"},
			expectedExitCode: -1,   // Command not found typically returns -1
			expectError:      true, // Should return error for command not found
		},
		{
			name:             "command with non-zero exit",
			command:          []string{"sh", "-c", "exit 42"},
			expectedExitCode: 42,
			expectError:      false,
		},
		{
			name:             "command writing to stderr",
			command:          []string{"sh", "-c", "echo 'error message' >&2; exit 1"},
			expectedExitCode: 1,
			expectError:      false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			transcript := NewMemoryTranscript()
			session := NewSession(
				WithCommand(tt.command[0], tt.command[1:]...),
				WithTTY(false),
				WithTranscript(transcript),
			)

			stdin := strings.NewReader("")
			stdout := &bytes.Buffer{}
			stderr := &bytes.Buffer{}

			exitCode, err := session.Run(ctx, stdin, stdout, stderr)

			if tt.expectError && err == nil {
				t.Error("expected error but got none")
			}
			if !tt.expectError && err != nil {
				t.Errorf("unexpected error: %v", err)
			}

			if exitCode != tt.expectedExitCode {
				t.Errorf("expected exit code %d, got %d", tt.expectedExitCode, exitCode)
			}

			// For stderr test, verify stderr was captured
			if strings.Contains(tt.name, "stderr") {
				stderrOutput := stderr.String()
				if !strings.Contains(stderrOutput, "error message") {
					t.Errorf("expected stderr to contain 'error message', got %q", stderrOutput)
				}

				// Check transcript captured stderr
				stderrData := transcript.GetStreamData("stderr")
				if !strings.Contains(string(stderrData), "error message") {
					t.Errorf("expected transcript stderr to contain 'error message', got %q", string(stderrData))
				}
			}
		})
	}
}
