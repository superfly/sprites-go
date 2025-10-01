package tests

import (
	"bufio"
	"context"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestLiveIntegration tests the client against a live sprite-env server
func TestLiveIntegration(t *testing.T) {
	spriteURL := os.Getenv("SPRITE_URL")
	spriteToken := os.Getenv("SPRITE_TOKEN")
	flyAppName := os.Getenv("FLY_APP_NAME")

	if spriteURL == "" || spriteToken == "" {
		t.Skip("SPRITE_URL and SPRITE_TOKEN environment variables not set")
	}

	// Get the project root directory
	projectRoot, err := filepath.Abs("..")
	if err != nil {
		t.Fatalf("Failed to get project root: %v", err)
	}

	// Build the client
	t.Log("Building client...")
	buildCmd := exec.Command("make", "build")
	buildCmd.Dir = projectRoot
	buildOutput, err := buildCmd.CombinedOutput()
	if err != nil {
		t.Fatalf("Failed to build client: %v\nOutput: %s", err, buildOutput)
	}
	t.Log("Client built successfully")

	// Run the exec command with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	spritePath := filepath.Join(projectRoot, "dist", "sprite")
	cmd := exec.CommandContext(ctx, spritePath, "--debug", "exec", "ls", "-la")
	cmd.Dir = projectRoot

	// Capture stdout and stderr
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to create stdout pipe: %v", err)
	}

	stderr, err := cmd.StderrPipe()
	if err != nil {
		t.Fatalf("Failed to create stderr pipe: %v", err)
	}

	// Start the command
	if err := cmd.Start(); err != nil {
		t.Fatalf("Failed to start command: %v", err)
	}

	// Read stdout with a timeout
	outputChan := make(chan string, 1)
	go func() {
		scanner := bufio.NewScanner(stdout)
		var output strings.Builder
		for scanner.Scan() {
			output.WriteString(scanner.Text() + "\n")
			// Send output as soon as we get any
			select {
			case outputChan <- output.String():
			default:
			}
		}
	}()

	// Wait for output or timeout
	var output string
	select {
	case output = <-outputChan:
		t.Logf("Received output:\n%s", output)
	case <-ctx.Done():
		// Command timed out, check logs if FLY_APP_NAME is set
		if flyAppName != "" {
			t.Log("No output received within 10 seconds, checking logs...")
			logCmd := exec.Command("fly", "logs", "-a", flyAppName, "--no-tail")
			logOutput, err := logCmd.CombinedOutput()
			if err != nil {
				t.Logf("Failed to get logs: %v", err)
			} else {
				lines := strings.Split(string(logOutput), "\n")
				start := len(lines) - 5
				if start < 0 {
					start = 0
				}
				lastLines := lines[start:]
				t.Logf("Last 5 log lines:\n%s", strings.Join(lastLines, "\n"))
			}
		}
		t.Fatal("Test failed: no output received within 10 seconds")
	}

	// Wait for command to finish
	if err := cmd.Wait(); err != nil {
		// Read stderr for error details
		stderrOutput, _ := io.ReadAll(stderr)
		t.Logf("Command stderr: %s", stderrOutput)
		t.Logf("Command output received: %s", output)

		// Check logs if FLY_APP_NAME is set
		if flyAppName != "" {
			t.Log("Command failed, checking logs...")
			logCmd := exec.Command("fly", "logs", "-a", flyAppName, "--no-tail")
			logOutput, err := logCmd.CombinedOutput()
			if err != nil {
				t.Logf("Failed to get logs: %v", err)
			} else {
				lines := strings.Split(string(logOutput), "\n")
				start := len(lines) - 5
				if start < 0 {
					start = 0
				}
				lastLines := lines[start:]
				t.Logf("Last 5 log lines:\n%s", strings.Join(lastLines, "\n"))
			}
		}
		t.Fatalf("Command failed: %v", err)
	}
}
