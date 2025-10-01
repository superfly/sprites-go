package tests

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/alecthomas/assert/v2"
	"github.com/creack/pty"
)

var (
	appName     string
	spriteToken string
)

func init() {
	appName = os.Getenv("FLY_APP_NAME")

	if appName == "" {
		fmt.Printf("warning: FLY_APP_NAME not set\n")
	}

	spriteToken = os.Getenv("SPRITE_TOKEN")
}

func TestRollback(t *testing.T) {
	t.Skip()

	spriteURL := getSpriteURL(t, appName)

	if appName == "" || spriteToken == "" || spriteURL == "" {
		t.Logf("skipping TestRollback: missing FLY_APP_NAME or SPRITE_TOKEN or SPRITE_URL")
		t.Skip()
	}

	run := func(args ...string) string {
		return runSpriteCommandTolerant(t, spriteURL, spriteToken, args...)
	}

	x := func(args ...string) string {
		return run(append([]string{"exec"}, args...)...)
	}

	csum := func(fn string) (sum string, ok bool) {
		r := strings.TrimSpace(x("sum", "/data/test.file"))
		sum, rest, _ := strings.Cut(r, " ")
		if !strings.Contains(rest, "test.file") {
			return "", false
		}

		return sum, true
	}

	ready := func(wait time.Duration) bool {
		alive, _ := trySpriteCommandTolerant(spriteURL, spriteToken, "exec", "uname")
		ok := strings.Contains(alive, "Linux")
		if !ok {
			time.Sleep(wait)
		}
		return ok
	}

	waitup := func() {
		up := false
		for i := 0; i < 10; i++ {
			if ready(250 * time.Millisecond) {
				up = true
				break
			}
		}

		assert.True(t, up)
	}

	t.Run("SimpleRollback", func(t *testing.T) {
		x("dd", "if=/dev/random", "of=/data/test.file", "bs=4k", "count=200")

		sum, ok := csum("/data/test.file")
		assert.True(t, ok)

		result := run("checkpoint", "create")
		lines := strings.Split(result, "\n")
		assert.True(t, len(lines) >= 3)
		checktup := strings.Split(lines[2], " ")
		assert.Equal(t, checktup[3], "successfully")
		checkpoint := checktup[1]

		x("dd", "if=/dev/random", "of=/data/test.file", "count=1", "bs=512", "seek=1024")

		ns, ok := csum("/data/test.file")
		assert.True(t, ok)
		assert.NotEqual(t, sum, ns)

		run("restore", checkpoint)

		waitup()

		fsum, ok := csum("/data/test.file")
		assert.True(t, ok)
		assert.Equal(t, sum, fsum)
	})

	t.Run("LoopRollback", func(t *testing.T) {
		x("dd", "if=/dev/random", "of=/data/test.file", "bs=4k", "count=200")

		sum, ok := csum("/data/test.file")
		assert.True(t, ok)

		result := run("checkpoint", "create")
		lines := strings.Split(result, "\n")
		assert.True(t, len(lines) >= 3)
		checktup := strings.Split(lines[2], " ")
		assert.Equal(t, checktup[3], "successfully")
		checkpoint := checktup[1]

		x("dd", "if=/dev/random", "of=/dev/loop0", "count=6", "bs=1M", "seek=1024")
		x("dd", "if=/dev/random", "of=/data/test2.file", "bs=4k", "count=200")

		run("restore", checkpoint)

		waitup()

		fsum, ok := csum("/data/test.file")
		assert.True(t, ok)
		assert.Equal(t, sum, fsum)
	})

	t.Run("LoopBigRollback", func(t *testing.T) {
		t.Skip()

		x("dd", "if=/dev/random", "of=/data/test.file", "bs=4k", "count=200")

		sum, ok := csum("/data/test.file")
		assert.True(t, ok)

		result := run("checkpoint", "create")
		lines := strings.Split(result, "\n")
		assert.True(t, len(lines) >= 3)
		checktup := strings.Split(lines[2], " ")
		assert.Equal(t, checktup[3], "successfully")
		checkpoint := checktup[1]

		x("dd", "if=/dev/random", "of=/dev/loop0", "count=6000", "bs=1M", "seek=1024")
		x("dd", "if=/dev/random", "of=/data/test2.file", "bs=4k", "count=200")
		t.Logf("%s\n", x("ls", "/tmp"))

		run("restore", checkpoint)

		waitup()

		fsum, ok := csum("/data/test.file")
		assert.True(t, ok)
		assert.Equal(t, sum, fsum)
	})

}

// TestDeployAndFunctionality tests the full deployment and sprite functionality
func TestDeployAndFunctionality(t *testing.T) {
	// Get app name from environment
	if appName == "" {
		t.Skip("FLY_APP_NAME not set, skipping integration test")
	}

	// Step 1: Deploy the sprite
	t.Run("Deploy", func(t *testing.T) {
		cmd := exec.Command("go", "run", "deploy.go", "-a", appName)
		cmd.Dir = "../cmd"
		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr

		if err := cmd.Run(); err != nil {
			t.Fatalf("Failed to deploy: %v", err)
		}

		// Give the machine a bit more time to fully initialize
		t.Log("Waiting for deployment to fully initialize...")
		time.Sleep(30 * time.Second)
	})

	// Step 2: Build the sprite client
	t.Run("BuildClient", func(t *testing.T) {
		// The sprite client should already be built by `make build`
		// Just verify the binary exists
		spritePath := "../dist/sprite"
		if _, err := os.Stat(spritePath); err != nil {
			t.Fatalf("Sprite binary not found at %s. Make sure to run 'make build' first: %v", spritePath, err)
		}
		t.Logf("Found sprite binary at %s", spritePath)
	})

	// Get sprite URL from flyctl
	spriteURL := getSpriteURL(t, appName)
	if spriteToken == "" {
		t.Fatal("SPRITE_TOKEN not set")
	}

	// Step 3: Test basic sprite commands
	t.Run("BasicCommands", func(t *testing.T) {
		// Retry the echo command a few times in case the container isn't ready
		var output string
		var err error
		maxRetries := 5

		for i := 0; i < maxRetries; i++ {
			cmd := exec.Command("../dist/sprite", "exec", "echo", "hello", "sprite")
			cmd.Env = append(os.Environ(),
				fmt.Sprintf("SPRITE_URL=%s", spriteURL),
				fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
			)

			outputBytes, cmdErr := cmd.CombinedOutput()
			output = string(outputBytes)
			err = cmdErr

			if err == nil && strings.Contains(output, "hello sprite") {
				break // Success
			}

			if i < maxRetries-1 {
				t.Logf("Retry %d/%d: Command failed, waiting 2 seconds before retry...", i+1, maxRetries)
				time.Sleep(2 * time.Second)
			}
		}

		if err != nil {
			t.Fatalf("Echo command failed after %d retries: %v\nOutput: %s", maxRetries, err, output)
		}

		if !strings.Contains(output, "hello sprite") {
			t.Errorf("Expected 'hello sprite', got: %s", output)
		}

		// Test exec with file creation
		testFile := fmt.Sprintf("/tmp/test_%d.txt", rand.Int())
		runSpriteCommand(t, spriteURL, spriteToken, "exec", "touch", testFile)

		// Verify file exists - use tolerant version since crun might return non-zero exit code
		output = runSpriteCommandTolerant(t, spriteURL, spriteToken, "exec", "ls", "-la", testFile)
		if !strings.Contains(output, testFile) {
			t.Errorf("Test file not found: %s", output)
		}
	})

	// Step 4: Test zombie cleanup
	t.Run("ZombieCleanup", func(t *testing.T) {
		// Test that sprite properly reaps zombie processes as PID 1
		client := &http.Client{Timeout: 10 * time.Second}

		req, err := http.NewRequest("POST", fmt.Sprintf("%s/debug/create-zombie", spriteURL), nil)
		if err != nil {
			t.Fatalf("Failed to create request: %v", err)
		}
		req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", spriteToken))

		resp, err := client.Do(req)
		if err != nil {
			t.Fatalf("Failed to call zombie endpoint: %v", err)
		}
		defer resp.Body.Close()

		if resp.StatusCode != http.StatusOK {
			body, _ := io.ReadAll(resp.Body)
			t.Fatalf("Failed to test zombie reaping: status %d, body: %s", resp.StatusCode, string(body))
		}

		var result struct {
			Message      string `json:"message"`
			PID          int    `json:"pid"`
			WasZombie    bool   `json:"was_zombie"`
			WasReaped    bool   `json:"was_reaped"`
			ReapDuration string `json:"reap_duration"`
			Success      string `json:"success,omitempty"`
			Error        string `json:"error,omitempty"`
			Warning      string `json:"warning,omitempty"`
		}

		if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
			t.Fatalf("Failed to decode response: %v", err)
		}

		t.Logf("Zombie reaping test result: PID=%d, WasZombie=%v, WasReaped=%v, Duration=%s",
			result.PID, result.WasZombie, result.WasReaped, result.ReapDuration)

		// The process should have been reaped
		if !result.WasReaped {
			t.Errorf("Zombie process was not reaped: %s", result.Error)
		}

		// Log success message if present
		if result.Success != "" {
			t.Logf("Success: %s", result.Success)
		}

		// Log warning if we couldn't observe zombie state (this is OK)
		if result.Warning != "" {
			t.Logf("Warning: %s", result.Warning)
		}
	})

	// Step 5: Test checkpoint and restore
	t.Run("CheckpointRestore", func(t *testing.T) {
		// Test checkpoint/restore by writing files that should persist
		// The /data mount is accessible from containers and should be included in checkpoints
		testFile := fmt.Sprintf("/data/checkpoint_test_%d.txt", time.Now().Unix())
		originalContent := fmt.Sprintf("original content %d", time.Now().Unix())

		// Create a test file
		runSpriteCommand(t, spriteURL, spriteToken, "exec", "sh", "-c",
			fmt.Sprintf("echo '%s' > %s", originalContent, testFile))

		// Verify file exists with original content
		output := runSpriteCommandTolerant(t, spriteURL, spriteToken, "exec", "cat", testFile)
		if !strings.Contains(output, originalContent) {
			t.Fatalf("File content mismatch: expected %s, got %s", originalContent, output)
		}

		// Create a checkpoint
		output = runSpriteCommand(t, spriteURL, spriteToken, "checkpoint", "create")
		t.Logf("Checkpoint output: %s", output)

		// Parse the checkpoint version from output
		// Look for "Checkpoint vX created successfully"
		var checkpointVersion string
		lines := strings.Split(output, "\n")
		for _, line := range lines {
			if strings.Contains(line, "Checkpoint") && strings.Contains(line, "created successfully") {
				// Extract version from line like "Checkpoint v1 created successfully"
				parts := strings.Fields(line)
				for _, part := range parts {
					if strings.HasPrefix(part, "v") && len(part) > 1 {
						if _, err := strconv.Atoi(part[1:]); err == nil {
							checkpointVersion = part
							break
						}
					}
				}
			}
		}

		if checkpointVersion == "" {
			t.Fatalf("Failed to parse checkpoint version from output: %s", output)
		}

		t.Logf("Created checkpoint version: %s", checkpointVersion)

		// Wait for checkpoint to complete
		time.Sleep(5 * time.Second)

		// List checkpoints to get the version that was created
		output = runSpriteCommand(t, spriteURL, spriteToken, "checkpoint", "list")
		t.Logf("Checkpoints list: %s", output)

		// Modify the file
		modifiedContent := fmt.Sprintf("modified content %d", time.Now().Unix())
		runSpriteCommand(t, spriteURL, spriteToken, "exec", "sh", "-c",
			fmt.Sprintf("echo '%s' > %s", modifiedContent, testFile))

		// Verify file was modified
		output = runSpriteCommandTolerant(t, spriteURL, spriteToken, "exec", "cat", testFile)
		if !strings.Contains(output, modifiedContent) {
			t.Fatalf("File should be modified: expected %s, got %s", modifiedContent, output)
		}

		// Delete the file entirely to make the test more robust
		runSpriteCommand(t, spriteURL, spriteToken, "exec", "rm", "-f", testFile)

		// Add debugging: verify file deletion with explicit check
		// Verify file is gone
		cmd := exec.Command("../dist/sprite", "exec", "ls", testFile)
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)
		lsOutput, err := cmd.CombinedOutput()
		t.Logf("ls command output after rm: %s", string(lsOutput))
		t.Logf("ls command error after rm: %v", err)

		// Also try with ls -la to see if file exists (don't fail if this errors)
		debugCmd := exec.Command("../dist/sprite", "exec", "ls", "-la", filepath.Dir(testFile))
		debugCmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)
		debugOutput, debugErr := debugCmd.CombinedOutput()
		t.Logf("Directory listing after rm: %s (error: %v)", string(debugOutput), debugErr)

		if err == nil {
			t.Fatal("File should have been deleted")
		}

		// Restore from checkpoint
		output = runSpriteCommand(t, spriteURL, spriteToken, "restore", checkpointVersion)
		t.Logf("Restored from checkpoint %s", checkpointVersion)
		t.Logf("Restore output: %s", output)

		// Wait for restore to complete and process to restart
		time.Sleep(20 * time.Second)

		// Verify file is back with original content
		output = runSpriteCommandTolerant(t, spriteURL, spriteToken, "exec", "cat", testFile)
		t.Logf("File content after restore: %s", output)
		if !strings.Contains(output, originalContent) {
			t.Fatalf("File not restored correctly: expected %s, got %s", originalContent, output)
		}

		// Clean up
		cleanupCmd := exec.Command("../dist/sprite", "exec", "rm", "-f", testFile)
		cleanupCmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)
		if output, err := cleanupCmd.CombinedOutput(); err != nil {
			t.Logf("Warning: Cleanup failed (non-fatal): %v\nOutput: %s", err, string(output))
		}
	})

	// Test WebSocket TTY exit with real PTY
	t.Run("WebSocketTTYExitWithPTY", func(t *testing.T) {
		t.Log("Testing WebSocket TTY exit behavior with real PTY...")

		// Use sprite exec with TTY
		cmd := exec.Command("../dist/sprite", "exec", "-tty", "/bin/bash")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		// Start with PTY
		ptmx, err := pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start with PTY: %v", err)
		}
		defer ptmx.Close()

		// Read output in background
		output := &bytes.Buffer{}
		done := make(chan error, 1)
		go func() {
			_, err := io.Copy(output, ptmx)
			done <- err
		}()

		// Wait for prompt
		time.Sleep(1 * time.Second)

		// Send commands
		commands := []string{
			"echo 'Starting PTY test'\n",
			"pwd\n",
			"echo 'Test complete'\n",
			"exit\n",
		}

		for _, cmd := range commands {
			t.Logf("Sending command: %q", strings.TrimSpace(cmd))
			if _, err := ptmx.Write([]byte(cmd)); err != nil {
				t.Fatalf("Failed to write command: %v", err)
			}
			time.Sleep(500 * time.Millisecond) // Give time for command to execute
		}

		// Set a timeout for the entire operation
		timeout := time.After(10 * time.Second)
		cmdDone := make(chan error, 1)

		go func() {
			cmdDone <- cmd.Wait()
		}()

		// Wait for command to complete or timeout
		select {
		case err := <-cmdDone:
			t.Log("Command completed")
			if err != nil {
				if exitErr, ok := err.(*exec.ExitError); ok {
					t.Logf("Exit code: %d", exitErr.ExitCode())
					if exitErr.ExitCode() != 0 {
						t.Errorf("Expected exit code 0, got %d", exitErr.ExitCode())
					}
				} else {
					t.Errorf("Command failed with error: %v", err)
				}
			} else {
				t.Log("Command exited successfully with code 0")
			}

		case <-timeout:
			t.Error("Command timed out after 10 seconds - TTY session is hanging")
			// Try to kill the process
			cmd.Process.Kill()
			<-cmdDone // Wait for it to actually die
		}

		// Check output
		outputStr := output.String()
		t.Logf("PTY output:\n%s", outputStr)

		// Verify we got expected output
		if !strings.Contains(outputStr, "Starting PTY test") {
			t.Error("Expected 'Starting PTY test' in output")
		}
		if !strings.Contains(outputStr, "Test complete") {
			t.Error("Expected 'Test complete' in output")
		}
	})

	// Test interactive TTY commands with exit
	t.Run("InteractiveTTYExit", func(t *testing.T) {
		t.Log("Testing interactive TTY commands with exit...")

		// Use a shorter timeout for this test
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		cmd := exec.CommandContext(ctx, "../dist/sprite", "exec", "-tty", "/bin/bash", "-c", "echo 'Hello'; sleep 1; echo 'World'; exit 0")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		output, err := cmd.CombinedOutput()

		if ctx.Err() == context.DeadlineExceeded {
			t.Errorf("Command timed out after 10 seconds")
			t.Logf("Output before timeout: %s", output)
		} else if err != nil {
			t.Logf("Command failed with error: %v", err)
			t.Logf("Output: %s", output)
			// Check exit code
			if exitErr, ok := err.(*exec.ExitError); ok {
				if exitErr.ExitCode() != 0 {
					t.Errorf("Expected exit code 0, got %d", exitErr.ExitCode())
				}
			}
		} else {
			t.Log("Command completed successfully")
			t.Logf("Output: %s", output)

			// Verify output
			if !strings.Contains(string(output), "Hello") {
				t.Error("Expected 'Hello' in output")
			}
			if !strings.Contains(string(output), "World") {
				t.Error("Expected 'World' in output")
			}
		}
	})
}

// Helper function to get sprite URL from flyctl
func getSpriteURL(t *testing.T, appName string) string {
	// First try to get the app status
	cmd := exec.Command("flyctl", "status", "-a", appName, "--json")
	output, err := cmd.Output()
	if err != nil {
		t.Fatalf("Failed to get app status: %v", err)
	}

	t.Logf("Flyctl status output: %s", string(output))

	var status struct {
		Hostname string `json:"Hostname"`
	}
	if err := json.Unmarshal(output, &status); err != nil {
		t.Fatalf("Failed to parse app status: %v", err)
	}

	url := fmt.Sprintf("https://%s", status.Hostname)
	t.Logf("Using sprite URL: %s", url)
	return url
}

// Helper function to run sprite commands
func runSpriteCommand(t *testing.T, url, token string, args ...string) string {
	cmd := exec.Command("../dist/sprite", args...)
	cmd.Env = append(os.Environ(),
		fmt.Sprintf("SPRITE_URL=%s", url),
		fmt.Sprintf("SPRITE_TOKEN=%s", token),
	)

	output, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("Sprite command failed: %v\nOutput: %s", err, string(output))
	}

	return string(output)
}

// Helper function to run sprite commands with output tolerance
// This version doesn't fail on non-zero exit codes if output is produced
func runSpriteCommandTolerant(t *testing.T, url, token string, args ...string) string {
	cmd := exec.Command("../dist/sprite", args...)
	cmd.Env = append(os.Environ(),
		fmt.Sprintf("SPRITE_URL=%s", url),
		fmt.Sprintf("SPRITE_TOKEN=%s", token),
	)

	output, err := cmd.CombinedOutput()
	if err != nil {
		// If we got output, just log a warning instead of failing
		if len(output) > 0 {
			t.Logf("Warning: Command exited with error but produced output: %v", err)
			t.Logf("output: %s\n", output)
			return string(output)
		}
		// If no output, then it's a real failure
		t.Fatalf("Sprite command failed: %v\nOutput: %s", err, string(output))
	}

	return string(output)
}

// when we expect the test to fail
func trySpriteCommandTolerant(url, token string, args ...string) (string, error) {
	cmd := exec.Command("../dist/sprite", args...)
	cmd.Env = append(os.Environ(),
		fmt.Sprintf("SPRITE_URL=%s", url),
		fmt.Sprintf("SPRITE_TOKEN=%s", token),
	)

	output, err := cmd.CombinedOutput()
	if err != nil {
		if len(output) > 0 {
			return string(output), nil
		}
		// If no output, then it's a real failure
		return "", fmt.Errorf("read command output: %w", err)
	}

	return string(output), nil
}

// Helper function to clean up after tests
func cleanupDeployment(t *testing.T, appName string) {
	// Note: This is optional - you might want to keep the deployment for debugging
	// Uncomment if you want automatic cleanup
	/*
		cmd := exec.Command("flyctl", "machine", "destroy", "-a", appName, "--force")
		if err := cmd.Run(); err != nil {
			t.Logf("Warning: Failed to cleanup deployment: %v", err)
		}
	*/
}
