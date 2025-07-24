package tests

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

// TestExecRaceCondition specifically tests the race condition reported by the JS developer
// where fast-exiting commands lose their output
func TestExecRaceCondition(t *testing.T) {
	// Skip if not in integration test mode
	if os.Getenv("FLY_APP_NAME") == "" || os.Getenv("SPRITE_TOKEN") == "" {
		t.Skip("Skipping integration test: FLY_APP_NAME and SPRITE_TOKEN must be set")
	}

	// Get the sprite client path
	spritePath := filepath.Join("..", "dist", "sprite")
	if _, err := os.Stat(spritePath); os.IsNotExist(err) {
		// Try to build it
		t.Log("Building sprite client...")
		buildCmd := exec.Command("make", "-C", "..", "build-client")
		if output, err := buildCmd.CombinedOutput(); err != nil {
			t.Fatalf("Failed to build sprite client: %v\nOutput: %s", err, output)
		}
	}

	// Test cases from the original issue
	testCases := []struct {
		name     string
		args     []string
		expected string
	}{
		{
			name:     "echo hello world",
			args:     []string{"echo", "hello", "world"},
			expected: "hello world\n",
		},
		{
			name:     "pwd",
			args:     []string{"pwd"},
			expected: "/", // Should contain something
		},
		{
			name:     "printf small output",
			args:     []string{"sh", "-c", "printf 'small output\\n'"},
			expected: "small output\n",
		},
		{
			name:     "echo single char",
			args:     []string{"echo", "1"},
			expected: "1\n",
		},
		{
			name:     "printf without newline",
			args:     []string{"sh", "-c", "printf 'hello'"},
			expected: "hello",
		},
		{
			name:     "ultra short output",
			args:     []string{"sh", "-c", "printf 'x'"},
			expected: "x",
		},
	}

	// Run each test multiple times to catch intermittent failures
	iterations := 50
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			failureCount := 0
			var lastOutput string

			for i := 0; i < iterations; i++ {
				args := append([]string{"exec"}, tc.args...)
				cmd := exec.Command(spritePath, args...)

				output, err := cmd.CombinedOutput()
				if err != nil {
					t.Logf("Iteration %d: Command failed: %v", i, err)
					failureCount++
					continue
				}

				outputStr := string(output)
				lastOutput = outputStr

				// For pwd, just check we got something
				if tc.name == "pwd" {
					if len(outputStr) == 0 || outputStr == "\n" {
						failureCount++
						t.Logf("Iteration %d: No output received", i)
					}
				} else {
					// Check exact output
					if outputStr != tc.expected {
						failureCount++
						t.Logf("Iteration %d: Expected %q, got %q (len=%d)",
							i, tc.expected, outputStr, len(outputStr))
					}
				}
			}

			if failureCount > 0 {
				t.Errorf("Race condition detected: %d/%d iterations failed. Last output: %q",
					failureCount, iterations, lastOutput)
			} else {
				t.Logf("All %d iterations passed", iterations)
			}
		})
	}
}

// TestExecConcurrentRaceCondition tests multiple concurrent fast commands
func TestExecConcurrentRaceCondition(t *testing.T) {
	// Skip if not in integration test mode
	if os.Getenv("FLY_APP_NAME") == "" || os.Getenv("SPRITE_TOKEN") == "" {
		t.Skip("Skipping integration test: FLY_APP_NAME and SPRITE_TOKEN must be set")
	}

	spritePath := filepath.Join("..", "dist", "sprite")
	if _, err := os.Stat(spritePath); os.IsNotExist(err) {
		t.Skip("Sprite client not built")
	}

	// Run 20 concurrent commands
	concurrency := 20
	iterations := 5

	for iter := 0; iter < iterations; iter++ {
		t.Logf("Concurrent iteration %d", iter)

		var wg sync.WaitGroup
		errors := make(chan string, concurrency)

		for i := 0; i < concurrency; i++ {
			wg.Add(1)
			go func(id int) {
				defer wg.Done()

				// Each goroutine runs a unique command
				cmd := exec.Command(spritePath, "exec", "sh", "-c",
					"echo 'worker "+string(rune('0'+id%10))+"'")

				output, err := cmd.CombinedOutput()
				if err != nil {
					errors <- "Command error: " + err.Error()
					return
				}

				expected := "worker " + string(rune('0'+id%10)) + "\n"
				if string(output) != expected {
					errors <- "Output mismatch: got " + string(output)
				}
			}(i)
		}

		wg.Wait()
		close(errors)

		var errorList []string
		for err := range errors {
			errorList = append(errorList, err)
		}

		if len(errorList) > 0 {
			t.Errorf("Iteration %d: %d errors occurred: %v",
				iter, len(errorList), errorList)
		}
	}
}

// TestExecStderrRaceCondition tests stderr output from fast commands
func TestExecStderrRaceCondition(t *testing.T) {
	// Skip if not in integration test mode
	if os.Getenv("FLY_APP_NAME") == "" || os.Getenv("SPRITE_TOKEN") == "" {
		t.Skip("Skipping integration test: FLY_APP_NAME and SPRITE_TOKEN must be set")
	}

	spritePath := filepath.Join("..", "dist", "sprite")
	if _, err := os.Stat(spritePath); os.IsNotExist(err) {
		t.Skip("Sprite client not built")
	}

	testCases := []struct {
		name         string
		args         []string
		expectStderr bool
	}{
		{
			name:         "stderr only",
			args:         []string{"sh", "-c", "echo 'error' >&2"},
			expectStderr: true,
		},
		{
			name:         "both streams",
			args:         []string{"sh", "-c", "echo 'out'; echo 'err' >&2"},
			expectStderr: true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			for i := 0; i < 20; i++ {
				args := append([]string{"exec"}, tc.args...)
				cmd := exec.Command(spritePath, args...)

				output, err := cmd.CombinedOutput()
				if err != nil {
					t.Errorf("Iteration %d: Command failed: %v", i, err)
					continue
				}

				outputStr := string(output)

				// For stderr test, we expect to see "error" or "err" in output
				if tc.expectStderr && !strings.Contains(outputStr, "err") {
					t.Errorf("Iteration %d: No stderr output found in: %q", i, outputStr)
				}

				// For both streams, check we got stdout too
				if tc.name == "both streams" && !strings.Contains(outputStr, "out") {
					t.Errorf("Iteration %d: No stdout output found in: %q", i, outputStr)
				}
			}
		})
	}
}

// TestExecTiming measures timing to detect potential delays
func TestExecTiming(t *testing.T) {
	// Skip if not in integration test mode
	if os.Getenv("FLY_APP_NAME") == "" || os.Getenv("SPRITE_TOKEN") == "" {
		t.Skip("Skipping integration test: FLY_APP_NAME and SPRITE_TOKEN must be set")
	}

	spritePath := filepath.Join("..", "dist", "sprite")
	if _, err := os.Stat(spritePath); os.IsNotExist(err) {
		t.Skip("Sprite client not built")
	}

	// Test a very fast command
	start := time.Now()
	cmd := exec.Command(spritePath, "exec", "echo", "test")
	output, err := cmd.CombinedOutput()
	duration := time.Since(start)

	if err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	if string(output) != "test\n" {
		t.Errorf("Unexpected output: %q", string(output))
	}

	// The command should complete quickly (allowing for network overhead)
	if duration > 5*time.Second {
		t.Errorf("Command took too long: %v", duration)
	}

	t.Logf("Command completed in %v", duration)
}
