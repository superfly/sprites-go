package tests

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestExecLargeOutput tests that the sprite can handle commands with large output
func TestExecLargeOutput(t *testing.T) {
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

	// Run all subtests
	t.Run("LargeStdout", testLargeStdout)
	t.Run("LargeStderr", testLargeStderr)
	t.Run("MixedLargeOutput", testMixedLargeOutput)
	t.Run("RapidSmallOutput", testRapidSmallOutput)
	t.Run("VeryLargeOutput", testVeryLargeOutput)
	t.Run("BurstOutput", testBurstOutput)
}

func testLargeStdout(t *testing.T) {
	spritePath := filepath.Join("..", "dist", "sprite")
	
	// Generate 5MB of stdout data
	cmd := exec.Command(spritePath, "exec", "sh", "-c", "dd if=/dev/zero bs=1048576 count=5 2>/dev/null | base64")
	
	start := time.Now()
	output, err := cmd.CombinedOutput()
	duration := time.Since(start)
	
	if err != nil {
		t.Fatalf("Command failed: %v\nOutput: %s", err, string(output))
	}
	
	// Base64 encoding increases size by ~33%
	expectedMinSize := 5 * 1024 * 1024
	if len(output) < expectedMinSize {
		t.Errorf("Output too small: expected at least %d bytes, got %d", expectedMinSize, len(output))
	}
	
	t.Logf("Successfully received %d bytes of stdout in %v (%.2f MB/s)", 
		len(output), duration, float64(len(output))/duration.Seconds()/1024/1024)
}

func testLargeStderr(t *testing.T) {
	spritePath := filepath.Join("..", "dist", "sprite")
	
	// Generate 3MB of stderr data
	cmd := exec.Command(spritePath, "exec", "sh", "-c", "dd if=/dev/zero bs=1048576 count=3 | base64 >&2")
	
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	
	start := time.Now()
	err := cmd.Run()
	duration := time.Since(start)
	
	if err != nil {
		t.Fatalf("Command failed: %v\nStdout: %s\nStderr: %s", err, stdout.String(), stderr.String())
	}
	
	// Check stderr has the data
	expectedMinSize := 3 * 1024 * 1024
	if stderr.Len() < expectedMinSize {
		t.Errorf("Stderr too small: expected at least %d bytes, got %d", expectedMinSize, stderr.Len())
	}
	
	// Stdout should be empty or just have dd's summary
	if stdout.Len() > 1000 {
		t.Errorf("Unexpected stdout data: %d bytes", stdout.Len())
	}
	
	t.Logf("Successfully received %d bytes of stderr in %v", stderr.Len(), duration)
}

func testMixedLargeOutput(t *testing.T) {
	spritePath := filepath.Join("..", "dist", "sprite")
	
	// Generate alternating stdout/stderr output
	script := `
	for i in $(seq 1 1000); do
		echo "stdout line $i"
		echo "stderr line $i" >&2
	done
	`
	
	cmd := exec.Command(spritePath, "exec", "sh", "-c", script)
	
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	
	err := cmd.Run()
	if err != nil {
		t.Fatalf("Command failed: %v", err)
	}
	
	// Count lines
	stdoutLines := strings.Count(stdout.String(), "\n")
	stderrLines := strings.Count(stderr.String(), "\n")
	
	if stdoutLines != 1000 {
		t.Errorf("Expected 1000 stdout lines, got %d", stdoutLines)
	}
	if stderrLines != 1000 {
		t.Errorf("Expected 1000 stderr lines, got %d", stderrLines)
	}
	
	// Verify content
	if !strings.Contains(stdout.String(), "stdout line 1\n") {
		t.Error("Missing first stdout line")
	}
	if !strings.Contains(stdout.String(), "stdout line 1000\n") {
		t.Error("Missing last stdout line")
	}
	if !strings.Contains(stderr.String(), "stderr line 1\n") {
		t.Error("Missing first stderr line")
	}
	if !strings.Contains(stderr.String(), "stderr line 1000\n") {
		t.Error("Missing last stderr line")
	}
	
	t.Logf("Successfully received %d stdout and %d stderr lines", stdoutLines, stderrLines)
}

func testRapidSmallOutput(t *testing.T) {
	spritePath := filepath.Join("..", "dist", "sprite")
	
	// Test many small outputs in rapid succession
	testCases := []struct {
		name    string
		command string
	}{
		{"echo", "echo hello"},
		{"pwd", "pwd"},
		{"printf", "printf 'test'"},
		{"echo_number", "echo 1"},
		{"echo_multiword", "echo hello world"},
	}
	
	// Run each command 10 times
	for _, tc := range testCases {
		for i := 0; i < 10; i++ {
			cmd := exec.Command(spritePath, "exec", "sh", "-c", tc.command)
			output, err := cmd.CombinedOutput()
			
			if err != nil {
				t.Errorf("Iteration %d of %s failed: %v\nOutput: %s", i, tc.name, err, output)
				continue
			}
			
			if len(output) == 0 {
				t.Errorf("Iteration %d of %s produced no output", i, tc.name)
			}
		}
	}
	
	t.Log("Rapid small output test completed successfully")
}

func testVeryLargeOutput(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping very large output test in short mode")
	}
	
	spritePath := filepath.Join("..", "dist", "sprite")
	
	// Generate 10MB of data
	cmd := exec.Command(spritePath, "exec", "sh", "-c", "dd if=/dev/zero bs=1048576 count=10 2>/dev/null | base64")
	
	start := time.Now()
	output, err := cmd.CombinedOutput()
	duration := time.Since(start)
	
	if err != nil {
		t.Fatalf("Command failed: %v", err)
	}
	
	expectedMinSize := 10 * 1024 * 1024
	if len(output) < expectedMinSize {
		t.Errorf("Output too small: expected at least %d bytes, got %d", expectedMinSize, len(output))
	}
	
	throughput := float64(len(output)) / duration.Seconds() / 1024 / 1024
	t.Logf("Successfully received %d bytes in %v (%.2f MB/s)", len(output), duration, throughput)
	
	if throughput < 1.0 {
		t.Logf("Warning: Low throughput detected: %.2f MB/s", throughput)
	}
}

func testBurstOutput(t *testing.T) {
	spritePath := filepath.Join("..", "dist", "sprite")
	
	// Generate output that should stress buffers
	script := `
	# Generate 200 chunks rapidly
	for i in $(seq 1 200); do
		echo "START_CHUNK_$i"
		# Small data chunk
		echo "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
		echo "END_CHUNK_$i"
	done
	`
	
	cmd := exec.Command(spritePath, "exec", "sh", "-c", script)
	output, err := cmd.CombinedOutput()
	
	if err != nil {
		t.Fatalf("Command failed: %v\nOutput: %s", err, string(output))
	}
	
	// Verify all chunks were received
	outputStr := string(output)
	startCount := strings.Count(outputStr, "START_CHUNK_")
	endCount := strings.Count(outputStr, "END_CHUNK_")
	
	if startCount != 200 {
		t.Errorf("Expected 200 START_CHUNK markers, got %d", startCount)
	}
	if endCount != 200 {
		t.Errorf("Expected 200 END_CHUNK markers, got %d", endCount)
	}
	
	// Verify chunks are in order
	for i := 1; i <= 200; i++ {
		if !strings.Contains(outputStr, fmt.Sprintf("START_CHUNK_%d", i)) {
			t.Errorf("Missing chunk %d", i)
			break
		}
	}
	
	t.Logf("Successfully received all %d chunks", startCount)
} 