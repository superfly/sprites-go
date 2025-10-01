package api

import (
	"bytes"
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

// TestExecVeryLargeOutput tests commands that produce very large output quickly
// This specifically targets potential buffer overflow and race conditions
func TestExecVeryLargeOutput(t *testing.T) {
	testCases := []struct {
		name        string
		command     []string
		minSize     int // minimum expected output size
		description string
	}{
		{
			name: "10MB_stdout_fast",
			// Generate 10MB of data as fast as possible
			command:     []string{"sh", "-c", "dd if=/dev/zero bs=1048576 count=10 2>/dev/null | base64"},
			minSize:     10 * 1024 * 1024, // base64 encoding will make it larger
			description: "10MB of stdout data from fast command",
		},
		{
			name: "10MB_stderr_fast",
			// Generate 10MB to stderr
			command:     []string{"sh", "-c", "dd if=/dev/zero bs=1048576 count=10 | base64 >&2"},
			minSize:     10 * 1024 * 1024,
			description: "10MB of stderr data from fast command",
		},
		{
			name: "burst_output",
			// Generate data that will definitely overflow the 100-item writeChan buffer
			command:     []string{"sh", "-c", "for i in $(seq 1 200); do echo \"Line $i with some padding to make it longer: $(seq 1 20)\"; done"},
			minSize:     1000, // Just check we got something
			description: "Burst of 200 lines to overflow write buffer",
		},
		{
			name: "continuous_stream",
			// Continuous output that should fill buffers
			command:     []string{"sh", "-c", "yes 'This is a line of output that will be repeated many times' | head -n 10000"},
			minSize:     100000,
			description: "10000 lines of continuous output",
		},
		{
			name: "mixed_large_output",
			// Both stdout and stderr with large output
			command: []string{"sh", "-c", `
				for i in $(seq 1 5000); do 
					echo "stdout line $i"
					echo "stderr line $i" >&2
				done
			`},
			minSize:     50000,
			description: "5000 lines each to stdout and stderr",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Run test multiple times to catch race conditions
			for iteration := 0; iteration < 3; iteration++ {
				t.Logf("Iteration %d: %s", iteration, tc.description)
				
				session := terminal.NewSession(
					terminal.WithCommand(tc.command[0], tc.command[1:]...),
					terminal.WithTTY(false),
				)

				ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				defer cancel()

				stdin := strings.NewReader("")
				stdout := &bytes.Buffer{}
				stderr := &bytes.Buffer{}

				start := time.Now()
				exitCode, err := session.Run(ctx, stdin, stdout, stderr)
				duration := time.Since(start)

				if err != nil {
					t.Fatalf("session.Run error: %v", err)
				}

				if exitCode != 0 {
					t.Errorf("non-zero exit code: %d", exitCode)
				}

				totalOutput := stdout.Len() + stderr.Len()
				if totalOutput < tc.minSize {
					t.Errorf("output too small: expected at least %d bytes, got %d (stdout=%d, stderr=%d)",
						tc.minSize, totalOutput, stdout.Len(), stderr.Len())
				}

				throughput := float64(totalOutput) / duration.Seconds() / 1024 / 1024
				t.Logf("Completed in %v, output=%d bytes, throughput=%.2f MB/s", 
					duration, totalOutput, throughput)

				// For mixed output test, verify both streams have data
				if strings.Contains(tc.name, "mixed") {
					if stdout.Len() == 0 {
						t.Error("expected stdout data but got none")
					}
					if stderr.Len() == 0 {
						t.Error("expected stderr data but got none")
					}
				}
			}
		})
	}
}

// TestExecBufferStress tests the WebSocket write buffer under stress
func TestExecBufferStress(t *testing.T) {
	// This test specifically targets the 100-item writeChan buffer
	// by generating output faster than it can be written to the WebSocket
	
	session := terminal.NewSession(
		terminal.WithCommand("sh", "-c", `
			# Generate 500 chunks of data rapidly
			for i in $(seq 1 500); do
				# Each echo creates a separate write to the channel
				echo "CHUNK_START_$i"
				# Generate 1KB of data per chunk
				dd if=/dev/zero bs=1024 count=1 2>/dev/null | base64
				echo "CHUNK_END_$i"
			done
		`),
		terminal.WithTTY(false),
	)

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	stdin := strings.NewReader("")
	stdout := &bytes.Buffer{}
	stderr := &bytes.Buffer{}

	start := time.Now()
	exitCode, err := session.Run(ctx, stdin, stdout, stderr)
	duration := time.Since(start)

	if err != nil {
		t.Fatalf("session.Run error: %v", err)
	}

	if exitCode != 0 {
		t.Errorf("non-zero exit code: %d", exitCode)
	}

	// Verify we got all chunks
	output := stdout.String()
	startCount := strings.Count(output, "CHUNK_START_")
	endCount := strings.Count(output, "CHUNK_END_")
	
	if startCount != 500 {
		t.Errorf("expected 500 chunk starts, got %d", startCount)
	}
	if endCount != 500 {
		t.Errorf("expected 500 chunk ends, got %d", endCount)
	}

	t.Logf("Buffer stress test completed in %v, verified %d chunks", duration, startCount)
}

// TestExecRapidExitLargeData tests commands that produce large output and exit immediately
func TestExecRapidExitLargeData(t *testing.T) {
	// These commands produce output and exit as fast as possible
	testCases := []struct {
		name    string
		command []string
		check   func(stdout, stderr *bytes.Buffer) error
	}{
		{
			name: "printf_large_string",
			command: []string{"sh", "-c", `printf '%s' "$(dd if=/dev/zero bs=1048576 count=5 2>/dev/null | base64)"`},
			check: func(stdout, stderr *bytes.Buffer) error {
				// Should be at least 5MB after base64 encoding
				if stdout.Len() < 5*1024*1024 {
					return fmt.Errorf("expected at least 5MB, got %d bytes", stdout.Len())
				}
				return nil
			},
		},
		{
			name: "cat_large_data",
			command: []string{"sh", "-c", `dd if=/dev/zero bs=1048576 count=8 2>/dev/null | cat`},
			check: func(stdout, stderr *bytes.Buffer) error {
				if stdout.Len() != 8*1024*1024 {
					return fmt.Errorf("expected exactly 8MB, got %d bytes", stdout.Len())
				}
				return nil
			},
		},
		{
			name: "echo_loop_no_delay",
			command: []string{"sh", "-c", `for i in $(seq 1 10000); do echo "$i"; done`},
			check: func(stdout, stderr *bytes.Buffer) error {
				lines := strings.Split(strings.TrimSpace(stdout.String()), "\n")
				if len(lines) != 10000 {
					return fmt.Errorf("expected 10000 lines, got %d", len(lines))
				}
				// Verify first and last lines
				if lines[0] != "1" {
					return fmt.Errorf("first line should be '1', got %q", lines[0])
				}
				if lines[9999] != "10000" {
					return fmt.Errorf("last line should be '10000', got %q", lines[9999])
				}
				return nil
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Run multiple times to catch race conditions
			for i := 0; i < 5; i++ {
				session := terminal.NewSession(
					terminal.WithCommand(tc.command[0], tc.command[1:]...),
					terminal.WithTTY(false),
				)

				ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				defer cancel()

				stdin := strings.NewReader("")
				stdout := &bytes.Buffer{}
				stderr := &bytes.Buffer{}

				start := time.Now()
				exitCode, err := session.Run(ctx, stdin, stdout, stderr)
				duration := time.Since(start)

				if err != nil {
					t.Fatalf("iteration %d: session.Run error: %v", i, err)
				}

				if exitCode != 0 {
					t.Errorf("iteration %d: non-zero exit code: %d", i, exitCode)
				}

				if err := tc.check(stdout, stderr); err != nil {
					t.Errorf("iteration %d: check failed: %v", i, err)
				}

				t.Logf("iteration %d: completed in %v", i, duration)
			}
		})
	}
} 