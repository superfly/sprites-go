package handlers

import (
	"bytes"
	"context"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

// TestExecRaceCondition tests the race condition with short commands that exit immediately
// This test runs commands directly through the terminal package to ensure proper flushing
func TestExecRaceCondition(t *testing.T) {
	testCases := []struct {
		name        string
		command     []string
		expectedOut string
		expectedErr string
		iterations  int
	}{
		{
			name:        "simple echo",
			command:     []string{"echo", "hello world"},
			expectedOut: "hello world\n",
			expectedErr: "",
			iterations:  50,
		},
		{
			name:        "pwd command",
			command:     []string{"pwd"},
			expectedOut: "/", // Will contain something
			expectedErr: "",
			iterations:  50,
		},
		{
			name:        "printf with immediate output",
			command:     []string{"sh", "-c", "printf 'small output\\n'"},
			expectedOut: "small output\n",
			expectedErr: "",
			iterations:  50,
		},
		{
			name:        "echo without newline",
			command:     []string{"sh", "-c", "printf 'hello'"},
			expectedOut: "hello",
			expectedErr: "",
			iterations:  50,
		},
		{
			name:        "ultra short output",
			command:     []string{"sh", "-c", "printf 'x'"},
			expectedOut: "x",
			expectedErr: "",
			iterations:  50,
		},
		{
			name:        "stderr only fast exit",
			command:     []string{"sh", "-c", "echo 'error' >&2"},
			expectedOut: "",
			expectedErr: "error\n",
			iterations:  50,
		},
		{
			name:        "both streams fast exit",
			command:     []string{"sh", "-c", "echo 'out'; echo 'err' >&2"},
			expectedOut: "out\n",
			expectedErr: "err\n",
			iterations:  50,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			successCount := 0
			var failures []string

			for i := 0; i < tc.iterations; i++ {
				// Create session with non-TTY mode to test separate streams
				session := terminal.NewSession(
					terminal.WithCommand(tc.command[0], tc.command[1:]...),
					terminal.WithTTY(false),
				)

				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
				defer cancel()

				stdin := strings.NewReader("")
				stdout := &bytes.Buffer{}
				stderr := &bytes.Buffer{}

				exitCode, err := session.Run(ctx, stdin, stdout, stderr)
				if err != nil {
					failures = append(failures, "session.Run error: "+err.Error())
					continue
				}

				if exitCode != 0 {
					failures = append(failures, "non-zero exit code")
					continue
				}

				gotStdout := stdout.String()
				gotStderr := stderr.String()

				// For pwd, just check we got something
				if tc.command[0] == "pwd" {
					if gotStdout == "" {
						failures = append(failures, "no pwd output")
						continue
					}
				} else {
					if gotStdout != tc.expectedOut {
						failures = append(failures, "stdout mismatch: "+gotStdout)
						continue
					}
				}

				if gotStderr != tc.expectedErr {
					failures = append(failures, "stderr mismatch: "+gotStderr)
					continue
				}

				successCount++
			}

			// Require 100% success rate - no race conditions allowed
			if successCount != tc.iterations {
				t.Errorf("Race condition detected: only %d/%d iterations succeeded. Failures: %v",
					successCount, tc.iterations, failures)
			}
		})
	}
}

// TestExecConcurrentCommands tests running many commands concurrently
func TestExecConcurrentCommands(t *testing.T) {
	concurrency := 20
	iterations := 5

	for iter := 0; iter < iterations; iter++ {
		var wg sync.WaitGroup
		errors := make(chan string, concurrency)

		for i := 0; i < concurrency; i++ {
			wg.Add(1)
			go func(id int) {
				defer wg.Done()

				// Each goroutine runs a unique command
				cmd := []string{"sh", "-c", "echo 'worker " + string(rune('0'+id%10)) + "'"}
				expected := "worker " + string(rune('0'+id%10)) + "\n"

				session := terminal.NewSession(
					terminal.WithCommand(cmd[0], cmd[1:]...),
					terminal.WithTTY(false),
				)

				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
				defer cancel()

				stdin := strings.NewReader("")
				stdout := &bytes.Buffer{}
				stderr := &bytes.Buffer{}

				exitCode, err := session.Run(ctx, stdin, stdout, stderr)
				if err != nil {
					errors <- "session error: " + err.Error()
					return
				}

				if exitCode != 0 {
					errors <- "non-zero exit code"
					return
				}

				if stdout.String() != expected {
					errors <- "output mismatch: got " + stdout.String()
					return
				}

				if stderr.String() != "" {
					errors <- "unexpected stderr: " + stderr.String()
					return
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
			t.Errorf("Iteration %d: Concurrent test failed with %d errors: %v",
				iter, len(errorList), errorList)
		}
	}
}

// TestExecBufferBoundaries tests commands that produce output at buffer boundaries
func TestExecBufferBoundaries(t *testing.T) {
	// Test various sizes around common buffer boundaries
	sizes := []int{
		1,    // Single byte
		63,   // Just under 64
		64,   // Common buffer size
		65,   // Just over 64
		1023, // Just under 1024
		1024, // Common buffer size
		1025, // Just over 1024
		4095, // Just under 4096
		4096, // Page size
		4097, // Just over page size
	}

	for _, size := range sizes {
		t.Run("size_"+string(rune(size)), func(t *testing.T) {
			// Generate string of exact size
			data := strings.Repeat("A", size)
			cmd := []string{"sh", "-c", "printf '" + data + "'"}

			session := terminal.NewSession(
				terminal.WithCommand(cmd[0], cmd[1:]...),
				terminal.WithTTY(false),
			)

			ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
			defer cancel()

			stdin := strings.NewReader("")
			stdout := &bytes.Buffer{}
			stderr := &bytes.Buffer{}

			exitCode, err := session.Run(ctx, stdin, stdout, stderr)
			if err != nil {
				t.Fatalf("session error: %v", err)
			}

			if exitCode != 0 {
				t.Errorf("non-zero exit code: %d", exitCode)
			}

			if stdout.String() != data {
				t.Errorf("output size mismatch: expected %d bytes, got %d",
					size, len(stdout.String()))
			}

			if stderr.String() != "" {
				t.Errorf("unexpected stderr: %q", stderr.String())
			}
		})
	}
}

// TestExecRapidFire tests many small commands in quick succession
func TestExecRapidFire(t *testing.T) {
	count := 100

	start := time.Now()
	successCount := 0

	for i := 0; i < count; i++ {
		session := terminal.NewSession(
			terminal.WithCommand("echo", "test"),
			terminal.WithTTY(false),
		)

		ctx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
		stdin := strings.NewReader("")
		stdout := &bytes.Buffer{}
		stderr := &bytes.Buffer{}

		exitCode, err := session.Run(ctx, stdin, stdout, stderr)
		cancel()

		if err == nil && exitCode == 0 && stdout.String() == "test\n" && stderr.String() == "" {
			successCount++
		}
	}

	elapsed := time.Since(start)

	if successCount != count {
		t.Errorf("Only %d/%d commands succeeded", successCount, count)
	}

	t.Logf("Executed %d commands in %v (%.2f/sec)", count, elapsed, float64(count)/elapsed.Seconds())
}
