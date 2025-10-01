package api

import (
	"bytes"
	"context"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

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
					errors <- fmt.Sprintf("output mismatch: got %q, expected %q (len=%d)", stdout.String(), expected, len(stdout.String()))
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
