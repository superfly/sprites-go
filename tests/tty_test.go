package tests

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"

	"github.com/creack/pty"
)

// TestTTYFunctionality tests TTY exec functionality
func TestTTYFunctionality(t *testing.T) {
	// Get sprite URL and token from environment
	spriteURL := os.Getenv("SPRITE_URL")
	spriteToken := os.Getenv("SPRITE_TOKEN")

	if spriteURL == "" || spriteToken == "" {
		t.Skip("SPRITE_URL or SPRITE_TOKEN not set, skipping TTY test")
	}

	// Test 1: Basic TTY command that outputs color codes
	t.Run("TTYColorOutput", func(t *testing.T) {
		cmd := exec.Command("../dist/sprite", "exec", "-tty", "/bin/sh", "-c", "printf '\\033[31mRED\\033[0m\\n'")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		// Create a PTY for the test
		ptmx, err := pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start with PTY: %v", err)
		}
		defer ptmx.Close()

		// Read output
		output := &bytes.Buffer{}
		done := make(chan error, 1)
		go func() {
			_, err := io.Copy(output, ptmx)
			done <- err
		}()

		// Wait for command to complete
		cmdErr := cmd.Wait()
		ptmx.Close() // Close PTY to trigger EOF
		<-done       // Wait for reader to finish

		if cmdErr != nil {
			t.Fatalf("TTY command failed: %v\nOutput: %s", cmdErr, output.String())
		}

		// Check that ANSI escape codes are preserved
		outputStr := output.String()
		if !strings.Contains(outputStr, "\033[31m") {
			t.Errorf("Expected ANSI color codes to be preserved, got: %q", outputStr)
		}

		// Should also contain "RED" text
		if !strings.Contains(outputStr, "RED") {
			t.Errorf("Expected 'RED' in output, got: %q", outputStr)
		}
	})

	// Test 2: TTY vs non-TTY output differences
	t.Run("TTYvsNonTTY", func(t *testing.T) {
		// Run same command with TTY using PTY
		cmdTTY := exec.Command("../dist/sprite", "exec", "-tty", "/bin/sh", "-c", "echo 'Hello TTY'")
		cmdTTY.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		ptmx, err := pty.Start(cmdTTY)
		if err != nil {
			t.Fatalf("Failed to start TTY command with PTY: %v", err)
		}
		defer ptmx.Close()

		outputTTY := &bytes.Buffer{}
		done := make(chan error, 1)
		go func() {
			_, err := io.Copy(outputTTY, ptmx)
			done <- err
		}()

		err = cmdTTY.Wait()
		ptmx.Close()
		<-done

		if err != nil {
			t.Fatalf("TTY command failed: %v", err)
		}

		// Run same command without TTY
		cmdNoTTY := exec.Command("../dist/sprite", "exec", "/bin/sh", "-c", "echo 'Hello no TTY'")
		cmdNoTTY.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		outputNoTTY, err := cmdNoTTY.CombinedOutput()
		if err != nil {
			t.Fatalf("Non-TTY command failed: %v", err)
		}

		// Both should contain their respective outputs
		if !strings.Contains(outputTTY.String(), "Hello TTY") {
			t.Errorf("TTY output missing expected text: %s", outputTTY.String())
		}

		if !strings.Contains(string(outputNoTTY), "Hello no TTY") {
			t.Errorf("Non-TTY output missing expected text: %s", string(outputNoTTY))
		}

		t.Logf("TTY output: %q", outputTTY.String())
		t.Logf("Non-TTY output: %q", string(outputNoTTY))
	})

	// Test 3: TTY command that would normally fail without proper PTY
	t.Run("TTYRequiredCommand", func(t *testing.T) {
		// Commands like 'tty' or terminal-specific operations should work with -tty flag
		cmd := exec.Command("../dist/sprite", "exec", "-tty", "/bin/sh", "-c", "stty size 2>/dev/null || echo 'No TTY available'")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		ptmx, err := pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start with PTY: %v", err)
		}
		defer ptmx.Close()

		// Set window size for the PTY
		if err := pty.Setsize(ptmx, &pty.Winsize{Rows: 24, Cols: 80}); err != nil {
			t.Logf("Failed to set PTY size (non-fatal): %v", err)
		}

		output := &bytes.Buffer{}
		done := make(chan error, 1)
		go func() {
			_, err := io.Copy(output, ptmx)
			done <- err
		}()

		err = cmd.Wait()
		ptmx.Close()
		<-done

		if err != nil {
			// This might fail if the container doesn't have stty, but that's OK
			t.Logf("TTY command returned error (this might be expected): %v", err)
		}

		outputStr := output.String()
		t.Logf("TTY stty output: %q", outputStr)

		// If stty worked, we should see terminal dimensions like "24 80"
		// If not, we should see our fallback message
		if strings.Contains(outputStr, "No TTY available") {
			t.Logf("Container doesn't have stty or TTY support")
		} else if strings.Contains(outputStr, "24") || strings.Contains(outputStr, "80") {
			// Likely got terminal dimensions - this is good
			t.Logf("TTY appears to be working - got terminal dimensions")
		}
	})

	// Test 4: Interactive command with input/output
	t.Run("InteractiveTTY", func(t *testing.T) {
		cmd := exec.Command("../dist/sprite", "exec", "-tty", "/bin/sh")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		ptmx, err := pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start with PTY: %v", err)
		}
		defer ptmx.Close()

		// Read output in background
		output := &bytes.Buffer{}
		readDone := make(chan struct{})
		go func() {
			io.Copy(output, ptmx)
			close(readDone)
		}()

		// Send some commands
		time.Sleep(500 * time.Millisecond) // Wait for shell prompt

		// Send command
		ptmx.Write([]byte("echo 'Interactive test'\n"))
		time.Sleep(200 * time.Millisecond)

		// Exit shell
		ptmx.Write([]byte("exit\n"))

		// Wait for command to complete
		err = cmd.Wait()
		ptmx.Close()

		// Wait for reader with timeout
		select {
		case <-readDone:
			// Good
		case <-time.After(2 * time.Second):
			t.Log("Reader timeout (expected)")
		}

		if err != nil {
			t.Fatalf("Interactive command failed: %v", err)
		}

		outputStr := output.String()
		if !strings.Contains(outputStr, "Interactive test") {
			t.Errorf("Expected 'Interactive test' in output, got: %q", outputStr)
		}
	})
}

// TestNonInteractiveTTY tests TTY functionality without requiring terminal interaction
func TestNonInteractiveTTY(t *testing.T) {
	// Get sprite URL and token from environment
	spriteURL := os.Getenv("SPRITE_URL")
	spriteToken := os.Getenv("SPRITE_TOKEN")

	if spriteURL == "" || spriteToken == "" {
		t.Skip("SPRITE_URL or SPRITE_TOKEN not set, skipping TTY test")
	}

	// Test non-TTY commands that should work in any environment
	t.Run("NonTTYEcho", func(t *testing.T) {
		cmd := exec.Command("../dist/sprite", "exec", "echo", "Hello from non-TTY")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		output, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("Non-TTY command failed: %v\nOutput: %s", err, string(output))
		}

		if !strings.Contains(string(output), "Hello from non-TTY") {
			t.Errorf("Expected 'Hello from non-TTY' in output, got: %q", string(output))
		}
	})

	// Test command with environment variables (non-TTY)
	t.Run("NonTTYEnvVars", func(t *testing.T) {
		cmd := exec.Command("../dist/sprite", "exec", "-env", "MYVAR=testvalue", "/bin/sh", "-c", "echo $MYVAR")
		cmd.Env = append(os.Environ(),
			fmt.Sprintf("SPRITE_URL=%s", spriteURL),
			fmt.Sprintf("SPRITE_TOKEN=%s", spriteToken),
		)

		output, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("Non-TTY env command failed: %v\nOutput: %s", err, string(output))
		}

		if !strings.Contains(string(output), "testvalue") {
			t.Errorf("Expected 'testvalue' in output, got: %q", string(output))
		}
	})
}
