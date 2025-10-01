package main

import (
	"strings"
	"testing"
	"time"
)

func TestTTY(t *testing.T) {
	spriteName := sharedSpriteName
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	// Test TTY with echo command
	output, err := runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-tty", "-tty-rows", "24", "-tty-cols", "80", "-output", "stdout", "echo", "tty-test")
	if err != nil {
		t.Fatalf("TTY test failed: %v", err)
	}
	// TTY mode outputs CRLF (\r\n) instead of just LF (\n), so normalize the output
	normalizedOutput := strings.ReplaceAll(output, "\r\n", "\n")
	if normalizedOutput != "tty-test\n" {
		t.Fatalf("TTY test failed: expected 'tty-test\\n', got '%s'", output)
	}

	// Test TTY with tty command to verify TTY is actually allocated
	output, err = runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-tty", "-tty-rows", "24", "-tty-cols", "80", "-output", "stdout", "tty")
	if err != nil {
		t.Fatalf("TTY allocation test failed: %v", err)
	}
	if !strings.Contains(output, "/dev/pts/") {
		t.Fatalf("TTY allocation test failed: expected TTY path, got %q", output)
	}
}
