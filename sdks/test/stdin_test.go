package main

import (
	"testing"
	"time"
)

func TestStdin(t *testing.T) {
	spriteName := sharedSpriteName
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	// Test stdin with cat command - we'll use echo to pipe input
	output, err := runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "sh", "-c", "echo 'stdin-test-input' | cat")
	if err != nil {
		t.Fatalf("Stdin test failed: %v", err)
	}
	if output != "stdin-test-input\n" {
		t.Fatalf("Stdin test failed: expected 'stdin-test-input\\n', got '%s'", output)
	}

	// Test stdin with multiple lines
	output, err = runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "sh", "-c", "printf 'line1\\nline2\\nline3\\n' | cat")
	if err != nil {
		t.Fatalf("Multi-line stdin test failed: %v", err)
	}
	expected := "line1\nline2\nline3\n"
	if output != expected {
		t.Fatalf("Multi-line stdin test failed: expected %q, got %q", expected, output)
	}
}
