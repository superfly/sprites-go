package main

import (
	"testing"
	"time"
)

func TestStdoutStreaming(t *testing.T) {
	spriteName := sharedSpriteName
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	// Test stdout streaming
	output, err := runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "echo", "Hello from stdout")
	if err != nil {
		t.Fatalf("Stdout test failed: %v", err)
	}
	if output != "Hello from stdout\n" {
		t.Fatalf("Stdout test failed: expected 'Hello from stdout\\n', got '%s'", output)
	}

	// Test stderr streaming
	output, err = runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "combined", "sh", "-c", "echo 'Hello from stderr' >&2")
	if err != nil {
		t.Fatalf("Stderr test failed: %v", err)
	}
	if output != "Hello from stderr\n" {
		t.Fatalf("Stderr test failed: expected 'Hello from stderr\\n', got '%s'", output)
	}
}
