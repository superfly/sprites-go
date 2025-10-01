package main

import (
	"testing"
	"time"
)

func TestNoHanging(t *testing.T) {
	spriteName := sharedSpriteName
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	// Test normal command doesn't hang
	output, err := runTestCli(testCliPath, baseURL, spriteName, 5*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "echo", "no-hang-test")
	if err != nil {
		t.Fatalf("No hang test failed: %v", err)
	}
	if output != "no-hang-test\n" {
		t.Fatalf("No hang test failed: expected 'no-hang-test\\n', got '%s'", output)
	}

	// Test that long-running command times out properly
	_, err = runTestCli(testCliPath, baseURL, spriteName, 2*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "sleep", "10")
	if err == nil {
		t.Fatalf("No hang test failed: expected timeout error, got nil")
	}
}
