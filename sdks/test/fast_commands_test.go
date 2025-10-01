package main

import (
	"fmt"
	"testing"
	"time"
)

func TestFastCommands(t *testing.T) {
	spriteName := sharedSpriteName
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	// Test very fast command
	output, err := runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
		"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "echo", "fast-command-output")
	if err != nil {
		t.Fatalf("Fast command test failed: %v", err)
	}
	if output != "fast-command-output\n" {
		t.Fatalf("Fast command test failed: expected 'fast-command-output\\n', got '%s'", output)
	}

	// Test multiple fast commands
	for i := 0; i < 5; i++ {
		output, err = runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
			"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "echo", fmt.Sprintf("fast-command-%d", i))
		if err != nil {
			t.Fatalf("Fast command %d test failed: %v", i, err)
		}
		expected := fmt.Sprintf("fast-command-%d\n", i)
		if output != expected {
			t.Fatalf("Fast command %d test failed: expected %q, got %q", i, expected, output)
		}
	}
}
