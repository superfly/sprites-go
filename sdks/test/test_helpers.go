package main

import (
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

// getTestSpriteName generates a unique sprite name for testing
func getTestSpriteName(t *testing.T) string {
	// Use timestamp and random number to ensure uniqueness
	timestamp := time.Now().Unix()
	random := rand.Intn(10000)
	return fmt.Sprintf("test-sprite-%d-%d", timestamp, random)
}

// getTestSpriteNameForSetup generates a unique sprite name for testing (without *testing.T)
func getTestSpriteNameForSetup() string {
	// Use timestamp and random number to ensure uniqueness
	timestamp := time.Now().Unix()
	random := rand.Intn(10000)
	return fmt.Sprintf("test-sprite-%d-%d", timestamp, random)
}

// getBaseURL returns the base URL for the sprite API
func getBaseURL() string {
	if baseURL := os.Getenv("SPRITES_BASE_URL"); baseURL != "" {
		return baseURL
	}
	return "https://api.sprites.dev"
}

// getTestCliPath locates the SDK test command binary
func getTestCliPath(t *testing.T) string {
	// First check if SDK_TEST_COMMAND environment variable is set
	if sdkTestCommand := os.Getenv("SDK_TEST_COMMAND"); sdkTestCommand != "" {
		if _, err := os.Stat(sdkTestCommand); err == nil {
			return sdkTestCommand
		}
		t.Fatalf("SDK_TEST_COMMAND binary not found at: %s", sdkTestCommand)
	}

	// Fallback to finding test-cli binary in various locations
	// First try to find it in the same directory as this binary
	execPath, err := os.Executable()
	if err != nil {
		t.Fatalf("Failed to get executable path: %v", err)
	}

	execDir := filepath.Dir(execPath)

	// Try in the test-cli subdirectory (if built locally)
	testCliPath := filepath.Join(execDir, "test-cli", "test-cli")
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	// Try in the current working directory
	testCliPath = "test-cli/test-cli"
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	// Try in the sdks/go/test-cli directory (relative to project root)
	testCliPath = "../../go/test-cli/test-cli"
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	// Try absolute path from project root
	testCliPath = "sdks/go/test-cli/test-cli"
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	t.Fatalf("SDK test command binary not found. Set SDK_TEST_COMMAND environment variable or ensure test-cli binary is available")
	return ""
}

// getTestCliPathForSetup locates the SDK test command binary (without *testing.T)
func getTestCliPathForSetup() string {
	// First check if SDK_TEST_COMMAND environment variable is set
	if sdkTestCommand := os.Getenv("SDK_TEST_COMMAND"); sdkTestCommand != "" {
		if _, err := os.Stat(sdkTestCommand); err == nil {
			return sdkTestCommand
		}
		panic(fmt.Sprintf("SDK_TEST_COMMAND binary not found at: %s", sdkTestCommand))
	}

	// Fallback to finding test-cli binary in various locations
	execPath, err := os.Executable()
	if err != nil {
		panic(fmt.Sprintf("Failed to get executable path: %v", err))
	}

	execDir := filepath.Dir(execPath)

	// Try in the test-cli subdirectory (if built locally)
	testCliPath := filepath.Join(execDir, "test-cli", "test-cli")
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	// Try in the current working directory
	testCliPath = "test-cli/test-cli"
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	// Try in the sdks/go/test-cli directory (relative to project root)
	testCliPath = "../go/test-cli/test-cli"
	if _, err := os.Stat(testCliPath); err == nil {
		return testCliPath
	}

	panic("SDK test command binary not found. Set SDK_TEST_COMMAND environment variable or ensure test-cli binary is available")
}

// runTestCli executes the test-cli binary with the given arguments
func runTestCli(testCliPath, baseURL, spriteName string, timeout time.Duration, args ...string) (string, error) {
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	cmd := exec.CommandContext(ctx, testCliPath, args...)
	cmd.Env = append(os.Environ(), "SPRITES_TOKEN="+os.Getenv("SPRITES_TEST_TOKEN"))

	output, err := cmd.CombinedOutput()
	return string(output), err
}

// createSprite creates a sprite using the test-cli binary
func createSprite(testCliPath, baseURL, spriteName string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 120*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, testCliPath, "create", spriteName)
	cmd.Env = append(os.Environ(), "SPRITES_TOKEN="+os.Getenv("SPRITES_TEST_TOKEN"))

	output, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("failed to create sprite: %v, output: %s", err, string(output))
	}

	return nil
}

// destroySprite destroys a sprite using the test-cli binary
func destroySprite(testCliPath, baseURL, spriteName string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, testCliPath, "destroy", spriteName)
	cmd.Env = append(os.Environ(), "SPRITES_TOKEN="+os.Getenv("SPRITES_TEST_TOKEN"))

	output, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("failed to destroy sprite: %v, output: %s", err, string(output))
	}

	return nil
}

// warmupSprite runs a simple command to ensure the sprite is fully ready
func warmupSprite(testCliPath, baseURL, spriteName string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, testCliPath, "-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "echo", "warmup")
	cmd.Env = append(os.Environ(), "SPRITES_TOKEN="+os.Getenv("SPRITES_TEST_TOKEN"))

	output, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("warmup command failed: %v, output: %s", err, string(output))
	}

	if string(output) != "warmup\n" {
		return fmt.Errorf("warmup command returned unexpected output: %s", string(output))
	}

	return nil
}

// setupTestSprite creates a sprite for testing and returns a cleanup function
func setupTestSprite(t *testing.T) (string, func()) {
	spriteName := getTestSpriteName(t)
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	// Create sprite
	err := createSprite(testCliPath, baseURL, spriteName)
	if err != nil {
		t.Fatalf("Failed to create test sprite: %v", err)
	}

	// Return cleanup function
	cleanup := func() {
		err := destroySprite(testCliPath, baseURL, spriteName)
		if err != nil {
			t.Logf("Warning: failed to destroy test sprite: %v", err)
		}
	}

	return spriteName, cleanup
}
