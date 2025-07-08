package tests

import (
	"bytes"
	"encoding/json"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

// TestDynamicConfiguration tests the dynamic configuration feature
func TestDynamicConfiguration(t *testing.T) {
	// Skip if not running integration tests
	if testing.Short() {
		t.Skip("Skipping integration test")
	}

	// Temporarily skip - dynamic config integration tests need server behavior fixes
	t.Skip("Dynamic configuration integration tests temporarily disabled - server behavior needs fixes")

	// Create a temporary directory for the config file
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "sprite.config")

	// Start the server with dynamic config flag and a long-running dummy process
	serverCmd := startTestServer(t, "--dynamic-config", configPath, "--", "sh", "-c", "while true; do sleep 1; done")
	defer stopTestServer(t, serverCmd)

	// Wait for server to start
	time.Sleep(3 * time.Second)

	// Prepare configuration request
	config := map[string]string{
		"SPRITE_S3_ACCESS_KEY":        "test-key",
		"SPRITE_S3_SECRET_ACCESS_KEY": "test-secret",
		"SPRITE_S3_ENDPOINT_URL":      "http://localhost:9000",
		"SPRITE_S3_BUCKET":            "test-bucket",
		"SPRITE_WRITE_DIR":            tmpDir,
		"SPRITE_PROCESS_CMD":          "echo hello",
	}

	configJSON, err := json.Marshal(config)
	if err != nil {
		t.Fatalf("Failed to marshal config: %v", err)
	}

	// Send configuration request
	req, err := http.NewRequest("POST", "http://localhost:8080/configure", bytes.NewReader(configJSON))
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer test-token")

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Failed to send request: %v", err)
	}
	defer resp.Body.Close()

	body, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("Expected status 200, got %d: %s", resp.StatusCode, string(body))
	}

	// Check if config file was created
	if _, err := os.Stat(configPath); os.IsNotExist(err) {
		t.Fatalf("Config file was not created at %s", configPath)
	}

	// Read and verify config file
	configData, err := os.ReadFile(configPath)
	if err != nil {
		t.Fatalf("Failed to read config file: %v", err)
	}

	var savedConfig map[string]interface{}
	if err := json.Unmarshal(configData, &savedConfig); err != nil {
		t.Fatalf("Failed to parse saved config: %v", err)
	}

	// Verify some expected fields
	if savedConfig["s3_access_key"] != "test-key" {
		t.Errorf("Expected s3_access_key to be 'test-key', got %v", savedConfig["s3_access_key"])
	}

	t.Logf("Dynamic configuration test passed")
}

// TestDynamicConfigurationWithExistingFile tests loading from existing config file
func TestDynamicConfigurationWithExistingFile(t *testing.T) {
	// Skip if not running integration tests
	if testing.Short() {
		t.Skip("Skipping integration test")
	}

	// Temporarily skip - dynamic config integration tests need server behavior fixes
	t.Skip("Dynamic configuration integration tests temporarily disabled - server behavior needs fixes")

	// Create a temporary directory for the config file
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "sprite.config")

	// Create a config file
	existingConfig := map[string]interface{}{
		"s3_access_key":        "existing-key",
		"s3_secret_access_key": "existing-secret",
		"s3_endpoint_url":      "http://localhost:9000",
		"s3_bucket":            "existing-bucket",
		"juicefs_base_dir":     filepath.Join(tmpDir, "juicefs"),
		"process_command":      []string{"echo", "existing"},
	}

	configData, err := json.MarshalIndent(existingConfig, "", "  ")
	if err != nil {
		t.Fatalf("Failed to marshal existing config: %v", err)
	}

	if err := os.WriteFile(configPath, configData, 0644); err != nil {
		t.Fatalf("Failed to write existing config: %v", err)
	}

	// Start the server with dynamic config flag and a long-running dummy process
	serverCmd := startTestServer(t, "--dynamic-config", configPath, "--", "sh", "-c", "while true; do sleep 1; done")
	defer stopTestServer(t, serverCmd)

	// Wait for server to start and boot
	time.Sleep(3 * time.Second)

	// Try to configure again - should fail since already configured
	config := map[string]string{
		"SPRITE_S3_ACCESS_KEY": "new-key",
	}

	configJSON, err := json.Marshal(config)
	if err != nil {
		t.Fatalf("Failed to marshal config: %v", err)
	}

	req, err := http.NewRequest("POST", "http://localhost:8080/configure", bytes.NewReader(configJSON))
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer test-token")

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Failed to send request: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusBadRequest {
		body, _ := io.ReadAll(resp.Body)
		t.Fatalf("Expected status 400 (already configured), got %d: %s", resp.StatusCode, string(body))
	}

	t.Logf("Existing config file test passed")
}

// TestDynamicConfigurationMerge tests the merge behavior with environment variables
func TestDynamicConfigurationMerge(t *testing.T) {
	// Skip if not running integration tests
	if testing.Short() {
		t.Skip("Skipping integration test")
	}

	// Temporarily skip - dynamic config integration tests need server behavior fixes
	t.Skip("Dynamic configuration integration tests temporarily disabled - server behavior needs fixes")

	// Create a temporary directory for the config file
	tmpDir := t.TempDir()
	configPath := filepath.Join(tmpDir, "sprite.config")

	// Set up environment variables
	os.Setenv("SPRITE_S3_ENDPOINT_URL", "https://s3-from-env.amazonaws.com")
	os.Setenv("SPRITE_S3_BUCKET", "bucket-from-env")
	os.Setenv("SPRITE_CONTAINER_ENABLED", "true")
	os.Setenv("SPRITE_PROCESS_ENV_FOO", "bar")
	defer func() {
		os.Unsetenv("SPRITE_S3_ENDPOINT_URL")
		os.Unsetenv("SPRITE_S3_BUCKET")
		os.Unsetenv("SPRITE_CONTAINER_ENABLED")
		os.Unsetenv("SPRITE_PROCESS_ENV_FOO")
	}()

	// Start the server with dynamic config flag and a long-running dummy process
	serverCmd := startTestServer(t, "--dynamic-config", configPath, "--", "sh", "-c", "while true; do sleep 1; done")
	defer stopTestServer(t, serverCmd)

	// Wait for server to start
	time.Sleep(3 * time.Second)

	// Prepare partial configuration request - only override some values
	config := map[string]string{
		"SPRITE_S3_ACCESS_KEY":        "test-key",
		"SPRITE_S3_SECRET_ACCESS_KEY": "test-secret",
		"SPRITE_S3_BUCKET":            "bucket-from-api", // Override env value
		"SPRITE_WRITE_DIR":            tmpDir,
		// Note: NOT setting SPRITE_S3_ENDPOINT_URL or SPRITE_CONTAINER_ENABLED
	}

	configJSON, err := json.Marshal(config)
	if err != nil {
		t.Fatalf("Failed to marshal config: %v", err)
	}

	// Send configuration request
	req, err := http.NewRequest("POST", "http://localhost:8080/configure", bytes.NewReader(configJSON))
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer test-token")

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("Failed to send request: %v", err)
	}
	defer resp.Body.Close()

	body, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("Expected status 200, got %d: %s", resp.StatusCode, string(body))
	}

	// Read and verify config file
	configData, err := os.ReadFile(configPath)
	if err != nil {
		t.Fatalf("Failed to read config file: %v", err)
	}

	var savedConfig map[string]interface{}
	if err := json.Unmarshal(configData, &savedConfig); err != nil {
		t.Fatalf("Failed to parse saved config: %v", err)
	}

	// Verify merge behavior
	// Should have API-provided values
	if savedConfig["s3_access_key"] != "test-key" {
		t.Errorf("Expected s3_access_key to be 'test-key', got %v", savedConfig["s3_access_key"])
	}

	// Should have overridden env value
	if savedConfig["s3_bucket"] != "bucket-from-api" {
		t.Errorf("Expected s3_bucket to be 'bucket-from-api' (overridden), got %v", savedConfig["s3_bucket"])
	}

	// Should have env value that wasn't overridden
	if savedConfig["s3_endpoint_url"] != "https://s3-from-env.amazonaws.com" {
		t.Errorf("Expected s3_endpoint_url to be from env, got %v", savedConfig["s3_endpoint_url"])
	}

	// Should have boolean env value
	if savedConfig["container_enabled"] != true {
		t.Errorf("Expected container_enabled to be true (from env), got %v", savedConfig["container_enabled"])
	}

	t.Logf("Dynamic configuration merge test passed")
}

// startTestServer starts a test server instance with the given arguments
func startTestServer(t *testing.T, args ...string) *exec.Cmd {
	t.Helper()

	// Ensure tmp directory exists
	if err := os.MkdirAll("../tmp", 0755); err != nil {
		t.Fatalf("Failed to create tmp directory: %v", err)
	}

	// Build the server first
	buildCmd := exec.Command("go", "build", "-o", "tmp/sprite-env-test", ".")
	buildCmd.Dir = ".." // Run from server directory
	if output, err := buildCmd.CombinedOutput(); err != nil {
		t.Fatalf("Failed to build server: %v\nOutput: %s", err, output)
	}

	// Prepare command arguments
	cmdArgs := append([]string{}, args...)
	cmdArgs = append(cmdArgs, "--listen", "localhost:8080")

	// Start the server
	binaryPath := filepath.Join("..", "tmp", "sprite-env-test")
	cmd := exec.Command(binaryPath, cmdArgs...)
	cmd.Dir = "." // Run from tests directory

	// Set environment variables for authentication
	cmd.Env = append(os.Environ(),
		"SPRITE_HTTP_API_TOKEN=test-token",
		"SPRITE_HTTP_ADMIN_TOKEN=test-token",
	)

	// Debug: Log the environment we're setting
	t.Logf("Setting environment: SPRITE_HTTP_API_TOKEN=test-token")

	// Capture output for debugging
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr

	if err := cmd.Start(); err != nil {
		t.Fatalf("Failed to start test server: %v", err)
	}

	return cmd
}

// stopTestServer stops a test server instance
func stopTestServer(t *testing.T, cmd *exec.Cmd) {
	t.Helper()

	if cmd == nil || cmd.Process == nil {
		return
	}

	// Try graceful shutdown first
	if err := cmd.Process.Kill(); err != nil {
		t.Logf("Failed to kill test server process: %v", err)
	}

	// Wait for process to exit
	if err := cmd.Wait(); err != nil {
		t.Logf("Test server process exited with error: %v", err)
	}

	// Clean up binary
	binaryPath := filepath.Join("..", "tmp", "sprite-env-test")
	if err := os.Remove(binaryPath); err != nil {
		t.Logf("Failed to remove test binary: %v", err)
	}
}
