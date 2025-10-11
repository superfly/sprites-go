package system

import (
	"context"
	"log/slog"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// createTestLogger creates a logger for testing
func createTestLogger() *slog.Logger {
	return slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
}

func TestSpriteDB(t *testing.T) {
	// Create temporary directory for test
	tempDir := t.TempDir()

	// Create a minimal config
	config := &Config{
		JuiceFSDataPath: tempDir,
		WriteDir:        tempDir,
	}

	// Create system
	sys := &System{
		ctx:    context.Background(),
		config: config,
		logger: createTestLogger(),
	}

	// Initialize sprite DB
	ctx := context.Background()
	err := sys.InitializeSpriteDB(ctx)
	if err != nil {
		t.Fatalf("Failed to initialize sprite DB: %v", err)
	}

	// Verify DB file was created
	dbPath := sys.GetSpriteDBPath()
	if _, err := os.Stat(dbPath); os.IsNotExist(err) {
		t.Fatalf("Sprite DB file was not created at %s", dbPath)
	}

	// Test getting sprite info when not assigned (should error)
	_, err = sys.GetSpriteInfo(ctx)
	if err == nil {
		t.Error("Expected error when getting sprite info before assignment, got nil")
	}

	// Test setting sprite info
	info := &SpriteInfo{
		SpriteName: "test-sprite",
		SpriteURL:  "test-sprite-abc123.sprites.app",
		OrgID:      "org_123",
		SpriteID:   "sprite_456",
		AssignedAt: time.Now().UTC(),
	}

	err = sys.SetSpriteInfo(ctx, info)
	if err != nil {
		t.Fatalf("Failed to set sprite info: %v", err)
	}

	// Test getting sprite info after assignment
	retrieved, err := sys.GetSpriteInfo(ctx)
	if err != nil {
		t.Fatalf("Failed to get sprite info: %v", err)
	}

	if retrieved.SpriteName != info.SpriteName {
		t.Errorf("SpriteName mismatch: got %s, want %s", retrieved.SpriteName, info.SpriteName)
	}
	if retrieved.SpriteURL != info.SpriteURL {
		t.Errorf("SpriteURL mismatch: got %s, want %s", retrieved.SpriteURL, info.SpriteURL)
	}
	if retrieved.OrgID != info.OrgID {
		t.Errorf("OrgID mismatch: got %s, want %s", retrieved.OrgID, info.OrgID)
	}
	if retrieved.SpriteID != info.SpriteID {
		t.Errorf("SpriteID mismatch: got %s, want %s", retrieved.SpriteID, info.SpriteID)
	}

	// Test that changing name/org fails
	newInfo := &SpriteInfo{
		SpriteName: "different-sprite",
		SpriteURL:  "different-sprite-xyz789.sprites.app",
		OrgID:      "org_999",
		SpriteID:   "sprite_999",
		AssignedAt: time.Now().UTC(),
	}

	err = sys.SetSpriteInfo(ctx, newInfo)
	if err == nil {
		t.Error("Expected error when changing sprite name/org, got nil")
	}
	if err != nil && err.Error() != "sprite name and org cannot be changed once set" {
		t.Errorf("Wrong error message: %v", err)
	}

	// Verify original info is still intact
	retrieved, err = sys.GetSpriteInfo(ctx)
	if err != nil {
		t.Fatalf("Failed to get sprite info after reassignment attempt: %v", err)
	}
	if retrieved.SpriteName != info.SpriteName {
		t.Errorf("SpriteName changed after failed reassignment: got %s, want %s", retrieved.SpriteName, info.SpriteName)
	}

	// Test that URL can be updated
	updatedInfo := &SpriteInfo{
		SpriteName: info.SpriteName, // Same name
		SpriteURL:  "updated-sprite-url.sprites.app",
		OrgID:      info.OrgID,      // Same org
		SpriteID:   info.SpriteID,   // Same sprite ID
		AssignedAt: time.Now().UTC(),
	}

	err = sys.SetSpriteInfo(ctx, updatedInfo)
	if err != nil {
		t.Errorf("Expected URL update to succeed, got error: %v", err)
	}

	// Verify URL was updated
	retrieved, err = sys.GetSpriteInfo(ctx)
	if err != nil {
		t.Fatalf("Failed to get sprite info after URL update: %v", err)
	}
	if retrieved.SpriteURL != updatedInfo.SpriteURL {
		t.Errorf("URL not updated: got %s, want %s", retrieved.SpriteURL, updatedInfo.SpriteURL)
	}
	// Verify other fields remain unchanged
	if retrieved.SpriteName != info.SpriteName {
		t.Errorf("SpriteName changed during URL update: got %s, want %s", retrieved.SpriteName, info.SpriteName)
	}
	if retrieved.OrgID != info.OrgID {
		t.Errorf("OrgID changed during URL update: got %s, want %s", retrieved.OrgID, info.OrgID)
	}
}

func TestApplySpriteHostname(t *testing.T) {
	// Skip if not running as root (can't set hostname)
	if os.Geteuid() != 0 {
		t.Skip("Skipping hostname test: requires root privileges")
	}

	tempDir := t.TempDir()
	hostsFile := filepath.Join(tempDir, "hosts")

	config := &Config{
		JuiceFSDataPath: tempDir,
		WriteDir:        tempDir,
	}

	sys := &System{
		ctx:    context.Background(),
		config: config,
		logger: createTestLogger(),
	}

	// Mock the writeFile function to capture what would be written
	var hostsContent []byte
	var hostnameContent []byte

	originalWriteFile := writeHostsFile
	writeHostsFile = func(path string, data []byte, perm uint32) error {
		if path == "/mnt/newroot/etc/hosts" {
			hostsContent = data
			// Write to test file
			return os.WriteFile(hostsFile, data, os.FileMode(perm))
		} else if path == "/mnt/newroot/etc/hostname" {
			hostnameContent = data
		}
		return nil
	}
	defer func() { writeHostsFile = originalWriteFile }()

	// Apply sprite hostname
	spriteName := "test-sprite"
	spriteURL := "test-sprite-abc123.sprites.app"

	ctx := context.Background()
	err := sys.ApplySpriteHostname(ctx, spriteName, spriteURL)
	if err != nil {
		t.Fatalf("Failed to apply sprite hostname: %v", err)
	}

	// Verify /etc/hosts file content (only short hostname, not the public URL)
	expectedLines := []string{
		"127.0.0.1   localhost",
		"127.0.0.1   sprite",
		"127.0.0.1   " + spriteName,
		"fdf::1      localhost",
		"fdf::1      sprite",
		"fdf::1      " + spriteName,
	}

	for _, expectedLine := range expectedLines {
		if !contains(string(hostsContent), expectedLine) {
			t.Errorf("/etc/hosts missing expected line: %s", expectedLine)
		}
	}

	// Verify /etc/hostname file content
	if string(hostnameContent) != spriteName+"\n" {
		t.Errorf("/etc/hostname content mismatch: got %q, want %q", string(hostnameContent), spriteName+"\n")
	}

	// Note: We don't verify hostname was set because setContainerHostname requires
	// a running container with a PID file, which we don't have in this test
}

func TestSetSpriteEnvironment(t *testing.T) {
	// Skip if not running as root
	if os.Geteuid() != 0 {
		t.Skip("Skipping test: requires root privileges")
	}

	tempDir := t.TempDir()
	hostsFile := filepath.Join(tempDir, "hosts")

	config := &Config{
		JuiceFSDataPath: tempDir,
		WriteDir:        tempDir,
	}

	sys := &System{
		ctx:    context.Background(),
		config: config,
		logger: createTestLogger(),
	}

	// Initialize sprite DB
	ctx := context.Background()
	err := sys.InitializeSpriteDB(ctx)
	if err != nil {
		t.Fatalf("Failed to initialize sprite DB: %v", err)
	}

	// Mock writeHostsFile - only write /etc/hosts to our test file
	originalWriteFile := writeHostsFile
	writeHostsFile = func(path string, data []byte, perm uint32) error {
		if path == "/mnt/newroot/etc/hosts" {
			return os.WriteFile(hostsFile, data, os.FileMode(perm))
		}
		return nil
	}
	defer func() { writeHostsFile = originalWriteFile }()

	// Set sprite environment
	info := &SpriteInfo{
		SpriteName: "my-sprite",
		SpriteURL:  "my-sprite-xyz789.sprites.app",
		OrgID:      "org_abc",
		SpriteID:   "sprite_def",
	}
	responseAny, err := sys.SetSpriteEnvironment(ctx, info)
	if err != nil {
		t.Fatalf("Failed to set sprite environment: %v", err)
	}
	response, ok := responseAny.(*SpriteEnvironmentResponse)
	if !ok {
		t.Fatalf("Invalid response type")
	}
	if err != nil {
		t.Fatalf("Failed to set sprite environment: %v", err)
	}
	if response.Status != "ok" {
		t.Errorf("Expected status ok, got %s", response.Status)
	}

	// Verify DB was updated
	info, err = sys.GetSpriteInfo(ctx)
	if err != nil {
		t.Fatalf("Failed to get sprite info: %v", err)
	}
	if info.SpriteName != "my-sprite" {
		t.Errorf("SpriteName mismatch: got %s, want my-sprite", info.SpriteName)
	}

	// Verify container hosts file was written
	hostsContent, err := os.ReadFile(hostsFile)
	if err != nil {
		t.Fatalf("Failed to read hosts file: %v", err)
	}
	if !contains(string(hostsContent), "127.0.0.1   my-sprite") {
		t.Error("hosts file does not contain sprite hostname entry")
	}

	// Note: We don't verify hostname was set because setContainerHostname requires
	// a running container with a PID file, which we don't have in this test
}

// Helper function
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) &&
		(s[:len(substr)] == substr || s[len(s)-len(substr):] == substr ||
		len(s) > len(substr)+1 && s[1:len(substr)+1] == substr ||
		findSubstring(s, substr)))
}

func findSubstring(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
