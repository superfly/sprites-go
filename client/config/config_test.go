package config

import (
	"os"
	"testing"

	"github.com/zalando/go-keyring"
)

func TestNewManager(t *testing.T) {
	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "config-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create manager
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	if mgr == nil {
		t.Fatal("Manager is nil")
	}
}

func TestAddAndGetSprite(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "sprite-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create manager
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Add a user first (required for v2)
	err = mgr.AddUser("test-user-123", "test@example.com")
	if err != nil {
		t.Fatalf("Failed to add user: %v", err)
	}

	// Set as active user
	err = mgr.SetActiveUser("test-user-123")
	if err != nil {
		t.Fatalf("Failed to set active user: %v", err)
	}

	// Add a sprite
	err = mgr.AddSprite("https://api.test.com", "test-org", "test-sprite", "test-token")
	if err != nil {
		t.Fatalf("Failed to add sprite: %v", err)
	}

	// Check current selection was set
	if mgr.config.CurrentSelection == nil {
		t.Fatal("Current selection should be set after adding first sprite")
	}
	if mgr.config.CurrentSelection.URL != "https://api.test.com" {
		t.Errorf("Expected URL https://api.test.com, got %s", mgr.config.CurrentSelection.URL)
	}
	if mgr.config.CurrentSelection.Org != "test-org" {
		t.Errorf("Expected org test-org, got %s", mgr.config.CurrentSelection.Org)
	}

	// Get current org token
	token, err := mgr.GetCurrentOrgToken()
	if err != nil {
		t.Fatalf("Failed to get current org token: %v", err)
	}
	if token != "test-token" {
		t.Errorf("Expected token test-token, got %s", token)
	}
}

func TestFindSprite(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "find-sprite-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create manager
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Add a user and set as active (required for v2)
	err = mgr.AddUser("test-user-123", "test@example.com")
	if err != nil {
		t.Fatalf("Failed to add user: %v", err)
	}
	err = mgr.SetActiveUser("test-user-123")
	if err != nil {
		t.Fatalf("Failed to set active user: %v", err)
	}

	// Add sprites with same name to different URLs
	err = mgr.AddSprite("https://api.prod.com", "acme-corp", "my-app", "prod-token")
	if err != nil {
		t.Fatalf("Failed to add prod sprite: %v", err)
	}

	err = mgr.AddSprite("https://api.dev.com", "acme-corp", "my-app", "dev-token")
	if err != nil {
		t.Fatalf("Failed to add dev sprite: %v", err)
	}

	// Find sprite by name - will handle conflict
	sprite, url, org, name, err := mgr.FindSprite("my-app")
	if err != nil {
		t.Fatalf("Failed to find sprite: %v", err)
	}

	// The function will print a warning about multiple sprites and choose one
	t.Logf("Found sprite: %s at %s (org: %s)", name, url, org)

	// Verify the sprite was found
	if sprite == nil {
		t.Error("Expected to find a sprite")
	}
}

func TestRemoveSprite(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "remove-sprite-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create manager
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Add a user and set as active (required for v2)
	err = mgr.AddUser("test-user-123", "test@example.com")
	if err != nil {
		t.Fatalf("Failed to add user: %v", err)
	}
	err = mgr.SetActiveUser("test-user-123")
	if err != nil {
		t.Fatalf("Failed to set active user: %v", err)
	}

	// Add sprites
	err = mgr.AddSprite("https://api.test.com", "test-org", "sprite1", "token1")
	if err != nil {
		t.Fatalf("Failed to add sprite1: %v", err)
	}

	err = mgr.AddSprite("https://api.test.com", "test-org", "sprite2", "token2")
	if err != nil {
		t.Fatalf("Failed to add sprite2: %v", err)
	}

	// Remove sprite1
	err = mgr.RemoveSprite("https://api.test.com", "test-org", "sprite1")
	if err != nil {
		t.Fatalf("Failed to remove sprite1: %v", err)
	}

	// Verify sprite1 is gone
	_, _, _, _, err = mgr.FindSprite("sprite1")
	if err == nil {
		t.Error("sprite1 should not be found after removal")
	}

	// Verify sprite2 still exists
	_, _, _, _, err = mgr.FindSprite("sprite2")
	if err != nil {
		t.Error("sprite2 should still exist")
	}

	// Remove sprite2 (last sprite in org)
	err = mgr.RemoveSprite("https://api.test.com", "test-org", "sprite2")
	if err != nil {
		t.Fatalf("Failed to remove sprite2: %v", err)
	}

	// Verify org is gone (check user config)
	if mgr.userConfig != nil && len(mgr.userConfig.URLs) != 0 {
		t.Error("User's URL config should be empty after removing all sprites")
	}

	// Verify current selection is cleared
	if mgr.config.CurrentSelection != nil {
		t.Error("Current selection should be nil after removing all sprites")
	}
}

func TestSetCurrentOrg(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "current-org-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create manager
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Add a user and set as active (required for v2)
	err = mgr.AddUser("test-user-123", "test@example.com")
	if err != nil {
		t.Fatalf("Failed to add user: %v", err)
	}
	err = mgr.SetActiveUser("test-user-123")
	if err != nil {
		t.Fatalf("Failed to set active user: %v", err)
	}

	// Add sprites to different orgs
	err = mgr.AddSprite("https://api.test.com", "org1", "sprite1", "token1")
	if err != nil {
		t.Fatalf("Failed to add sprite to org1: %v", err)
	}

	err = mgr.AddSprite("https://api.test.com", "org2", "sprite2", "token2")
	if err != nil {
		t.Fatalf("Failed to add sprite to org2: %v", err)
	}

	// Set current org to org2
	err = mgr.SetCurrentOrg("org2")
	if err != nil {
		t.Fatalf("Failed to set current org: %v", err)
	}

	// Verify current selection
	if mgr.config.CurrentSelection == nil {
		t.Fatal("Current selection should not be nil")
	}
	if mgr.config.CurrentSelection.Org != "org2" {
		t.Errorf("Expected current org to be org2, got %s", mgr.config.CurrentSelection.Org)
	}

	// Get current token
	token, err := mgr.GetCurrentOrgToken()
	if err != nil {
		t.Fatalf("Failed to get current org token: %v", err)
	}
	if token != "token2" {
		t.Errorf("Expected token2, got %s", token)
	}
}

func TestVersionMetadata(t *testing.T) {
	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "version-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create manager
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Test version setters and getters
	mgr.SetLastVersionCheck("2023-01-01T00:00:00Z")
	if mgr.GetLastVersionCheck() != "2023-01-01T00:00:00Z" {
		t.Error("LastVersionCheck not set correctly")
	}

	mgr.SetLatestVersion("v1.2.3")
	if mgr.GetLatestVersion() != "v1.2.3" {
		t.Error("LatestVersion not set correctly")
	}

	mgr.SetCurrentVersion("v1.0.0")
	if mgr.GetCurrentVersion() != "v1.0.0" {
		t.Error("CurrentVersion not set correctly")
	}
}
