package keyring

import (
	"os"
	"path/filepath"
	"sync"
	"testing"

	"github.com/zalando/go-keyring"
)

func TestFileKeyringBasics(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir := t.TempDir()

	kr, err := NewFileKeyring(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create file keyring: %v", err)
	}

	service := "test-service"
	user := "test-user"
	password := "test-password"

	// Test Set
	err = kr.Set(service, user, password)
	if err != nil {
		t.Fatalf("Failed to set password: %v", err)
	}

	// Test Get
	retrieved, err := kr.Get(service, user)
	if err != nil {
		t.Fatalf("Failed to get password: %v", err)
	}
	if retrieved != password {
		t.Errorf("Expected password %q, got %q", password, retrieved)
	}

	// Test Delete
	err = kr.Delete(service, user)
	if err != nil {
		t.Fatalf("Failed to delete password: %v", err)
	}

	// Verify deleted
	_, err = kr.Get(service, user)
	if err == nil {
		t.Error("Expected error getting deleted password, got nil")
	}
}

func TestFileKeyringSanitizePath(t *testing.T) {
	tmpDir := t.TempDir()
	kr, err := NewFileKeyring(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create file keyring: %v", err)
	}

	// Test with colons in service and user names
	service := "sprites-cli:user123"
	user := "fly-encryption-key:user123"
	password := "secret"

	err = kr.Set(service, user, password)
	if err != nil {
		t.Fatalf("Failed to set password with colons: %v", err)
	}

	retrieved, err := kr.Get(service, user)
	if err != nil {
		t.Fatalf("Failed to get password with colons: %v", err)
	}
	if retrieved != password {
		t.Errorf("Expected password %q, got %q", password, retrieved)
	}

	// Verify the path was sanitized (colons replaced with dashes)
	expectedPath := filepath.Join(tmpDir, "sprites-cli-user123", "fly-encryption-key-user123")
	if _, err := os.Stat(expectedPath); err != nil {
		t.Errorf("Expected file at %s, but stat failed: %v", expectedPath, err)
	}
}

func TestFileKeyringDeleteAll(t *testing.T) {
	tmpDir := t.TempDir()
	kr, err := NewFileKeyring(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create file keyring: %v", err)
	}

	service := "test-service"

	// Create multiple entries
	kr.Set(service, "user1", "pass1")
	kr.Set(service, "user2", "pass2")
	kr.Set(service, "user3", "pass3")

	// Delete all
	err = kr.DeleteAll(service)
	if err != nil {
		t.Fatalf("Failed to delete all: %v", err)
	}

	// Verify all are gone
	for _, user := range []string{"user1", "user2", "user3"} {
		_, err := kr.Get(service, user)
		if err == nil {
			t.Errorf("Expected error getting deleted password for %s, got nil", user)
		}
	}
}

func TestFallbackBehavior(t *testing.T) {
	// Mock the keyring to fail
	keyring.MockInitWithError(os.ErrNotExist)
	defer keyring.MockInit() // Reset after test

	// Reset fallback state for testing
	fallbackKeyring = nil
	usingFallback = false
	fallbackOnce = sync.Once{}
	warnedAboutFallback = false

	// Override home directory for testing
	tmpDir := t.TempDir()
	t.Setenv("HOME", tmpDir)

	service := "test-service"
	user := "test-user"
	password := "test-password"

	// This should fall back to file storage
	err := Set(service, user, password)
	if err != nil {
		t.Fatalf("Failed to set password with fallback: %v", err)
	}

	if !IsUsingFallback() {
		t.Error("Expected to be using fallback, but IsUsingFallback returned false")
	}

	// Verify we can retrieve it
	retrieved, err := Get(service, user)
	if err != nil {
		t.Fatalf("Failed to get password with fallback: %v", err)
	}
	if retrieved != password {
		t.Errorf("Expected password %q, got %q", password, retrieved)
	}

	// Verify it's in the expected location
	keyringDir := filepath.Join(tmpDir, ".sprite", "keyring")
	expectedPath := filepath.Join(keyringDir, service, user)
	if _, err := os.Stat(expectedPath); err != nil {
		t.Errorf("Expected fallback file at %s, but stat failed: %v", expectedPath, err)
	}

	// Test Delete
	err = Delete(service, user)
	if err != nil {
		t.Fatalf("Failed to delete password with fallback: %v", err)
	}

	// Verify deleted
	_, err = Get(service, user)
	if err == nil {
		t.Error("Expected error getting deleted password, got nil")
	}
}

func TestFallbackWithColons(t *testing.T) {
	// Mock the keyring to fail
	keyring.MockInitWithError(os.ErrNotExist)
	defer keyring.MockInit() // Reset after test

	// Reset fallback state for testing
	fallbackKeyring = nil
	usingFallback = false
	fallbackOnce = sync.Once{}
	warnedAboutFallback = false

	// Override home directory for testing
	tmpDir := t.TempDir()
	t.Setenv("HOME", tmpDir)

	service := "sprites-cli:user123"
	user := "fly-encryption-key:user123"
	password := "secret-key-data"

	// Set with colons
	err := Set(service, user, password)
	if err != nil {
		t.Fatalf("Failed to set password with colons: %v", err)
	}

	// Get with colons
	retrieved, err := Get(service, user)
	if err != nil {
		t.Fatalf("Failed to get password with colons: %v", err)
	}
	if retrieved != password {
		t.Errorf("Expected password %q, got %q", password, retrieved)
	}

	// Verify path sanitization
	keyringDir := filepath.Join(tmpDir, ".sprite", "keyring")
	expectedPath := filepath.Join(keyringDir, "sprites-cli-user123", "fly-encryption-key-user123")
	if _, err := os.Stat(expectedPath); err != nil {
		t.Errorf("Expected file at %s, but stat failed: %v", expectedPath, err)
	}
}
