package fly

import (
	"context"
	"os"
	"testing"
	"time"
)

func TestSuspend(t *testing.T) {
	// Setup mock server
	mock, err := NewMockServer()
	if err != nil {
		t.Fatalf("Failed to create mock server: %v", err)
	}
	defer mock.Stop()

	if err := mock.Start(); err != nil {
		t.Fatalf("Failed to start mock server: %v", err)
	}

	// Override the socket path
	originalSocketPath := LocalAPI.socketPath
	LocalAPI.socketPath = mock.SocketPath()
	defer func() {
		LocalAPI.socketPath = originalSocketPath
	}()

	// Set environment variables
	os.Setenv("FLY_APP_NAME", "test-app")
	os.Setenv("FLY_MACHINE_ID", "test-machine")
	defer func() {
		os.Unsetenv("FLY_APP_NAME")
		os.Unsetenv("FLY_MACHINE_ID")
	}()

	// Test suspend
	ctx := context.Background()
	err = Suspend(ctx)
	if err != nil {
		t.Errorf("Suspend() failed: %v", err)
	}
}

func TestSuspendWithoutEnvVars(t *testing.T) {
	// Ensure env vars are not set
	os.Unsetenv("FLY_APP_NAME")
	os.Unsetenv("FLY_MACHINE_ID")

	ctx := context.Background()
	err := Suspend(ctx)
	if err == nil {
		t.Error("Suspend() should fail without FLY_APP_NAME")
	}
}

func TestSecretsList(t *testing.T) {
	// Setup mock server
	mock, err := NewMockServer()
	if err != nil {
		t.Fatalf("Failed to create mock server: %v", err)
	}
	defer mock.Stop()

	if err := mock.Start(); err != nil {
		t.Fatalf("Failed to start mock server: %v", err)
	}

	// Override the socket path
	originalSocketPath := LocalAPI.socketPath
	LocalAPI.socketPath = mock.SocketPath()
	defer func() {
		LocalAPI.socketPath = originalSocketPath
	}()

	// Set environment variables
	os.Setenv("FLY_APP_NAME", "test-app")
	defer os.Unsetenv("FLY_APP_NAME")

	// Add some test secrets
	mock.SetSecret(Secret{
		Name:      "SECRET1",
		Value:     "value1",
		Digest:    "digest1",
		CreatedAt: time.Now().Format(time.RFC3339),
		UpdatedAt: time.Now().Format(time.RFC3339),
	})
	mock.SetSecret(Secret{
		Name:      "SECRET2",
		Value:     "value2",
		Digest:    "digest2",
		CreatedAt: time.Now().Format(time.RFC3339),
		UpdatedAt: time.Now().Format(time.RFC3339),
	})

	// Test list secrets
	ctx := context.Background()
	secrets, err := Secrets.List(ctx, "")
	if err != nil {
		t.Fatalf("Secrets.List() failed: %v", err)
	}

	if len(secrets) != 2 {
		t.Errorf("Expected 2 secrets, got %d", len(secrets))
	}

	// Check that values are returned (show_secrets=true)
	for _, s := range secrets {
		if s.Value == "" {
			t.Errorf("Secret %s has empty value", s.Name)
		}
	}
}

func TestSecretsGet(t *testing.T) {
	// Setup mock server
	mock, err := NewMockServer()
	if err != nil {
		t.Fatalf("Failed to create mock server: %v", err)
	}
	defer mock.Stop()

	if err := mock.Start(); err != nil {
		t.Fatalf("Failed to start mock server: %v", err)
	}

	// Override the socket path
	originalSocketPath := LocalAPI.socketPath
	LocalAPI.socketPath = mock.SocketPath()
	defer func() {
		LocalAPI.socketPath = originalSocketPath
	}()

	// Set environment variables
	os.Setenv("FLY_APP_NAME", "test-app")
	defer os.Unsetenv("FLY_APP_NAME")

	// Add a test secret
	testSecret := Secret{
		Name:      "TEST_SECRET",
		Value:     "secret-value",
		Digest:    "test-digest",
		CreatedAt: time.Now().Format(time.RFC3339),
		UpdatedAt: time.Now().Format(time.RFC3339),
	}
	mock.SetSecret(testSecret)

	// Test get secret
	ctx := context.Background()
	secret, err := Secrets.Get(ctx, "TEST_SECRET", "")
	if err != nil {
		t.Fatalf("Secrets.Get() failed: %v", err)
	}

	if secret.Name != testSecret.Name {
		t.Errorf("Expected secret name %s, got %s", testSecret.Name, secret.Name)
	}

	if secret.Value != testSecret.Value {
		t.Errorf("Expected secret value %s, got %s", testSecret.Value, secret.Value)
	}

	// Test get non-existent secret
	_, err = Secrets.Get(ctx, "NON_EXISTENT", "")
	if err == nil {
		t.Error("Secrets.Get() should fail for non-existent secret")
	}
}

func TestSecretsGetWithMinVersion(t *testing.T) {
	// Setup mock server
	mock, err := NewMockServer()
	if err != nil {
		t.Fatalf("Failed to create mock server: %v", err)
	}
	defer mock.Stop()

	if err := mock.Start(); err != nil {
		t.Fatalf("Failed to start mock server: %v", err)
	}

	// Override the socket path
	originalSocketPath := LocalAPI.socketPath
	LocalAPI.socketPath = mock.SocketPath()
	defer func() {
		LocalAPI.socketPath = originalSocketPath
	}()

	// Set environment variables
	os.Setenv("FLY_APP_NAME", "test-app")
	defer os.Unsetenv("FLY_APP_NAME")

	// Add a test secret
	testSecret := Secret{
		Name:      "VERSIONED_SECRET",
		Value:     "versioned-value",
		Digest:    "version-123",
		CreatedAt: time.Now().Format(time.RFC3339),
		UpdatedAt: time.Now().Format(time.RFC3339),
	}
	mock.SetSecret(testSecret)

	// Test get secret with min_version
	ctx := context.Background()
	secret, err := Secrets.Get(ctx, "VERSIONED_SECRET", "version-100")
	if err != nil {
		t.Fatalf("Secrets.Get() with min_version failed: %v", err)
	}

	if secret.Name != testSecret.Name {
		t.Errorf("Expected secret name %s, got %s", testSecret.Name, secret.Name)
	}
}
