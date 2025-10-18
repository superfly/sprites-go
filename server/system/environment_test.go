package system

import (
	"context"
	"os"
	"testing"
)

func TestTestEnvironment(t *testing.T) {
	env := NewTestEnvironment("test-app")

	if env.AppName() != "test-app" {
		t.Errorf("Expected app name 'test-app', got '%s'", env.AppName())
	}

	// Test secrets
	env.SetSecret("TEST_SECRET", "test-value")

	ctx := context.Background()
	value, err := env.GetSecret(ctx, "TEST_SECRET")
	if err != nil {
		t.Errorf("GetSecret failed: %v", err)
	}
	if value != "test-value" {
		t.Errorf("Expected secret value 'test-value', got '%s'", value)
	}

	// Test list secrets
	secrets, err := env.ListSecrets(ctx)
	if err != nil {
		t.Errorf("ListSecrets failed: %v", err)
	}
	if len(secrets) != 1 {
		t.Errorf("Expected 1 secret, got %d", len(secrets))
	}
	if secrets["TEST_SECRET"] != "test-value" {
		t.Error("Secret not found in list")
	}

	// Test suspend
	if env.IsSuspended() {
		t.Error("Environment should not be suspended initially")
	}

	err = env.Suspend(ctx)
	if err != nil {
		t.Errorf("Suspend failed: %v", err)
	}

	if !env.IsSuspended() {
		t.Error("Environment should be suspended after calling Suspend")
	}
}

func TestLocalEnvironment(t *testing.T) {
	// Set test environment variables for secrets
	os.Setenv("TEST_SECRET_VAR", "secret-value")
	defer func() {
		os.Unsetenv("TEST_SECRET_VAR")
	}()

	env := NewLocalEnvironment()

	// AppName should be empty in local environment
	if env.AppName() != "" {
		t.Errorf("Expected empty app name, got '%s'", env.AppName())
	}

	// Test getting a secret from environment variable
	ctx := context.Background()
	value, err := env.GetSecret(ctx, "TEST_SECRET_VAR")
	if err != nil {
		t.Errorf("GetSecret failed: %v", err)
	}
	if value != "secret-value" {
		t.Errorf("Expected secret value 'secret-value', got '%s'", value)
	}

	// Test listing secrets (should include TEST_SECRET_VAR)
	secrets, err := env.ListSecrets(ctx)
	if err != nil {
		t.Errorf("ListSecrets failed: %v", err)
	}
	if secrets["TEST_SECRET_VAR"] != "secret-value" {
		t.Error("TEST_SECRET_VAR not found in secrets list")
	}

	// Test suspend (should be no-op)
	err = env.Suspend(ctx)
	if err != nil {
		t.Errorf("Suspend failed: %v", err)
	}
}

func TestIsSecretLike(t *testing.T) {
	tests := []struct {
		key      string
		expected bool
	}{
		{"API_KEY", true},
		{"DATABASE_URL", true},
		{"TEST_123", true},
		{"MY_SECRET_VAR", true},
		{"lowercase", false},
		{"MixedCase", false},
		{"WITH-DASH", false},
		{"WITH.DOT", false},
		{"", false},
	}

	for _, tt := range tests {
		result := isSecretLike(tt.key)
		if result != tt.expected {
			t.Errorf("isSecretLike(%q) = %v, expected %v", tt.key, result, tt.expected)
		}
	}
}

func TestFlyEnvironment(t *testing.T) {
	// Set Fly environment variables
	os.Setenv("FLY_APP_NAME", "fly-app")
	os.Setenv("FLY_MACHINE_ID", "fly-machine")
	defer func() {
		os.Unsetenv("FLY_APP_NAME")
		os.Unsetenv("FLY_MACHINE_ID")
	}()

	env := NewFlyEnvironment()

	if env.AppName() != "fly-app" {
		t.Errorf("Expected app name 'fly-app', got '%s'", env.AppName())
	}
}
