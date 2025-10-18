package system

import (
	"context"
	"os"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/fly"
)

// Environment provides access to platform-specific environment information
type Environment interface {
	// AppName returns the application name (Fly-specific, empty in local env)
	AppName() string

	// Suspend suspends the current machine (no-op if not supported)
	Suspend(ctx context.Context) error

	// GetSecret retrieves a secret by name
	GetSecret(ctx context.Context, key string) (string, error)

	// ListSecrets returns all secrets
	ListSecrets(ctx context.Context) (map[string]string, error)
}

// FlyEnvironment implements Environment using Fly.io APIs
type FlyEnvironment struct {
	info *fly.Info
}

// NewFlyEnvironment creates a new Fly environment
func NewFlyEnvironment() *FlyEnvironment {
	return &FlyEnvironment{
		info: fly.Environment(),
	}
}

func (e *FlyEnvironment) AppName() string {
	return e.info.AppName
}

func (e *FlyEnvironment) Suspend(ctx context.Context) error {
	return fly.Suspend(ctx)
}

func (e *FlyEnvironment) GetSecret(ctx context.Context, key string) (string, error) {
	secret, err := fly.Secrets.Get(ctx, key, "")
	if err != nil {
		return "", err
	}
	return secret.Value, nil
}

func (e *FlyEnvironment) ListSecrets(ctx context.Context) (map[string]string, error) {
	secrets, err := fly.Secrets.List(ctx, "")
	if err != nil {
		return nil, err
	}

	result := make(map[string]string, len(secrets))
	for _, secret := range secrets {
		result[secret.Name] = secret.Value
	}
	return result, nil
}

// LocalEnvironment implements Environment using local environment variables
// This is for non-Fly environments where Fly-specific concepts don't apply
type LocalEnvironment struct{}

// NewLocalEnvironment creates a new local environment
func NewLocalEnvironment() *LocalEnvironment {
	return &LocalEnvironment{}
}

func (e *LocalEnvironment) AppName() string {
	return ""
}

func (e *LocalEnvironment) Suspend(ctx context.Context) error {
	// No-op for local environment
	return nil
}

func (e *LocalEnvironment) GetSecret(ctx context.Context, key string) (string, error) {
	// For local environment, secrets come from environment variables
	return os.Getenv(key), nil
}

func (e *LocalEnvironment) ListSecrets(ctx context.Context) (map[string]string, error) {
	// For local environment, return all environment variables that look like secrets
	// (all uppercase with underscores)
	result := make(map[string]string)
	for _, env := range os.Environ() {
		parts := strings.SplitN(env, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := parts[0]
		value := parts[1]

		// Only include uppercase variables with underscores (common secret pattern)
		if isSecretLike(key) {
			result[key] = value
		}
	}
	return result, nil
}

// isSecretLike returns true if the key looks like a secret variable
func isSecretLike(key string) bool {
	if key == "" {
		return false
	}

	// Must be all uppercase, digits, or underscores
	for _, ch := range key {
		if !((ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_') {
			return false
		}
	}

	return true
}

// TestEnvironment implements Environment for testing purposes
type TestEnvironment struct {
	appName   string
	secrets   map[string]string
	suspended bool
}

// NewTestEnvironment creates a new test environment with configurable values
func NewTestEnvironment(appName string) *TestEnvironment {
	return &TestEnvironment{
		appName:   appName,
		secrets:   make(map[string]string),
		suspended: false,
	}
}

func (e *TestEnvironment) AppName() string {
	return e.appName
}

func (e *TestEnvironment) Suspend(ctx context.Context) error {
	// Simulate a delay
	time.Sleep(10 * time.Millisecond)
	e.suspended = true
	return nil
}

func (e *TestEnvironment) GetSecret(ctx context.Context, key string) (string, error) {
	if val, ok := e.secrets[key]; ok {
		return val, nil
	}
	return "", nil
}

func (e *TestEnvironment) ListSecrets(ctx context.Context) (map[string]string, error) {
	result := make(map[string]string, len(e.secrets))
	for k, v := range e.secrets {
		result[k] = v
	}
	return result, nil
}

// SetSecret sets a secret in the test environment
func (e *TestEnvironment) SetSecret(key, value string) {
	e.secrets[key] = value
}

// IsSuspended returns whether the test environment has been suspended
func (e *TestEnvironment) IsSuspended() bool {
	return e.suspended
}
