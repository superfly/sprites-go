// Package keyring provides a keyring interface that automatically falls back
// to file-based storage when the system keyring is unavailable.
package keyring

import (
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"sync"

	"github.com/zalando/go-keyring"
)

var (
	// fallbackKeyring is the file-based keyring used when OS keyring is unavailable
	fallbackKeyring *FileKeyring
	// usingFallback tracks whether we've fallen back to file storage
	usingFallback bool
	// fallbackOnce ensures we only initialize fallback once
	fallbackOnce sync.Once
	// warnedAboutFallback ensures we only warn once per process
	warnedAboutFallback bool
	warnMutex           sync.Mutex
)

// initFallback initializes the fallback file-based keyring
func initFallback() error {
	var initErr error
	fallbackOnce.Do(func() {
		home, err := os.UserHomeDir()
		if err != nil {
			initErr = fmt.Errorf("failed to get home directory: %w", err)
			return
		}

		keyringDir := filepath.Join(home, ".sprite", "keyring")
		fallbackKeyring, initErr = NewFileKeyring(keyringDir)
		if initErr == nil {
			usingFallback = true
			slog.Debug("Initialized file-based keyring fallback", "dir", keyringDir)
		}
	})
	return initErr
}

// warnAboutFallback prints a warning that secrets are being stored on disk
func warnAboutFallback() {
	warnMutex.Lock()
	defer warnMutex.Unlock()

	if warnedAboutFallback {
		return
	}

	fmt.Fprintf(os.Stderr, "\n⚠️  WARNING: No system keyring available. Storing secrets unencrypted in ~/.sprite/keyring/\n")
	fmt.Fprintf(os.Stderr, "   For better security, ensure your system keyring is available.\n\n")
	warnedAboutFallback = true
}

// Set stores a password, falling back to file storage if system keyring fails
func Set(service, user, password string) error {
	err := keyring.Set(service, user, password)
	if err == nil {
		return nil
	}

	// System keyring failed, try fallback
	slog.Debug("System keyring Set failed, attempting fallback", "error", err)
	if err := initFallback(); err != nil {
		return fmt.Errorf("system keyring unavailable and fallback failed: %w", err)
	}

	warnAboutFallback()
	return fallbackKeyring.Set(service, user, password)
}

// Get retrieves a password, falling back to file storage if system keyring fails
func Get(service, user string) (string, error) {
	password, err := keyring.Get(service, user)
	if err == nil {
		return password, nil
	}

	// System keyring failed, try fallback
	slog.Debug("System keyring Get failed, attempting fallback", "error", err)
	if err := initFallback(); err != nil {
		return "", fmt.Errorf("system keyring unavailable and fallback failed: %w", err)
	}

	return fallbackKeyring.Get(service, user)
}

// Delete removes a password, trying both system keyring and fallback
func Delete(service, user string) error {
	// Try system keyring first
	err := keyring.Delete(service, user)
	if err == nil {
		return nil
	}

	// System keyring failed, try fallback
	if usingFallback && fallbackKeyring != nil {
		return fallbackKeyring.Delete(service, user)
	}

	return err
}

// DeleteAll removes all passwords for a service, trying both system keyring and fallback
func DeleteAll(service string) error {
	// Note: zalando/go-keyring doesn't expose DeleteAll, so we only handle fallback
	if usingFallback && fallbackKeyring != nil {
		return fallbackKeyring.DeleteAll(service)
	}
	return nil
}

// IsUsingFallback returns true if the file-based fallback is being used
func IsUsingFallback() bool {
	return usingFallback
}
