package keyring

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// FileKeyring is a simple file-based keyring implementation that stores
// credentials as plaintext files in a directory structure.
// WARNING: This stores secrets unencrypted on disk and should only be used
// as a fallback when no system keyring is available.
type FileKeyring struct {
	dir string
}

// NewFileKeyring creates a new file-based keyring that stores data in the given directory.
func NewFileKeyring(dir string) (*FileKeyring, error) {
	// Expand home directory if present
	if strings.HasPrefix(dir, "~/") {
		home, err := os.UserHomeDir()
		if err != nil {
			return nil, fmt.Errorf("failed to get home directory: %w", err)
		}
		dir = filepath.Join(home, dir[2:])
	}

	// Create directory if it doesn't exist
	if err := os.MkdirAll(dir, 0700); err != nil {
		return nil, fmt.Errorf("failed to create keyring directory: %w", err)
	}

	return &FileKeyring{dir: dir}, nil
}

// sanitizePath converts service and user into a safe filename by replacing colons with dashes
func (f *FileKeyring) sanitizePath(service, user string) string {
	// Replace colons with dashes to make valid filenames
	service = strings.ReplaceAll(service, ":", "-")
	user = strings.ReplaceAll(user, ":", "-")

	// Create path: <dir>/<service>/<user>
	return filepath.Join(f.dir, service, user)
}

// Set stores a password for the given service and user
func (f *FileKeyring) Set(service, user, password string) error {
	path := f.sanitizePath(service, user)

	// Ensure parent directory exists
	if err := os.MkdirAll(filepath.Dir(path), 0700); err != nil {
		return fmt.Errorf("failed to create service directory: %w", err)
	}

	// Write password to file with secure permissions
	if err := os.WriteFile(path, []byte(password), 0600); err != nil {
		return fmt.Errorf("failed to write keyring entry: %w", err)
	}

	return nil
}

// Get retrieves a password for the given service and user
func (f *FileKeyring) Get(service, user string) (string, error) {
	path := f.sanitizePath(service, user)

	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return "", fmt.Errorf("keyring entry not found")
		}
		return "", fmt.Errorf("failed to read keyring entry: %w", err)
	}

	return string(data), nil
}

// Delete removes a password for the given service and user
func (f *FileKeyring) Delete(service, user string) error {
	path := f.sanitizePath(service, user)

	if err := os.Remove(path); err != nil {
		if os.IsNotExist(err) {
			return nil // Already deleted
		}
		return fmt.Errorf("failed to delete keyring entry: %w", err)
	}

	return nil
}

// DeleteAll removes all passwords for the given service
func (f *FileKeyring) DeleteAll(service string) error {
	service = strings.ReplaceAll(service, ":", "-")
	servicePath := filepath.Join(f.dir, service)

	if err := os.RemoveAll(servicePath); err != nil {
		if os.IsNotExist(err) {
			return nil // Already deleted
		}
		return fmt.Errorf("failed to delete service directory: %w", err)
	}

	return nil
}
