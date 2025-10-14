package fly

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/superfly/sprite-env/client/keyring"
)

const (
	// EncryptionKeyringService is the keyring service for encryption keys
	EncryptionKeyringService = "sprites-cli"
	// EncryptionKeyPrefix is the prefix for encryption keys in keyring
	EncryptionKeyPrefix = "fly-encryption-key"
)

// generateEncryptionKey generates a new random 32-byte AES-256 key
func generateEncryptionKey() ([]byte, error) {
	key := make([]byte, 32) // AES-256
	if _, err := io.ReadFull(rand.Reader, key); err != nil {
		return nil, fmt.Errorf("failed to generate encryption key: %w", err)
	}
	return key, nil
}

// getOrCreateEncryptionKey retrieves the encryption key from keyring or creates a new one
func getOrCreateEncryptionKey(userID string) ([]byte, error) {
	keyringService := fmt.Sprintf("%s:%s", EncryptionKeyringService, userID)
	keyringKey := fmt.Sprintf("%s:%s", EncryptionKeyPrefix, userID)

	// Try to get existing key
	encodedKey, err := keyring.Get(keyringService, keyringKey)
	if err == nil && encodedKey != "" {
		// Decode the base64-encoded key
		key, err := base64.StdEncoding.DecodeString(encodedKey)
		if err != nil {
			return nil, fmt.Errorf("failed to decode encryption key: %w", err)
		}
		if len(key) != 32 {
			return nil, fmt.Errorf("invalid encryption key length: %d", len(key))
		}
		return key, nil
	}

	// Key doesn't exist, generate a new one
	key, err := generateEncryptionKey()
	if err != nil {
		return nil, err
	}

	// Store the key in keyring (base64 encoded)
	encodedKey = base64.StdEncoding.EncodeToString(key)
	if err := keyring.Set(keyringService, keyringKey, encodedKey); err != nil {
		return nil, fmt.Errorf("failed to store encryption key: %w", err)
	}

	return key, nil
}

// deleteEncryptionKey removes the encryption key from keyring
func deleteEncryptionKey(userID string) error {
	keyringService := fmt.Sprintf("%s:%s", EncryptionKeyringService, userID)
	keyringKey := fmt.Sprintf("%s:%s", EncryptionKeyPrefix, userID)
	return keyring.Delete(keyringService, keyringKey)
}

// encryptToken encrypts a token using AES-256-GCM with envelope encryption
func encryptToken(token string, key []byte) ([]byte, error) {
	// Create AES cipher
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, fmt.Errorf("failed to create cipher: %w", err)
	}

	// Create GCM mode
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, fmt.Errorf("failed to create GCM: %w", err)
	}

	// Generate nonce
	nonce := make([]byte, gcm.NonceSize())
	if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
		return nil, fmt.Errorf("failed to generate nonce: %w", err)
	}

	// Encrypt token
	ciphertext := gcm.Seal(nonce, nonce, []byte(token), nil)
	return ciphertext, nil
}

// decryptToken decrypts a token using AES-256-GCM
func decryptToken(ciphertext []byte, key []byte) (string, error) {
	// Create AES cipher
	block, err := aes.NewCipher(key)
	if err != nil {
		return "", fmt.Errorf("failed to create cipher: %w", err)
	}

	// Create GCM mode
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return "", fmt.Errorf("failed to create GCM: %w", err)
	}

	// Extract nonce
	nonceSize := gcm.NonceSize()
	if len(ciphertext) < nonceSize {
		return "", fmt.Errorf("ciphertext too short")
	}
	nonce, ciphertext := ciphertext[:nonceSize], ciphertext[nonceSize:]

	// Decrypt
	plaintext, err := gcm.Open(nil, nonce, ciphertext, nil)
	if err != nil {
		return "", fmt.Errorf("failed to decrypt: %w", err)
	}

	return string(plaintext), nil
}

// hashUserID creates a lowercase hex hash of the userID for safe filenames
// This ensures case-insensitive filesystem compatibility
func hashUserID(userID string) string {
	hash := sha256.Sum256([]byte(userID))
	// Convert to hex and take first 16 characters
	hexHash := hex.EncodeToString(hash[:])
	return strings.ToLower(hexHash[:16])
}

// getTokenFilePath returns the path to the encrypted token file for a user
// Format: <userID>-<hash>.token.enc where hash is lowercase hex for case-insensitive filesystems
// Stored in ~/.sprites/users/ alongside user config files
func getTokenFilePath(userID string) (string, error) {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return "", fmt.Errorf("failed to get home directory: %w", err)
	}

	usersDir := filepath.Join(homeDir, ".sprites", "users")

	// Ensure directory exists with secure permissions
	if err := os.MkdirAll(usersDir, 0700); err != nil {
		return "", fmt.Errorf("failed to create users directory: %w", err)
	}

	// Create safe filename: userID-hash.token.enc
	// The hash ensures uniqueness even on case-insensitive filesystems
	hash := hashUserID(userID)
	filename := fmt.Sprintf("%s-%s.token.enc", userID, hash)

	return filepath.Join(usersDir, filename), nil
}

// StoreFlyTokenEncrypted stores a Fly token using envelope encryption
// The token is encrypted with AES-256-GCM, and the encryption key is stored in the keyring
func StoreFlyTokenEncrypted(userID, token string) error {
	// Get or create encryption key
	key, err := getOrCreateEncryptionKey(userID)
	if err != nil {
		return fmt.Errorf("failed to get encryption key: %w", err)
	}

	// Encrypt token
	ciphertext, err := encryptToken(token, key)
	if err != nil {
		return fmt.Errorf("failed to encrypt token: %w", err)
	}

	// Get token file path
	tokenPath, err := getTokenFilePath(userID)
	if err != nil {
		return err
	}

	// Write encrypted token to file with secure permissions
	if err := os.WriteFile(tokenPath, ciphertext, 0600); err != nil {
		return fmt.Errorf("failed to write encrypted token: %w", err)
	}

	return nil
}

// ReadFlyTokenEncrypted reads and decrypts a Fly token using envelope encryption
func ReadFlyTokenEncrypted(userID string) (string, error) {
	// Get encryption key from keyring
	key, err := getOrCreateEncryptionKey(userID)
	if err != nil {
		return "", fmt.Errorf("failed to get encryption key: %w", err)
	}

	// Get token file path
	tokenPath, err := getTokenFilePath(userID)
	if err != nil {
		return "", err
	}

	// Read encrypted token
	ciphertext, err := os.ReadFile(tokenPath)
	if err != nil {
		if os.IsNotExist(err) {
			return "", ErrNoToken
		}
		return "", fmt.Errorf("failed to read encrypted token: %w", err)
	}

	// Decrypt token
	token, err := decryptToken(ciphertext, key)
	if err != nil {
		return "", fmt.Errorf("failed to decrypt token: %w", err)
	}

	return token, nil
}

// DeleteFlyTokenEncrypted removes both the encrypted token file and the encryption key
func DeleteFlyTokenEncrypted(userID string) error {
	// Delete token file
	tokenPath, err := getTokenFilePath(userID)
	if err != nil {
		return err
	}

	if err := os.Remove(tokenPath); err != nil && !os.IsNotExist(err) {
		return fmt.Errorf("failed to remove encrypted token file: %w", err)
	}

	// Delete encryption key from keyring
	if err := deleteEncryptionKey(userID); err != nil {
		return fmt.Errorf("failed to remove encryption key: %w", err)
	}

	return nil
}

// ReadFlyTokenForUserEncrypted reads the encrypted Fly token for a specific user
func ReadFlyTokenForUserEncrypted(userID string) (string, error) {
	token, err := ReadFlyTokenEncrypted(userID)
	if err != nil {
		return "", err
	}
	return token, nil
}
