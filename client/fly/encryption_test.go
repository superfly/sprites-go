package fly

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/zalando/go-keyring"
)

func TestEncryption(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "fly-encryption-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Override home directory for testing
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	userID := "test-user-123"
	testToken := "FlyV1_fm1r_very_long_token_that_would_be_too_big_for_keyring_" +
		"with_lots_of_data_and_multiple_macaroons_concatenated_together_" +
		"making_it_several_kilobytes_in_size_which_exceeds_keyring_limits"

	// Test 1: Store encrypted token
	t.Run("Store encrypted token", func(t *testing.T) {
		err := StoreFlyTokenEncrypted(userID, testToken)
		if err != nil {
			t.Fatalf("Failed to store encrypted token: %v", err)
		}

		// Verify encrypted file exists
		tokenPath, err := getTokenFilePath(userID)
		if err != nil {
			t.Fatalf("Failed to get token path: %v", err)
		}

		if _, err := os.Stat(tokenPath); os.IsNotExist(err) {
			t.Fatal("Encrypted token file was not created")
		}

		// Verify filename format: <userID>-<hash>.token.enc
		expectedHash := hashUserID(userID)
		expectedFilename := userID + "-" + expectedHash + ".token.enc"
		if !strings.HasSuffix(tokenPath, expectedFilename) {
			t.Errorf("Expected filename to end with %s, got %s", expectedFilename, tokenPath)
		}

		// Verify hash is lowercase hex only
		for _, c := range expectedHash {
			if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) {
				t.Errorf("Hash contains invalid character: %c (must be [a-f0-9])", c)
			}
		}

		// Verify encryption key is in keyring
		keyringService := EncryptionKeyringService + ":" + userID
		keyringKey := EncryptionKeyPrefix + ":" + userID
		encKey, err := keyring.Get(keyringService, keyringKey)
		if err != nil {
			t.Fatalf("Encryption key not found in keyring: %v", err)
		}
		if encKey == "" {
			t.Fatal("Encryption key is empty")
		}
	})

	// Test 2: Read encrypted token
	t.Run("Read encrypted token", func(t *testing.T) {
		retrievedToken, err := ReadFlyTokenEncrypted(userID)
		if err != nil {
			t.Fatalf("Failed to read encrypted token: %v", err)
		}

		if retrievedToken != testToken {
			t.Errorf("Retrieved token doesn't match. Expected %d bytes, got %d bytes",
				len(testToken), len(retrievedToken))
		}
	})

	// Test 3: ReadFlyTokenForUser (uses encrypted storage)
	t.Run("ReadFlyTokenForUser", func(t *testing.T) {
		retrievedToken, err := ReadFlyTokenForUser(userID)
		if err != nil {
			t.Fatalf("Failed to read token for user: %v", err)
		}

		if retrievedToken != testToken {
			t.Error("Retrieved token doesn't match original")
		}
	})

	// Test 4: Verify file is actually encrypted (not plaintext)
	t.Run("Verify encryption", func(t *testing.T) {
		tokenPath, err := getTokenFilePath(userID)
		if err != nil {
			t.Fatalf("Failed to get token path: %v", err)
		}

		encryptedData, err := os.ReadFile(tokenPath)
		if err != nil {
			t.Fatalf("Failed to read encrypted file: %v", err)
		}

		// Verify the encrypted data doesn't contain the plaintext token
		encryptedStr := string(encryptedData)
		if len(encryptedStr) > 0 && encryptedStr[:len("FlyV1")] == "FlyV1" {
			t.Error("Token appears to be stored in plaintext!")
		}
	})

	// Test 5: Multiple users have separate tokens
	t.Run("Multiple users", func(t *testing.T) {
		userID2 := "test-user-456"
		testToken2 := "FlyV1_different_token_for_second_user"

		err := StoreFlyTokenEncrypted(userID2, testToken2)
		if err != nil {
			t.Fatalf("Failed to store token for second user: %v", err)
		}

		// Read both tokens
		token1, err := ReadFlyTokenEncrypted(userID)
		if err != nil {
			t.Fatalf("Failed to read token for user 1: %v", err)
		}

		token2, err := ReadFlyTokenEncrypted(userID2)
		if err != nil {
			t.Fatalf("Failed to read token for user 2: %v", err)
		}

		if token1 != testToken {
			t.Error("User 1 token was corrupted")
		}

		if token2 != testToken2 {
			t.Error("User 2 token doesn't match")
		}

		if token1 == token2 {
			t.Error("Users have the same token!")
		}
	})

	// Test 6: Delete encrypted token
	t.Run("Delete encrypted token", func(t *testing.T) {
		err := DeleteFlyTokenEncrypted(userID)
		if err != nil {
			t.Fatalf("Failed to delete encrypted token: %v", err)
		}

		// Verify file is deleted
		tokenPath, err := getTokenFilePath(userID)
		if err != nil {
			t.Fatalf("Failed to get token path: %v", err)
		}

		if _, err := os.Stat(tokenPath); !os.IsNotExist(err) {
			t.Error("Encrypted token file still exists after deletion")
		}

		// Verify encryption key is deleted from keyring
		keyringService := EncryptionKeyringService + ":" + userID
		keyringKey := EncryptionKeyPrefix + ":" + userID
		_, err = keyring.Get(keyringService, keyringKey)
		if err == nil {
			t.Error("Encryption key still exists in keyring after deletion")
		}

		// Verify we can't read the token anymore
		_, err = ReadFlyTokenEncrypted(userID)
		if err != ErrNoToken {
			t.Errorf("Expected ErrNoToken, got %v", err)
		}
	})

	// Test 7: File permissions are secure
	t.Run("File permissions", func(t *testing.T) {
		testUserID := "test-user-permissions"
		err := StoreFlyTokenEncrypted(testUserID, "test-token")
		if err != nil {
			t.Fatalf("Failed to store token: %v", err)
		}

		tokenPath, err := getTokenFilePath(testUserID)
		if err != nil {
			t.Fatalf("Failed to get token path: %v", err)
		}

		info, err := os.Stat(tokenPath)
		if err != nil {
			t.Fatalf("Failed to stat file: %v", err)
		}

		// Check that permissions are 0600 (owner read/write only)
		mode := info.Mode().Perm()
		expected := os.FileMode(0600)
		if mode != expected {
			t.Errorf("File permissions are %o, expected %o", mode, expected)
		}
	})

	// Test 8: Directory permissions are secure
	t.Run("Directory permissions", func(t *testing.T) {
		// The users directory should have 0700 permissions
		homeDir := os.Getenv("HOME")
		usersDir := filepath.Join(homeDir, ".sprites", "users")

		info, err := os.Stat(usersDir)
		if err != nil {
			t.Fatalf("Failed to stat directory: %v", err)
		}

		// Check that permissions are 0700 (owner rwx only)
		mode := info.Mode().Perm()
		expected := os.FileMode(0700)
		if mode != expected {
			t.Errorf("Directory permissions are %o, expected %o", mode, expected)
		}
	})

	// Test 9: Large token handling
	t.Run("Large token", func(t *testing.T) {
		// Create a very large token (10KB+)
		largeToken := "FlyV1_"
		for i := 0; i < 10000; i++ {
			largeToken += "x"
		}

		testUserID := "test-user-large"
		err := StoreFlyTokenEncrypted(testUserID, largeToken)
		if err != nil {
			t.Fatalf("Failed to store large token: %v", err)
		}

		retrievedToken, err := ReadFlyTokenEncrypted(testUserID)
		if err != nil {
			t.Fatalf("Failed to read large token: %v", err)
		}

		if retrievedToken != largeToken {
			t.Errorf("Large token corrupted. Expected %d bytes, got %d bytes",
				len(largeToken), len(retrievedToken))
		}
	})
}

func TestEncryptionKeyGeneration(t *testing.T) {
	// Test that encryption keys are properly generated
	key1, err := generateEncryptionKey()
	if err != nil {
		t.Fatalf("Failed to generate key: %v", err)
	}

	if len(key1) != 32 {
		t.Errorf("Key length is %d, expected 32", len(key1))
	}

	// Generate another key to ensure they're different
	key2, err := generateEncryptionKey()
	if err != nil {
		t.Fatalf("Failed to generate second key: %v", err)
	}

	// Keys should be different
	if string(key1) == string(key2) {
		t.Error("Generated keys are identical!")
	}
}

func TestEncryptDecrypt(t *testing.T) {
	key, err := generateEncryptionKey()
	if err != nil {
		t.Fatalf("Failed to generate key: %v", err)
	}

	testCases := []string{
		"short",
		"a longer token with multiple words",
		"FlyV1_fm1r_abc123",
		"",
		"unicode: 你好世界 🚀",
	}

	for _, testToken := range testCases {
		t.Run("token: "+testToken, func(t *testing.T) {
			encrypted, err := encryptToken(testToken, key)
			if err != nil {
				t.Fatalf("Failed to encrypt: %v", err)
			}

			decrypted, err := decryptToken(encrypted, key)
			if err != nil {
				t.Fatalf("Failed to decrypt: %v", err)
			}

			if decrypted != testToken {
				t.Errorf("Decrypted token doesn't match. Expected %q, got %q", testToken, decrypted)
			}
		})
	}
}

func TestEncryptionWithWrongKey(t *testing.T) {
	key1, _ := generateEncryptionKey()
	key2, _ := generateEncryptionKey()

	token := "test-token"

	encrypted, err := encryptToken(token, key1)
	if err != nil {
		t.Fatalf("Failed to encrypt: %v", err)
	}

	// Try to decrypt with wrong key
	_, err = decryptToken(encrypted, key2)
	if err == nil {
		t.Error("Decryption with wrong key should have failed")
	}
}

func TestCaseInsensitiveFilenames(t *testing.T) {
	// Test that userIDs that differ only in case get different filenames
	userID1 := "UserABC123"
	userID2 := "userabc123"
	userID3 := "USERABC123"

	hash1 := hashUserID(userID1)
	hash2 := hashUserID(userID2)
	hash3 := hashUserID(userID3)

	// Hashes should be different
	if hash1 == hash2 {
		t.Error("Different case userIDs produced same hash")
	}
	if hash1 == hash3 {
		t.Error("Different case userIDs produced same hash")
	}
	if hash2 == hash3 {
		t.Error("Different case userIDs produced same hash")
	}

	// All hashes should be lowercase hex
	for _, hash := range []string{hash1, hash2, hash3} {
		if len(hash) != 16 {
			t.Errorf("Hash length is %d, expected 16", len(hash))
		}
		for _, c := range hash {
			if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) {
				t.Errorf("Hash contains invalid character: %c (must be [0-9a-f])", c)
			}
		}
		// Verify no uppercase
		if strings.ToLower(hash) != hash {
			t.Error("Hash contains uppercase characters")
		}
	}

	// Test that filenames are different
	path1, _ := getTokenFilePath(userID1)
	path2, _ := getTokenFilePath(userID2)
	path3, _ := getTokenFilePath(userID3)

	if path1 == path2 || path1 == path3 || path2 == path3 {
		t.Error("Different case userIDs produced same file path")
	}

	// Verify filename format
	expectedFilename1 := fmt.Sprintf("%s-%s.token.enc", userID1, hash1)
	if !strings.HasSuffix(path1, expectedFilename1) {
		t.Errorf("Expected path to end with %s, got %s", expectedFilename1, path1)
	}
}

func TestHashUserID(t *testing.T) {
	testCases := []struct {
		userID string
		name   string
	}{
		{"simple", "lowercase simple"},
		{"UPPERCASE", "all uppercase"},
		{"MixedCase123", "mixed case with numbers"},
		{"user@example.com", "email format"},
		{"123-456-789", "numeric with dashes"},
		{"user_with_special!@#", "special characters"},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			hash := hashUserID(tc.userID)

			// Verify length
			if len(hash) != 16 {
				t.Errorf("Hash length is %d, expected 16", len(hash))
			}

			// Verify lowercase hex only [0-9a-f]
			for _, c := range hash {
				if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) {
					t.Errorf("Hash contains invalid character: %c", c)
				}
			}

			// Verify deterministic (same input = same hash)
			hash2 := hashUserID(tc.userID)
			if hash != hash2 {
				t.Error("Hash function is not deterministic")
			}
		})
	}
}
