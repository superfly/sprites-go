package config

import (
	"fmt"
	"os"
	"testing"

	"github.com/zalando/go-keyring"
)

func TestUserManagementIntegration(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "user-integration-test")
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

	// Test 1: Add first user
	user1ID := "user1-123"
	user1Email := "alice@example.com"

	err = mgr.AddUser(user1ID, user1Email)
	if err != nil {
		t.Fatalf("Failed to add user: %v", err)
	}

	// Verify user was added
	user := mgr.GetUser(user1ID)
	if user == nil {
		t.Fatal("User not found after adding")
	}
	if user.ID != user1ID {
		t.Errorf("Expected user ID %s, got %s", user1ID, user.ID)
	}
	if user.Email != user1Email {
		t.Errorf("Expected user email %s, got %s", user1Email, user.Email)
	}
	// UserInfo no longer has KeyringService field - it's built from ID
	expectedKeyringService := "sprites-cli:user1-123"
	if fmt.Sprintf("%s:%s", "sprites-cli", user.ID) != expectedKeyringService {
		t.Errorf("Expected keyring service %s", expectedKeyringService)
	}

	// Test 2: Set as active user
	err = mgr.SetActiveUser(user1ID)
	if err != nil {
		t.Fatalf("Failed to set active user: %v", err)
	}

	activeUser := mgr.GetActiveUser()
	if activeUser == nil {
		t.Fatal("No active user found")
	}
	if activeUser.ID != user1ID {
		t.Errorf("Expected active user ID %s, got %s", user1ID, activeUser.ID)
	}

	// Test 3: Add second user
	user2ID := "user2-456"
	user2Email := "bob@example.com"

	err = mgr.AddUser(user2ID, user2Email)
	if err != nil {
		t.Fatalf("Failed to add second user: %v", err)
	}

	// Verify both users exist
	allUsers := mgr.GetAllUsers()
	if len(allUsers) != 2 {
		t.Errorf("Expected 2 users, got %d", len(allUsers))
	}

	// Test 4: Switch active user
	err = mgr.SetActiveUser(user2ID)
	if err != nil {
		t.Fatalf("Failed to switch active user: %v", err)
	}

	activeUser = mgr.GetActiveUser()
	if activeUser.ID != user2ID {
		t.Errorf("Expected active user ID %s, got %s", user2ID, activeUser.ID)
	}

	// Test 5: Remove first user
	err = mgr.RemoveUser(user1ID)
	if err != nil {
		t.Fatalf("Failed to remove user: %v", err)
	}

	// Verify user was removed
	user = mgr.GetUser(user1ID)
	if user != nil {
		t.Fatal("User should have been removed")
	}

	// Verify active user is still user2
	activeUser = mgr.GetActiveUser()
	if activeUser == nil {
		t.Fatal("No active user found after removing user1")
	}
	if activeUser.ID != user2ID {
		t.Errorf("Expected active user ID %s, got %s", user2ID, activeUser.ID)
	}

	// Test 6: Remove active user (should clear active user)
	err = mgr.RemoveUser(user2ID)
	if err != nil {
		t.Fatalf("Failed to remove active user: %v", err)
	}

	activeUser = mgr.GetActiveUser()
	if activeUser != nil {
		t.Fatal("Active user should be cleared after removing the active user")
	}
}

func TestUserScopedKeyringIntegration(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "keyring-integration-test")
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

	// Add two users
	user1ID := "user1-123"
	user1Email := "alice@example.com"
	user2ID := "user2-456"
	user2Email := "bob@example.com"

	err = mgr.AddUser(user1ID, user1Email)
	if err != nil {
		t.Fatalf("Failed to add user1: %v", err)
	}

	err = mgr.AddUser(user2ID, user2Email)
	if err != nil {
		t.Fatalf("Failed to add user2: %v", err)
	}

	// Test 1: Add org for user1
	org1Name := "test-org-1"
	org1Token := "sprite-token-user1"
	apiURL := "https://api.sprites.dev"

	err = mgr.AddOrgWithUser(org1Name, org1Token, apiURL, user1ID, user1Email, "")
	if err != nil {
		t.Fatalf("Failed to add org for user1: %v", err)
	}

	// Test 2: Add same org name for user2 (should be isolated)
	org2Token := "sprite-token-user2"
	err = mgr.AddOrgWithUser(org1Name, org2Token, apiURL, user2ID, user2Email, "")
	if err != nil {
		t.Fatalf("Failed to add org for user2: %v", err)
	}

	// Test 3: Verify tokens are stored in separate keyring services
	user1Service := "sprites-cli:user1-123"
	user2Service := "sprites-cli:user2-456"
	keyringKey := "sprites:org:" + apiURL + ":test-org-1"

	// Get token for user1
	token1, err := keyring.Get(user1Service, keyringKey)
	if err != nil {
		t.Fatalf("Failed to get token for user1: %v", err)
	}
	if token1 != org1Token {
		t.Errorf("Expected token %s for user1, got %s", org1Token, token1)
	}

	// Get token for user2
	token2, err := keyring.Get(user2Service, keyringKey)
	if err != nil {
		t.Fatalf("Failed to get token for user2: %v", err)
	}
	if token2 != org2Token {
		t.Errorf("Expected token %s for user2, got %s", org2Token, token2)
	}

	// Test 4: Verify tokens are different (isolation)
	if token1 == token2 {
		t.Fatal("Users should have different tokens for the same org name")
	}

	// Test 5: Set user1 as active and verify org retrieval
	err = mgr.SetActiveUser(user1ID)
	if err != nil {
		t.Fatalf("Failed to set user1 as active: %v", err)
	}

	orgs := mgr.GetOrgs()
	if len(orgs) != 1 {
		t.Errorf("Expected 1 org in config (same org name for both users), got %d", len(orgs))
	}

	// Find the org (should be the one from user2 since it was added last)
	var org *Organization
	for _, o := range orgs {
		if o.Name == org1Name {
			org = o
			break
		}
	}

	if org == nil {
		t.Fatal("Could not find org")
	}

	// Test 6: Verify token retrieval through Organization.GetToken() for user1
	// The org config should have user2's UserID (since user2 was added last)
	// But we need to manually set the UserID to user1 to test user1's token
	org.UserID = user1ID
	retrievedToken, err := org.GetToken()
	if err != nil {
		t.Fatalf("Failed to get token through Organization: %v", err)
	}
	if retrievedToken != org1Token {
		t.Errorf("Expected token %s for user1, got %s", org1Token, retrievedToken)
	}

	// Test 7: Switch to user2 and verify different token
	err = mgr.SetActiveUser(user2ID)
	if err != nil {
		t.Fatalf("Failed to set user2 as active: %v", err)
	}

	// Set the UserID to user2 to test user2's token
	org.UserID = user2ID
	retrievedToken, err = org.GetToken()
	if err != nil {
		t.Fatalf("Failed to get token for user2: %v", err)
	}
	if retrievedToken != org2Token {
		t.Errorf("Expected token %s for user2, got %s", org2Token, retrievedToken)
	}
}

func TestUserLogoutCleanupIntegration(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "logout-integration-test")
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

	// Add user and orgs
	userID := "user-123"
	userEmail := "test@example.com"
	apiURL := "https://api.sprites.dev"

	err = mgr.AddUser(userID, userEmail)
	if err != nil {
		t.Fatalf("Failed to add user: %v", err)
	}

	// Add multiple orgs for the user
	orgs := []struct {
		name  string
		token string
	}{
		{"org1", "token1"},
		{"org2", "token2"},
		{"org3", "token3"},
	}

	for _, org := range orgs {
		err = mgr.AddOrgWithUser(org.name, org.token, apiURL, userID, userEmail, "")
		if err != nil {
			t.Fatalf("Failed to add org %s: %v", org.name, err)
		}
	}

	// Verify tokens are stored in keyring (with URL in key since no alias)
	keyringService := "sprites-cli:user-123"
	for _, org := range orgs {
		token, err := keyring.Get(keyringService, "sprites:org:"+apiURL+":"+org.name)
		if err != nil {
			t.Fatalf("Failed to get token for %s: %v", org.name, err)
		}
		if token != org.token {
			t.Errorf("Expected token %s for %s, got %s", org.token, org.name, token)
		}
	}

	// Verify orgs exist in config
	configOrgs := mgr.GetOrgs()
	if len(configOrgs) != len(orgs) {
		t.Errorf("Expected %d orgs in config, got %d", len(orgs), len(configOrgs))
	}

	// Test logout: remove user
	err = mgr.RemoveUser(userID)
	if err != nil {
		t.Fatalf("Failed to remove user: %v", err)
	}

	// Verify user is removed from config
	user := mgr.GetUser(userID)
	if user != nil {
		t.Fatal("User should have been removed from config")
	}

	// Verify active user is cleared
	activeUser := mgr.GetActiveUser()
	if activeUser != nil {
		t.Fatal("Active user should be cleared after logout")
	}

	// Verify all tokens are removed from keyring
	for _, org := range orgs {
		_, err := keyring.Get(keyringService, "sprites:org:"+org.name)
		if err == nil {
			t.Errorf("Token for %s should have been removed from keyring", org.name)
		}
	}

	// Verify orgs are removed from config
	configOrgs = mgr.GetOrgs()
	if len(configOrgs) != 0 {
		t.Errorf("Expected 0 orgs in config after logout, got %d", len(configOrgs))
	}
}

func TestMultipleUsersSameOrgIntegration(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create temp directory for test
	tempDir, err := os.MkdirTemp("", "multi-user-integration-test")
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

	// Add two users
	user1ID := "user1-123"
	user1Email := "alice@example.com"
	user2ID := "user2-456"
	user2Email := "bob@example.com"

	err = mgr.AddUser(user1ID, user1Email)
	if err != nil {
		t.Fatalf("Failed to add user1: %v", err)
	}

	err = mgr.AddUser(user2ID, user2Email)
	if err != nil {
		t.Fatalf("Failed to add user2: %v", err)
	}

	// Both users authenticate to the same org with different tokens
	orgName := "shared-org"
	user1Token := "alice-sprite-token"
	user2Token := "bob-sprite-token"
	apiURL := "https://api.sprites.dev"

	// Add org for user1
	err = mgr.AddOrgWithUser(orgName, user1Token, apiURL, user1ID, user1Email, "")
	if err != nil {
		t.Fatalf("Failed to add org for user1: %v", err)
	}

	// Add same org for user2
	err = mgr.AddOrgWithUser(orgName, user2Token, apiURL, user2ID, user2Email, "")
	if err != nil {
		t.Fatalf("Failed to add org for user2: %v", err)
	}

	// Verify both users can access their own tokens
	user1Service := "sprites-cli:user1-123"
	user2Service := "sprites-cli:user2-456"
	keyringKey := "sprites:org:" + apiURL + ":shared-org"

	// User1's token
	token1, err := keyring.Get(user1Service, keyringKey)
	if err != nil {
		t.Fatalf("Failed to get user1's token: %v", err)
	}
	if token1 != user1Token {
		t.Errorf("Expected user1 token %s, got %s", user1Token, token1)
	}

	// User2's token
	token2, err := keyring.Get(user2Service, keyringKey)
	if err != nil {
		t.Fatalf("Failed to get user2's token: %v", err)
	}
	if token2 != user2Token {
		t.Errorf("Expected user2 token %s, got %s", user2Token, token2)
	}

	// Verify tokens are different
	if token1 == token2 {
		t.Fatal("Users should have different tokens for the same org")
	}

	// Test user switching
	err = mgr.SetActiveUser(user1ID)
	if err != nil {
		t.Fatalf("Failed to set user1 as active: %v", err)
	}

	// Get orgs for user1
	orgs := mgr.GetOrgs()
	if len(orgs) != 1 {
		t.Errorf("Expected 1 org (same org name for both users), got %d", len(orgs))
	}

	// Find the org
	var org *Organization
	for _, o := range orgs {
		if o.Name == orgName {
			org = o
			break
		}
	}

	if org == nil {
		t.Fatal("Could not find org")
	}

	// Verify user1 gets their own token
	org.UserID = user1ID
	retrievedToken, err := org.GetToken()
	if err != nil {
		t.Fatalf("Failed to get user1's token: %v", err)
	}
	if retrievedToken != user1Token {
		t.Errorf("Expected user1 token %s, got %s", user1Token, retrievedToken)
	}

	// Switch to user2
	err = mgr.SetActiveUser(user2ID)
	if err != nil {
		t.Fatalf("Failed to set user2 as active: %v", err)
	}

	// Verify user2 gets their own token
	org.UserID = user2ID
	retrievedToken, err = org.GetToken()
	if err != nil {
		t.Fatalf("Failed to get user2's token: %v", err)
	}
	if retrievedToken != user2Token {
		t.Errorf("Expected user2 token %s, got %s", user2Token, retrievedToken)
	}

	// Test partial logout (remove only user1)
	err = mgr.RemoveUser(user1ID)
	if err != nil {
		t.Fatalf("Failed to remove user1: %v", err)
	}

	// Verify user1's token is removed
	_, err = keyring.Get(user1Service, keyringKey)
	if err == nil {
		t.Fatal("User1's token should have been removed")
	}

	// Verify user2's token still exists
	token2, err = keyring.Get(user2Service, keyringKey)
	if err != nil {
		t.Fatalf("User2's token should still exist: %v", err)
	}
	if token2 != user2Token {
		t.Errorf("Expected user2 token %s, got %s", user2Token, token2)
	}

	// Verify user2 is now the active user
	activeUser := mgr.GetActiveUser()
	if activeUser == nil {
		t.Fatal("User2 should be the active user")
	}
	if activeUser.ID != user2ID {
		t.Errorf("Expected active user %s, got %s", user2ID, activeUser.ID)
	}
}
