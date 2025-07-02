package config

import (
	"testing"

	"github.com/zalando/go-keyring"
)

func TestKeyringIntegration(t *testing.T) {
	// Create a test organization
	org := &Organization{
		Name: "test-org",
		URL:  "https://api.test.dev",
	}

	testToken := "test-token-12345"

	// Test 1: SetToken should try keyring first
	err := org.SetToken(testToken)
	if err != nil {
		t.Fatalf("SetToken failed: %v", err)
	}

	// Test 2: GetToken should retrieve the token
	retrievedToken, err := org.GetToken()
	if err != nil {
		t.Fatalf("GetToken failed: %v", err)
	}

	if retrievedToken != testToken {
		t.Errorf("Expected token %s, got %s", testToken, retrievedToken)
	}

	// Test 3: Check if we're using keyring or file storage
	t.Logf("Organization is using keyring: %v", org.UseKeyring)
	t.Logf("File-stored token: %q", org.Token)

	// Clean up - delete from keyring
	_ = org.DeleteToken()
}

func TestKeyringFallback(t *testing.T) {
	// Create a test organization
	org := &Organization{
		Name: "fallback-test-org",
		URL:  "https://api.test.dev",
	}

	testToken := "fallback-token-67890"

	// Simulate keyring being unavailable by using mock
	keyring.MockInit()

	// Test SetToken with mock (should succeed)
	err := org.SetToken(testToken)
	if err != nil {
		t.Fatalf("SetToken failed with mock: %v", err)
	}

	// Test GetToken with mock
	retrievedToken, err := org.GetToken()
	if err != nil {
		t.Fatalf("GetToken failed with mock: %v", err)
	}

	if retrievedToken != testToken {
		t.Errorf("Expected token %s, got %s", testToken, retrievedToken)
	}

	t.Logf("Mock keyring test - Organization is using keyring: %v", org.UseKeyring)

	// Clean up
	_ = org.DeleteToken()
}

func TestBackwardCompatibility(t *testing.T) {
	// Create a test organization with a pre-existing file-stored token
	org := &Organization{
		Name:       "legacy-org",
		URL:        "https://api.legacy.dev",
		Token:      "legacy-file-token",
		UseKeyring: false,
	}

	// GetToken should return the file-stored token
	retrievedToken, err := org.GetToken()
	if err != nil {
		t.Fatalf("GetToken failed for legacy org: %v", err)
	}

	if retrievedToken != "legacy-file-token" {
		t.Errorf("Expected legacy token 'legacy-file-token', got %s", retrievedToken)
	}

	t.Logf("Legacy org is using keyring: %v", org.UseKeyring)
}

func TestEnhancedCredentialManagement(t *testing.T) {
	// Initialize mock keyring for consistent testing
	keyring.MockInit()

	// Create a test organization
	org := &Organization{
		Name: "enhanced-test-org",
		URL:  "https://api.enhanced.dev",
	}

	// Test storing different credential types
	testCredentials := map[CredentialType]string{
		CredentialTypeToken:  "token-12345",
		CredentialTypeAPIKey: "apikey-67890",
		CredentialTypeCert:   "cert-abcdef",
		CredentialTypeSSHKey: "ssh-key-ghijkl",
	}

	// Store all credential types
	for credType, credential := range testCredentials {
		err := org.SetCredential(credType, credential)
		if err != nil {
			t.Fatalf("Failed to set %s: %v", credType, err)
		}
	}

	// Retrieve and verify all credential types
	for credType, expectedCredential := range testCredentials {
		retrievedCredential, err := org.GetCredential(credType)
		if err != nil {
			t.Fatalf("Failed to get %s: %v", credType, err)
		}
		if retrievedCredential != expectedCredential {
			t.Errorf("Expected %s %s, got %s", credType, expectedCredential, retrievedCredential)
		}
	}

	// Test listing credential types
	credTypes := org.ListCredentialTypes()
	if len(credTypes) != len(testCredentials) {
		t.Errorf("Expected %d credential types, got %d", len(testCredentials), len(credTypes))
	}

	// Test getting all credentials
	allCreds := org.GetAllCredentials()
	if len(allCreds) != len(testCredentials) {
		t.Errorf("Expected %d credentials in map, got %d", len(testCredentials), len(allCreds))
	}

	// Test deleting specific credential types
	err := org.DeleteCredential(CredentialTypeAPIKey)
	if err != nil {
		t.Fatalf("Failed to delete API key: %v", err)
	}

	// Verify it's actually deleted
	_, err = org.GetCredential(CredentialTypeAPIKey)
	if err == nil {
		t.Error("Expected API key to be deleted, but it still exists")
	}

	// Clean up remaining credentials
	for credType := range testCredentials {
		if credType != CredentialTypeAPIKey { // Already deleted
			_ = org.DeleteCredential(credType)
		}
	}
}

func TestManagerSearchFunctions(t *testing.T) {
	// Initialize mock keyring
	keyring.MockInit()

	// Create a test manager
	cfg, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Add test organizations
	testOrgs := map[string]struct {
		name  string
		token string
		url   string
	}{
		"org1": {"test-org-1", "token-111", "https://api.test1.dev"},
		"org2": {"test-org-2", "token-222", "https://api.test2.dev"},
		"org3": {"test-org-3", "token-333", "https://api.test1.dev"}, // Same URL as org1
	}

	for _, orgData := range testOrgs {
		err := cfg.AddOrg(orgData.name, orgData.token, orgData.url)
		if err != nil {
			t.Fatalf("Failed to add org %s: %v", orgData.name, err)
		}
	}

	// Test FindOrgByToken
	org, orgName, err := cfg.FindOrgByToken("token-222")
	if err != nil {
		t.Fatalf("Failed to find org by token: %v", err)
	}
	if orgName != "test-org-2" {
		t.Errorf("Expected org name 'test-org-2', got '%s'", orgName)
	}
	if org.Name != "test-org-2" {
		t.Errorf("Expected org name 'test-org-2', got '%s'", org.Name)
	}

	// Test SearchOrgsByURL
	orgsWithSameURL := cfg.SearchOrgsByURL("https://api.test1.dev")
	if len(orgsWithSameURL) != 2 {
		t.Errorf("Expected 2 orgs with same URL, got %d", len(orgsWithSameURL))
	}

	// Test SearchOrgsByCredential
	orgsWithToken := cfg.SearchOrgsByCredential(CredentialTypeToken, "token-111")
	if len(orgsWithToken) != 1 {
		t.Errorf("Expected 1 org with token-111, got %d", len(orgsWithToken))
	}
	if len(orgsWithToken) > 0 && orgsWithToken[0].Name != "test-org-1" {
		t.Errorf("Expected org 'test-org-1', got '%s'", orgsWithToken[0].Name)
	}

	// Test searching for non-existent token
	_, _, err = cfg.FindOrgByToken("non-existent-token")
	if err == nil {
		t.Error("Expected error when searching for non-existent token")
	}

	// Clean up
	for orgName := range testOrgs {
		_ = cfg.RemoveOrg(orgName)
	}
}

func TestCredentialKeyStructure(t *testing.T) {
	// Test buildKeyringKey function
	orgName := "test-org"

	// Token should use just the org name for backward compatibility
	tokenKey := buildKeyringKey(orgName, CredentialTypeToken)
	if tokenKey != orgName {
		t.Errorf("Expected token key to be '%s', got '%s'", orgName, tokenKey)
	}

	// Other credential types should include the type
	apiKeyKey := buildKeyringKey(orgName, CredentialTypeAPIKey)
	expectedAPIKeyKey := "test-org:api-key"
	if apiKeyKey != expectedAPIKeyKey {
		t.Errorf("Expected API key to be '%s', got '%s'", expectedAPIKeyKey, apiKeyKey)
	}

	certKey := buildKeyringKey(orgName, CredentialTypeCert)
	expectedCertKey := "test-org:certificate"
	if certKey != expectedCertKey {
		t.Errorf("Expected cert key to be '%s', got '%s'", expectedCertKey, certKey)
	}
}
