package commands

import (
    "os"
    "testing"

    "github.com/zalando/go-keyring"
    "github.com/superfly/sprite-env/client/config"
)

func setupTempHome(t *testing.T) string {
    t.Helper()
    tempDir, err := os.MkdirTemp("", "sprite-client-test")
    if err != nil {
        t.Fatalf("Failed to create temp dir: %v", err)
    }
    t.Cleanup(func() { os.RemoveAll(tempDir) })
    originalHome := os.Getenv("HOME")
    os.Setenv("HOME", tempDir)
    t.Cleanup(func() { os.Setenv("HOME", originalHome) })
    return tempDir
}

func newTestContext(t *testing.T) *GlobalContext {
    keyring.MockInit()
    setupTempHome(t)
    mgr, err := config.NewManager()
    if err != nil {
        t.Fatalf("failed to create manager: %v", err)
    }
    return &GlobalContext{ConfigMgr: mgr}
}

// These tests avoid importing the go SDK by calling the internal getOrganization function

func TestOrgOverrideWithAlias_LooksUpApiAndOrg(t *testing.T) {
    ctx := newTestContext(t)

    // Prepare config: URL and org
    const stagingURL = "https://staging-api.sprites.dev"
    if err := ctx.ConfigMgr.AddSprite(stagingURL, "acme", "acme", "token-staging"); err != nil {
        t.Fatalf("failed to add staging sprite: %v", err)
    }

    // Map alias -> URL
    if err := ctx.ConfigMgr.SetURLAlias("staging", stagingURL); err != nil {
        t.Fatalf("failed to set URL alias: %v", err)
    }

    org, err := getOrganization(ctx, "staging:acme")
    if err != nil {
        t.Fatalf("getOrganization error: %v", err)
    }
    if org == nil || org.Name != "acme" || org.URL != stagingURL {
        t.Fatalf("expected org=acme at %s, got %+v", stagingURL, org)
    }
}

func TestOrgOverrideWithoutAlias_DefaultsToPublicAPI(t *testing.T) {
    ctx := newTestContext(t)

    const defaultURL = "https://api.sprites.dev"
    const otherURL = "https://staging-api.sprites.dev"

    // Add orgs under two URLs
    if err := ctx.ConfigMgr.AddSprite(defaultURL, "acme", "acme", "token-default"); err != nil {
        t.Fatalf("failed to add default sprite: %v", err)
    }
    if err := ctx.ConfigMgr.AddSprite(otherURL, "acme", "acme", "token-other"); err != nil {
        t.Fatalf("failed to add other sprite: %v", err)
    }

    org, err := getOrganization(ctx, "acme")
    if err != nil {
        t.Fatalf("getOrganization error: %v", err)
    }
    if org.URL != defaultURL {
        t.Fatalf("expected default API %s, got %s", defaultURL, org.URL)
    }
}

func TestSPRITE_ORG_UsedWhenNoFlag(t *testing.T) {
    ctx := newTestContext(t)

    const defaultURL = "https://api.sprites.dev"
    if err := ctx.ConfigMgr.AddSprite(defaultURL, "acme", "acme", "token-default"); err != nil {
        t.Fatalf("failed to add default sprite: %v", err)
    }

    os.Setenv("SPRITE_ORG", "acme")
    t.Cleanup(func() { os.Unsetenv("SPRITE_ORG") })

    org, err := getOrganization(ctx, "")
    if err != nil {
        t.Fatalf("getOrganization error: %v", err)
    }
    if org.Name != "acme" || org.URL != defaultURL {
        t.Fatalf("expected org=acme under %s, got %+v", defaultURL, org)
    }
}

func TestNoFlag_DefaultsPrefersDefaultAPIOrFirstAvailable(t *testing.T) {
    ctx := newTestContext(t)

    const defaultURL = "https://api.sprites.dev"
    const otherURL = "https://staging-api.sprites.dev"
    if err := ctx.ConfigMgr.AddSprite(otherURL, "org1", "org1", "token1"); err != nil {
        t.Fatalf("failed to add sprite: %v", err)
    }
    if err := ctx.ConfigMgr.AddSprite(defaultURL, "org2", "org2", "token2"); err != nil {
        t.Fatalf("failed to add sprite: %v", err)
    }

    org, err := getOrganization(ctx, "")
    if err != nil {
        t.Fatalf("getOrganization error: %v", err)
    }
    if org.URL != defaultURL {
        t.Fatalf("expected default API %s, got %s", defaultURL, org.URL)
    }
}
