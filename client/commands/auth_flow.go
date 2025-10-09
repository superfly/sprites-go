package commands

import (
	"context"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/fly"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
	sprites "github.com/superfly/sprites-go"
)

// IsTTY checks if stdout is a terminal (not a pipe)
func IsTTY() bool {
	fileInfo, err := os.Stdout.Stat()
	if err != nil {
		return false
	}
	return (fileInfo.Mode() & os.ModeCharDevice) != 0
}

// EnsureAuthenticated ensures a user is authenticated and returns their org and client
// This is a reusable component that:
// 1. Checks if user is already authenticated
// 2. Runs login flow if necessary
// 3. Shows org selector if needed
// 4. Returns the selected org and configured client
func EnsureAuthenticated(ctx *GlobalContext, orgOverride string) (*config.Organization, *sprites.Client, error) {
	// Check if we have a current user
	activeUser := ctx.ConfigMgr.GetActiveUser()

	// If no active user or org override is provided, try to get org from existing config
	if activeUser != nil && orgOverride == "" {
		// Try to use existing org
		org, client, err := GetOrgAndClient(ctx, orgOverride)
		if err == nil {
			return org, client, nil
		}
		// If we couldn't get org/client, fall through to login flow
	}

	// Need to authenticate
	fmt.Println("Authentication required...")
	org, err := AuthenticateWithFly(ctx.ConfigMgr, orgOverride, "", "")
	if err != nil {
		return nil, nil, fmt.Errorf("authentication failed: %w", err)
	}

	// Get client
	token, err := org.GetToken()
	if err != nil {
		return nil, nil, fmt.Errorf("failed to get auth token: %w", err)
	}

	client := sprites.New(token, sprites.WithBaseURL(getSpritesAPIURL(org)))

	return org, client, nil
}

// PromptForSpriteName prompts the user for a sprite name if not provided
func PromptForSpriteName() (string, error) {
	fmt.Print("Enter sprite name: ")
	var name string
	if _, err := fmt.Scanln(&name); err != nil {
		return "", fmt.Errorf("failed to read sprite name: %w", err)
	}

	name = strings.TrimSpace(name)
	if name == "" {
		return "", fmt.Errorf("sprite name cannot be empty")
	}

	return name, nil
}

// SelectOrganization shows the org selector and authenticates with the selected org
// Returns the selected organization and configured client
func SelectOrganization(ctx *GlobalContext) (*config.Organization, *sprites.Client, error) {
	authCtx, cancel := context.WithTimeout(context.Background(), 20*time.Minute)
	defer cancel()

	// Get Fly token
	flyToken, _, err := fly.ReadFlyToken()
	if err != nil {
		if err == fly.ErrNoToken {
			// No token found - run web-based login flow
			fmt.Println("No user information found locally. Starting login...")
			flyToken, err = RunWebLoginForFlyToken(authCtx)
			if err != nil {
				return nil, nil, fmt.Errorf("web login failed: %w", err)
			}
		} else {
			return nil, nil, fmt.Errorf("failed to read Fly token: %w", err)
		}
	}

	// Get user info
	fmt.Print("Getting user info...")
	user, err := fly.GetCurrentUser(authCtx, flyToken)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		return nil, nil, fmt.Errorf("failed to get user info: %w", err)
	}
	fmt.Print("\r\033[K") // Clear the line

	// Store Fly token using envelope encryption
	if err := fly.StoreFlyTokenEncrypted(user.ID, flyToken); err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Failed to store Fly token: %v\n", err)
	}

	// Fetch organizations
	fmt.Print("Fetching organizations...")
	flyMgr := fly.NewManager(ctx.ConfigMgr)
	flyOrgs, err := flyMgr.FetchOrganizations(authCtx, flyToken)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		return nil, nil, fmt.Errorf("failed to fetch organizations: %w", err)
	}
	fmt.Print("\r\033[K") // Clear the line

	if len(flyOrgs) == 0 {
		return nil, nil, fmt.Errorf("no organizations found in your Fly.io account")
	}

	fmt.Printf("✓ Found %d organization(s)\n", len(flyOrgs))
	fmt.Println()

	// Convert to prompts format
	promptOrgs := make([]prompts.FlyOrganization, len(flyOrgs))
	for i, org := range flyOrgs {
		promptOrgs[i] = prompts.FlyOrganization{
			ID:     org.ID,
			Slug:   org.Slug,
			Name:   org.Name,
			Type:   org.Type,
			Status: org.Status,
		}
	}

	// Prompt for organization selection
	selectedOrg, err := prompts.PromptForFlyOrganization(promptOrgs)
	if err != nil {
		return nil, nil, fmt.Errorf("organization selection cancelled: %w", err)
	}

	// Create Sprite token
	fmt.Printf("\nCreating Sprite token for organization %s...\n", format.Org(selectedOrg.Slug))

	spriteToken, err := sprites.CreateToken(authCtx, flyToken, selectedOrg.Slug, "")
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line

		// Check if invite code is needed
		errStr := err.Error()
		if strings.Contains(errStr, "401") || strings.Contains(errStr, "403") ||
			strings.Contains(errStr, "Sprites not enabled") || strings.Contains(errStr, "Forbidden") {

			// Prompt for invite code
			inviteCode, promptErr := prompts.PromptForInviteCode()
			if promptErr != nil {
				return nil, nil, fmt.Errorf("organization requires an invite code: %w", promptErr)
			}

			// Retry with invite code
			fmt.Printf("Creating Sprite token with invite code...")
			spriteToken, err = sprites.CreateToken(authCtx, flyToken, selectedOrg.Slug, inviteCode)
			if err != nil {
				fmt.Print("\r\033[K") // Clear the line
				return nil, nil, fmt.Errorf("failed to create Sprite token: %w", err)
			}
		} else {
			return nil, nil, fmt.Errorf("failed to create Sprite token: %w", err)
		}
	}
	fmt.Print("\r\033[K") // Clear the line

	// Determine API URL
	apiURL := "https://api.sprites.dev"
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		apiURL = envURL
	}

	fmt.Printf("✓ Using API URL: %s\n", format.URL(apiURL))

	// Add the organization with user-scoped token storage
	if err := ctx.ConfigMgr.AddOrgWithUser(selectedOrg.Slug, spriteToken, apiURL, user.ID, user.Email); err != nil {
		return nil, nil, fmt.Errorf("failed to save organization: %w", err)
	}

	// Set as current org
	if err := ctx.ConfigMgr.SetCurrentOrg(selectedOrg.Slug); err != nil {
		return nil, nil, fmt.Errorf("failed to set current org: %w", err)
	}

	fmt.Printf("%s Authenticated as organization: %s\n\n", format.Success("✓"), format.Org(selectedOrg.Slug))

	// Return the org and client
	org, client, err := GetOrgAndClient(ctx, selectedOrg.Slug)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to get org and client: %w", err)
	}

	return org, client, nil
}
