package commands

import (
	"context"
	"flag"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/fly"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
	sprites "github.com/superfly/sprites-go"
)

// LoginCommand handles the login flow using Fly.io authentication
func LoginCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "login",
		Usage:       "login [-o <org>]",
		Description: "Authenticate with Fly.io and create Sprite token",
		FlagSet:     flag.NewFlagSet("login", flag.ContinueOnError),
		Examples: []string{
			"sprite login",
			"sprite login -o my-org",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: login takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Get org override if provided
	orgOverride := ctx.OrgOverride
	if orgOverride == "" && flags.Org != "" {
		orgOverride = flags.Org
	}

	// Parse org with alias if provided
	var aliasOverride string
	if orgOverride != "" {
		orgName, alias, hasAlias := ctx.ConfigMgr.ParseOrgWithAlias(orgOverride)
		if hasAlias {
			orgOverride = orgName
			aliasOverride = alias
		}
	}

	// Create fly manager
	flyMgr := fly.NewManager(ctx.ConfigMgr)

	authCtx, cancel := context.WithTimeout(context.Background(), 20*time.Minute)
	defer cancel()

	fmt.Println("🚀 Starting Fly.io authentication...")
	fmt.Println()

	// Step 1: Try to get or fetch organizations
	var flyToken string
	var flyOrgs []fly.Organization

	flyToken, _, err = fly.ReadFlyToken()
	if err != nil {
		if err == fly.ErrNoToken {
			// No token found - run web-based login flow
			fmt.Println("No user information found locally. Starting login...")

			flyToken, err = RunWebLoginForFlyToken(authCtx)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
		} else {
			fmt.Fprintf(os.Stderr, "Error: Failed to read Fly token: %v\n", err)
			os.Exit(1)
		}
	}

	// Step 1.5: Get user info for user-scoped keyring
	fmt.Print("Getting user info...")
	user, err := fly.GetCurrentUser(authCtx, flyToken)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		fmt.Fprintf(os.Stderr, "Error: Failed to get user info: %v\n", err)
		os.Exit(1)
	}
	fmt.Print("\r\033[K") // Clear the line

	// Store Fly token using envelope encryption
	// The token is encrypted with AES-256-GCM and stored in ~/.sprites/fly-auth/<id>.enc
	// The encryption key is stored in the keyring
	if err := fly.StoreFlyTokenEncrypted(user.ID, flyToken); err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Failed to store Fly token: %v\n", err)
		// Continue anyway - not fatal
	}

	// Step 2: Fetch organizations
	fmt.Print("Fetching organizations...")
	flyOrgs, err = flyMgr.FetchOrganizations(authCtx, flyToken)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		fmt.Fprintf(os.Stderr, "Error: Failed to fetch organizations: %v\n", err)
		os.Exit(1)
	}
	fmt.Print("\r\033[K") // Clear the line

	if len(flyOrgs) == 0 {
		fmt.Println("No organizations found in your Fly.io account.")
		os.Exit(1)
	}

	fmt.Printf("✓ Found %d organization(s)\n", len(flyOrgs))
	fmt.Println()

	// Step 3: Select organization
	var selectedOrg *fly.Organization
	if orgOverride != "" {
		// Try to find the specified org
		for i, org := range flyOrgs {
			if org.Slug == orgOverride {
				selectedOrg = &flyOrgs[i]
				break
			}
		}
		if selectedOrg == nil {
			// With alias, just use the first org
			if aliasOverride != "" && len(flyOrgs) > 0 {
				selectedOrg = &flyOrgs[0]
			} else {
				fmt.Fprintf(os.Stderr, "Error: Organization '%s' not found in your Fly.io account\n", orgOverride)
				os.Exit(1)
			}
		}
		fmt.Printf("Using organization: %s\n", format.Org(selectedOrg.Slug))
	} else {
		// Convert to prompts.FlyOrganization for selection
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

		promptOrg, err := prompts.PromptForFlyOrganization(promptOrgs)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}

		// Convert back to fly.Organization
		for i, org := range flyOrgs {
			if org.Slug == promptOrg.Slug {
				selectedOrg = &flyOrgs[i]
				break
			}
		}
	}

	// Step 4: Create Sprite token using Fly token
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
				fmt.Fprintf(os.Stderr, "Error: Organization requires an invite code: %v\n", promptErr)
				os.Exit(1)
			}

			// Retry with invite code
			fmt.Printf("Creating Sprite token with invite code...")
			spriteToken, err = sprites.CreateToken(authCtx, flyToken, selectedOrg.Slug, inviteCode)
			if err != nil {
				fmt.Print("\r\033[K") // Clear the line
				fmt.Fprintf(os.Stderr, "Error: Failed to create Sprite token: %v\n", err)
				os.Exit(1)
			}
		} else {
			fmt.Fprintf(os.Stderr, "Error: Failed to create Sprite token: %v\n", err)
			os.Exit(1)
		}
	}
	fmt.Print("\r\033[K") // Clear the line

	// Step 5: Store the organization with user-scoped token storage
	apiURL := "https://api.sprites.dev"
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		apiURL = envURL
	}

	// Handle alias if provided
	if aliasOverride != "" {
		url, exists := ctx.ConfigMgr.GetURLForAlias(aliasOverride)
		if !exists {
			// Get all configured URLs
			urls := ctx.ConfigMgr.GetAllURLs()
			if len(urls) == 0 {
				// No URLs configured yet, use the default
				url = apiURL
			} else {
				// Prompt user to select URL for this alias
				selectedURL, err := prompts.SelectURLForAlias(aliasOverride, urls)
				if err != nil {
					fmt.Fprintf(os.Stderr, "Error: Failed to select URL for alias: %v\n", err)
					os.Exit(1)
				}
				url = selectedURL
			}
			// Save the alias
			if err := ctx.ConfigMgr.SetURLAlias(aliasOverride, url); err != nil {
				fmt.Fprintf(os.Stderr, "Error: Failed to save alias: %v\n", err)
				os.Exit(1)
			}
			fmt.Printf("✓ Saved alias '%s' for URL %s\n", aliasOverride, format.URL(url))
		}
		apiURL = url
	}

	fmt.Printf("✓ Using API URL: %s\n", format.URL(apiURL))

	// Add the organization with user-scoped token storage
	if err := ctx.ConfigMgr.AddOrgWithUser(selectedOrg.Slug, spriteToken, apiURL, user.ID, user.Email, aliasOverride); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to save credentials: %v\n", err)
		os.Exit(1)
	}

	// Set as current org
	if err := ctx.ConfigMgr.SetCurrentOrg(selectedOrg.Slug); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to set current organization: %v\n", err)
		os.Exit(1)
	}

	fmt.Println()
	fmt.Println(format.Success("✓ Successfully authenticated with Fly.io!"))
	fmt.Printf("✓ Organization: %s\n", format.Org(selectedOrg.Slug))
	if aliasOverride != "" {
		fmt.Printf("✓ Available as: %s:%s\n", aliasOverride, selectedOrg.Slug)
	}
	fmt.Println(format.Success("✓ Ready to work with Sprites!"))
	fmt.Println()
}

// RunWebLoginForFlyToken runs the web-based login flow to get a Fly.io token
func RunWebLoginForFlyToken(ctx context.Context) (string, error) {
	// Get hostname for session
	hostname, err := getHostname()
	if err != nil {
		hostname = "sprite-cli"
	}

	// Start CLI session
	fmt.Print("Starting authentication session...")
	session, err := fly.StartCLISession(hostname, map[string]interface{}{
		"signup": false,
		"target": "auth",
	})
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		return "", fmt.Errorf("failed to start login session: %w", err)
	}
	fmt.Print("\r\033[K") // Clear the line

	// Open browser
	fmt.Printf("Opening %s in your browser...\n\n", session.URL)
	if err := openBrowser(session.URL); err != nil {
		fmt.Printf("Failed to open browser automatically. Please visit this URL:\n%s\n\n", session.URL)
	}

	// Wait for authentication
	fmt.Println("Waiting for authentication...")
	token, err := fly.WaitForCLISession(ctx, session.ID)
	if err != nil {
		return "", fmt.Errorf("authentication failed: %w", err)
	}

	// Get user info to display
	user, err := fly.GetCurrentUser(ctx, token)
	if err != nil {
		// Don't fail on this, just log it
		fmt.Println("Authentication successful")
	} else {
		fmt.Printf("Authenticated as: %s\n", user.Email)
	}

	return token, nil
}

// getHostname returns a hostname for CLI sessions
func getHostname() (string, error) {
	hostname, err := os.Hostname()
	if err != nil {
		return "", err
	}
	return hostname, nil
}
