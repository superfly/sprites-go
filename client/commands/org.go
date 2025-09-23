package commands

import (
	"flag"
	"fmt"
	"os"

	"log/slog"
	"strings"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
)

// OrgCommand handles organization-related commands
func OrgCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "org",
		Usage:       "org <subcommand> [options]",
		Description: "Manage organizations and API tokens",
		FlagSet:     flag.NewFlagSet("org", flag.ContinueOnError),
		Examples: []string{
			"sprite org auth",
			"sprite org list",
			"sprite org logout",
			"sprite org keyring status",
			"sprite org keyring disable",
		},
	}

	// Set up global flags for the main org command
	_ = NewGlobalFlags(cmd.FlagSet)

	// Custom usage to show subcommands
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		fmt.Fprintf(os.Stderr, "Subcommands:\n")
		fmt.Fprintf(os.Stderr, "  auth      Add an API token\n")
		fmt.Fprintf(os.Stderr, "  list      Show configured tokens\n")
		fmt.Fprintf(os.Stderr, "  logout    Remove all tokens\n")
		fmt.Fprintf(os.Stderr, "  keyring   Enable/disable keyring usage\n\n")
		fmt.Fprintf(os.Stderr, "Options:\n")
		cmd.FlagSet.PrintDefaults()
		fmt.Fprintln(os.Stderr)
		if len(cmd.Examples) > 0 {
			fmt.Fprintf(os.Stderr, "Examples:\n")
			for _, example := range cmd.Examples {
				fmt.Fprintf(os.Stderr, "  %s\n", example)
			}
			fmt.Fprintln(os.Stderr)
		}
	}

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) < 1 {
		fmt.Fprintf(os.Stderr, "Error: org requires a subcommand\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	subcommand := remainingArgs[0]
	subArgs := remainingArgs[1:]

	switch subcommand {
	case "auth":
		orgAuthCommand(ctx, subArgs)
	case "list", "ls":
		orgListCommand(ctx.ConfigMgr, subArgs)
	case "logout":
		orgLogoutCommand(ctx.ConfigMgr, subArgs)
	case "keyring":
		orgKeyringCommand(ctx.ConfigMgr, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown org subcommand '%s'\n\n", subcommand)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}
}

func orgAuthCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "org auth",
		Usage:       "org auth [api-url] [-o <api>:<org>]",
		Description: "Add an API token",
		FlagSet:     flag.NewFlagSet("org auth", flag.ContinueOnError),
		Examples: []string{
			"sprite org auth",
			"sprite org auth https://custom-api.sprites.dev",
			"sprite org auth -o prod:my-org",
			"sprite org auth -o staging:test-org",
			"sprite org auth https://staging-api.sprites.dev -o staging:test-org",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Check for optional API URL argument
	var apiURLOverride string
	if len(remainingArgs) > 0 {
		// Check if the first argument looks like a URL
		possibleURL := remainingArgs[0]
		if strings.HasPrefix(possibleURL, "http://") || strings.HasPrefix(possibleURL, "https://") {
			apiURLOverride = possibleURL
			remainingArgs = remainingArgs[1:]
		}
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: unexpected argument '%s'\n\n", remainingArgs[0])
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Parse org override if provided
	var orgOverride string
	var aliasOverride string
	// First check the global context for org override
	orgSpec := ctx.OrgOverride
	if orgSpec == "" && flags.Org != "" {
		// If not in global context, check local flags (shouldn't happen but just in case)
		orgSpec = flags.Org
	}

	if orgSpec != "" {
		orgName, alias, hasAlias := ctx.ConfigMgr.ParseOrgWithAlias(orgSpec)
		if hasAlias {
			orgOverride = orgName
			aliasOverride = alias
		} else {
			// Just an org name, no alias
			orgOverride = orgSpec
		}
	}

	// Try Fly authentication
	org, err := AuthenticateWithFly(ctx.ConfigMgr, orgOverride, aliasOverride, apiURLOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Set as current org
	if err := ctx.ConfigMgr.SetCurrentOrg(org.Name); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to set current organization: %v\n", err)
		os.Exit(1)
	}
}

// AuthenticateWithFly handles the Fly.io authentication flow
func AuthenticateWithFly(cfg *config.Manager, orgOverride string, aliasOverride string, apiURLOverride string) (*config.Organization, error) {
	fmt.Println("🚀 Checking for Fly.io authentication...")
	slog.Debug("Starting Fly.io authentication flow", "orgOverride", orgOverride, "aliasOverride", aliasOverride, "apiURLOverride", apiURLOverride)

	// Get Fly token
	flyToken, source, err := GetFlyToken()
	if err != nil {
		slog.Debug("Failed to get Fly token", "error", err)
		// Check if flyctl is installed
		if CheckFlyctlInstalled() {
			return nil, fmt.Errorf("no Fly.io authentication found. Please run 'flyctl auth login' first")
		}
		return nil, fmt.Errorf("flyctl is not installed. Please install flyctl from https://fly.io/docs/flyctl/install/ and run 'flyctl auth login' to authenticate")
	}

	// Print where credentials were found
	if strings.HasPrefix(source, "FLY_") {
		fmt.Printf("Using Fly credentials from %s\n", source)
	} else {
		fmt.Printf("Using Fly credentials from %s\n", source)
	}

	slog.Debug("Successfully retrieved Fly token", "token_prefix", flyToken[:10]+"...", "token_length", len(flyToken), "source", source)
	fmt.Print("Fetching organizations...")

	// Fetch organizations
	flyOrgs, err := FetchFlyOrganizations(flyToken)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		slog.Debug("Failed to fetch organizations", "error", err)
		return nil, fmt.Errorf("failed to fetch Fly.io organizations: %w", err)
	}
	fmt.Print("\r\033[K") // Clear the line

	if len(flyOrgs) == 0 {
		slog.Debug("No organizations found in Fly account")
		return nil, fmt.Errorf("no organizations found in your Fly.io account")
	}

	slog.Debug("Successfully fetched organizations", "count", len(flyOrgs))
	fmt.Printf("✓ Found %d organization(s)\n", len(flyOrgs))
	fmt.Println()

	// Convert FlyOrganization to prompts.FlyOrganization
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

	// Check if org was specified via command line
	var selectedOrg *prompts.FlyOrganization
	if orgOverride != "" {
		// When using alias syntax (e.g., alpha:kurt), the org part might not be a real Fly org
		// In this case, just use the first available org or let user pick one specific org
		if aliasOverride != "" {
			// Using alias:org syntax - just pick the first org or the one that matches if it exists
			for i, org := range promptOrgs {
				if org.Slug == orgOverride {
					selectedOrg = &promptOrgs[i]
					break
				}
			}
			// If no exact match found with alias syntax, use the first org
			if selectedOrg == nil && len(promptOrgs) > 0 {
				selectedOrg = &promptOrgs[0]
				slog.Debug("Using first available organization with alias", "slug", selectedOrg.Slug, "alias", aliasOverride)
			}
		} else {
			// Just -o <org> without alias - find the exact org
			for i, org := range promptOrgs {
				if org.Slug == orgOverride {
					selectedOrg = &promptOrgs[i]
					break
				}
			}
			if selectedOrg == nil {
				return nil, fmt.Errorf("organization '%s' not found in your Fly.io account", orgOverride)
			}
		}
		slog.Debug("Using specified organization", "slug", selectedOrg.Slug, "name", selectedOrg.Name)
		fmt.Printf("Using organization: %s\n", format.Org(selectedOrg.Slug))
	} else {
		// Let user select organization
		var err error
		selectedOrg, err = prompts.PromptForFlyOrganization(promptOrgs)
		if err != nil {
			slog.Debug("Organization selection cancelled", "error", err)
			return nil, err
		}
		slog.Debug("Organization selected", "slug", selectedOrg.Slug, "name", selectedOrg.Name)
	}

	fmt.Printf("\nCreating Sprite token for organization %s...", format.Org(selectedOrg.Slug))

	// Create sprite token
	spriteToken, err := CreateSpriteToken(flyToken, selectedOrg.Slug)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		slog.Debug("Failed to create sprite token", "error", err)
		return nil, fmt.Errorf("failed to create Sprite token: %w", err)
	}
	fmt.Print("\r\033[K") // Clear the line

	// Store the organization
	// Priority: command-line arg > environment variable > default
	apiURL := "https://api.sprites.dev"
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		apiURL = envURL
		slog.Debug("Using custom API URL from environment", "url", apiURL)
	}
	if apiURLOverride != "" {
		apiURL = apiURLOverride
		slog.Debug("Using API URL from command line", "url", apiURL)
	}

	// Handle alias if provided
	if aliasOverride != "" {
		// Check if we need to prompt for URL selection
		url, exists := cfg.GetURLForAlias(aliasOverride)
		if !exists {
			// Get all configured URLs
			urls := cfg.GetAllURLs()
			if len(urls) == 0 {
				// No URLs configured yet, use the default
				url = apiURL
			} else {
				// Prompt user to select URL for this alias
				selectedURL, err := prompts.SelectURLForAlias(aliasOverride, urls)
				if err != nil {
					return nil, fmt.Errorf("failed to select URL for alias: %w", err)
				}
				url = selectedURL
			}
			// Save the alias
			if err := cfg.SetURLAlias(aliasOverride, url); err != nil {
				return nil, fmt.Errorf("failed to save alias: %w", err)
			}
			fmt.Printf("✓ Saved alias '%s' for URL %s\n", aliasOverride, format.URL(url))
		}
		apiURL = url
	}

	// Print the API URL being used
	fmt.Printf("Using API URL: %s\n", format.URL(apiURL))

	// Add the organization with the Fly org name (uses keyring by default)
	slog.Debug("Saving organization", "name", selectedOrg.Slug, "url", apiURL)
	if err := cfg.AddOrg(selectedOrg.Slug, spriteToken, apiURL); err != nil {
		slog.Debug("Failed to save organization", "error", err)
		return nil, fmt.Errorf("failed to save credentials: %w", err)
	}

	fmt.Println(format.Success("✓ Authenticated with Fly.io organization: " + format.Org(selectedOrg.Slug)))
	if aliasOverride != "" {
		fmt.Printf("✓ Organization available as: %s:%s\n", aliasOverride, selectedOrg.Slug)
	}
	fmt.Println(format.Success("✓ Ready to work with Sprites!") + "\n")

	// Return the newly added org
	orgs := cfg.GetOrgs()
	return orgs[selectedOrg.Slug], nil
}

func orgListCommand(cfg *config.Manager, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "org list",
		Usage:       "org list",
		Description: "Show configured tokens",
		FlagSet:     flag.NewFlagSet("org list", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: org list takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	orgs := cfg.GetOrgs()
	slog.Debug("Loaded organizations from config", "count", len(orgs))

	// If no organizations in config, try to discover from Fly API
	if len(orgs) == 0 {
		fmt.Println("No organizations found in config. Checking Fly.io account...")

		// Get Fly token
		flyToken, source, err := GetFlyToken()
		if err != nil {
			slog.Debug("Failed to get Fly token", "error", err)
			fmt.Println("No API tokens configured.")
			fmt.Println("Run 'sprite org auth' to add one.")
			return
		}

		slog.Debug("Found Fly token", "source", source)

		// Fetch organizations from Fly API
		flyOrgs, err := FetchFlyOrganizations(flyToken)
		if err != nil {
			slog.Debug("Failed to fetch organizations", "error", err)
			fmt.Printf("Failed to fetch organizations from Fly.io: %v\n", err)
			fmt.Println("Run 'sprite org auth' to authenticate.")
			return
		}

		if len(flyOrgs) == 0 {
			fmt.Println("No organizations found in your Fly.io account.")
			return
		}

		// For each discovered org, check if we can get its sprite token from keyring
		discoveredOrgs := 0
		for _, flyOrg := range flyOrgs {
			// Try to get the sprite token from keyring
			org := &config.Organization{
				Name: flyOrg.Slug,
				URL:  "https://api.sprites.dev",
			}
			if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
				org.URL = envURL
			}

			// Check if we can get token from keyring
			_, err := org.GetToken()
			if err == nil {
				// Found a valid token in keyring, add to config
				if err := cfg.AddOrgMetadataOnly(flyOrg.Slug, org.URL); err == nil {
					discoveredOrgs++
					slog.Debug("Discovered organization from keyring", "org", flyOrg.Slug)
				}
			}
		}

		if discoveredOrgs > 0 {
			// Save config with discovered orgs
			if err := cfg.Save(); err != nil {
				slog.Debug("Failed to save config with discovered orgs", "error", err)
			}
			// Reload orgs after discovery
			orgs = cfg.GetOrgs()
		} else {
			fmt.Println("No authenticated organizations found.")
			fmt.Println("Run 'sprite org auth' to authenticate.")
			return
		}
	} else {
		// We have orgs in config - do NOT remove them even if keyring access fails
		// This preserves the user's configuration regardless of keychain/keyring state
		slog.Debug("Found organizations in config", "count", len(orgs))
	}

	if len(orgs) == 0 {
		fmt.Println("No API tokens configured.")
		fmt.Println("Run 'sprite org auth' to add one.")
		return
	}

	// Show all organizations
	fmt.Printf("You have %s API token(s) configured:\n", format.Info(fmt.Sprintf("%d", len(orgs))))

	i := 1
	for _, org := range orgs {
		displayName := format.GetOrgDisplayName(org.Name, org.URL)

		// Check if token is accessible (but don't remove the org if it's not)
		tokenStatus := ""
		if !cfg.IsKeyringDisabled() {
			if _, err := org.GetToken(); err != nil {
				tokenStatus = " " + format.Subtle("(token not accessible in keyring)")
			}
		}

		fmt.Printf("  %d. %s%s\n", i, format.Org(displayName), tokenStatus)
		i++
	}

	currentOrg := cfg.GetCurrentOrg()
	if currentOrg != nil {
		fmt.Printf("\nCurrently selected: %s\n", format.Org(format.GetOrgDisplayName(currentOrg.Name, currentOrg.URL)))
	} else {
		fmt.Printf("\nNo organization currently selected.\n")
		fmt.Printf("Organizations will be selected automatically when needed, or you can specify with -o flag.\n")
	}
}

func orgLogoutCommand(cfg *config.Manager, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "org logout",
		Usage:       "org logout [options]",
		Description: "Remove all tokens",
		FlagSet:     flag.NewFlagSet("org logout", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)
	force := cmd.FlagSet.Bool("force", false, "Skip confirmation prompt")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: org logout takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	orgs := cfg.GetOrgs()

	if len(orgs) == 0 {
		fmt.Println("No API tokens to remove.")
		return
	}

	if !*force {
		title := fmt.Sprintf("Remove all %d API token(s)?", len(orgs))
		description := "This will remove all configured API tokens. You'll need to re-authenticate to use Sprites."

		confirmed := PromptForConfirmationOrExit(title, description)

		if !confirmed {
			fmt.Println("Logout cancelled.")
			return
		}
	}

	// For now, since we auto-generate org names, just remove all
	// TODO: Improve this when we have proper org management
	for name := range orgs {
		if err := cfg.RemoveOrg(name); err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to remove token: %v\n", err)
			os.Exit(1)
		}
	}

	fmt.Println(format.Success("✓ Removed all API tokens."))
}

func orgKeyringCommand(cfg *config.Manager, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "org keyring",
		Usage:       "org keyring <enable|disable|status>",
		Description: "Enable/disable keyring usage",
		FlagSet:     flag.NewFlagSet("org keyring", flag.ContinueOnError),
		Examples: []string{
			"sprite org keyring status",
			"sprite org keyring enable",
			"sprite org keyring disable",
		},
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Custom usage to show subcommands
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		fmt.Fprintf(os.Stderr, "Subcommands:\n")
		fmt.Fprintf(os.Stderr, "  status    Show current keyring status\n")
		fmt.Fprintf(os.Stderr, "  enable    Enable keyring usage (default)\n")
		fmt.Fprintf(os.Stderr, "  disable   Disable keyring, use file storage\n\n")
		fmt.Fprintf(os.Stderr, "Options:\n")
		cmd.FlagSet.PrintDefaults()
		fmt.Fprintln(os.Stderr)
		if len(cmd.Examples) > 0 {
			fmt.Fprintf(os.Stderr, "Examples:\n")
			for _, example := range cmd.Examples {
				fmt.Fprintf(os.Stderr, "  %s\n", example)
			}
			fmt.Fprintln(os.Stderr)
		}
	}

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) < 1 {
		// Default to status if no subcommand
		orgKeyringStatusCommand(cfg)
		return
	}

	subcommand := remainingArgs[0]
	switch subcommand {
	case "status":
		orgKeyringStatusCommand(cfg)
	case "enable":
		orgKeyringEnableCommand(cfg)
	case "disable":
		orgKeyringDisableCommand(cfg)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown keyring subcommand '%s'\n\n", subcommand)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}
}

func orgKeyringStatusCommand(cfg *config.Manager) {
	if cfg.IsKeyringDisabled() {
		fmt.Printf("Keyring usage: %s\n", format.Error("DISABLED"))
		fmt.Printf("Tokens are stored in: %s\n", format.Info("~/.sprites/config.json"))
		fmt.Println("\nRun 'sprite org keyring enable' to use system keyring for secure token storage.")
	} else {
		fmt.Printf("Keyring usage: %s\n", format.Success("ENABLED"))
		fmt.Printf("Tokens are stored in: %s\n", format.Info("System keyring (secure)"))
		fmt.Println("\nRun 'sprite org keyring disable' to store tokens in config file instead.")
	}
}

func orgKeyringEnableCommand(cfg *config.Manager) {
	if !cfg.IsKeyringDisabled() {
		fmt.Println("Keyring usage is already enabled.")
		return
	}

	if err := cfg.SetKeyringDisabled(false); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to enable keyring: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("%s Keyring usage enabled.\n", format.Success("✓"))
	fmt.Println("Future tokens will be stored securely in the system keyring.")
	fmt.Println("Existing tokens in config file will be migrated on next use.")
}

func orgKeyringDisableCommand(cfg *config.Manager) {
	if cfg.IsKeyringDisabled() {
		fmt.Println("Keyring usage is already disabled.")
		return
	}

	if err := cfg.SetKeyringDisabled(true); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to disable keyring: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("%s Keyring usage disabled.\n", format.Success("✓"))
	fmt.Println("Tokens will be stored in ~/.sprites/config.json")
	fmt.Printf("%s Note: Existing tokens remain in keyring until you re-authenticate.\n", format.Info("ℹ"))
}
