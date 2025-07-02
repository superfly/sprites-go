package commands

import (
	"flag"
	"fmt"
	"os"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"github.com/sprite-env/client/prompts"
)

// OrgCommand handles organization-related commands
func OrgCommand(cfg *config.Manager, args []string) {
	// Create command structure for org
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
		orgAuthCommand(cfg, subArgs)
	case "list":
		orgListCommand(cfg, subArgs)
	case "logout":
		orgLogoutCommand(cfg, subArgs)
	case "keyring":
		orgKeyringCommand(cfg, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown org subcommand '%s'\n\n", subcommand)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}
}

func orgAuthCommand(cfg *config.Manager, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "org auth",
		Usage:       "org auth",
		Description: "Add an API token",
		FlagSet:     flag.NewFlagSet("org auth", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: org auth takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Use the same simplified flow as initial login
	org, err := prompts.PromptForInitialLogin(cfg)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Set as current org
	if err := cfg.SetCurrentOrg(org.Name); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to set current organization: %v\n", err)
		os.Exit(1)
	}
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

	// If no organizations in config, try to discover from keyring
	if len(orgs) == 0 {
		_, err := cfg.DiscoverFromKeyring()
		if err == nil {
			// Reload orgs after discovery
			orgs = cfg.GetOrgs()
		}
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
		fmt.Printf("  %d. %s\n", i, format.Org(displayName))
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

		confirmed, err := prompts.PromptForConfirmation(title, description)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}

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
