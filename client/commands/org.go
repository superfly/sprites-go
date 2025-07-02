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
		fmt.Fprintf(os.Stderr, "  logout    Remove all tokens\n\n")
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
	
	if len(orgs) == 0 {
		fmt.Println("No API tokens configured.")
		fmt.Println("Run 'sprite org auth' to add one.")
		return
	}

	// For now, just show a count since org names are auto-generated
	fmt.Printf("You have %s API token(s) configured.\n", format.Info(fmt.Sprintf("%d", len(orgs))))
	
	currentOrg := cfg.GetCurrentOrg()
	if currentOrg != nil {
		fmt.Printf("Currently using: %s\n", format.Org(format.GetOrgDisplayName(currentOrg.Name, currentOrg.URL)))
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
		fmt.Printf("This will remove all %d API token(s). Are you sure? (y/N): ", len(orgs))
		var response string
		fmt.Scanln(&response)
		
		if response != "y" && response != "Y" {
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