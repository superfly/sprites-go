package commands

import (
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
)

// TranscriptsCommand handles the transcripts command
func TranscriptsCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "transcripts",
		Usage:       "transcripts <subcommand>",
		Description: "Manage transcript recording",
		FlagSet:     flag.NewFlagSet("transcripts", flag.ContinueOnError),
		Examples: []string{
			"sprite transcripts enable",
			"sprite transcripts disable",
		},
	}

	// Set up global flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Custom usage to show subcommands
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		fmt.Fprintf(os.Stderr, "Subcommands:\n")
		fmt.Fprintf(os.Stderr, "  enable     Enable transcript recording for future exec calls\n")
		fmt.Fprintf(os.Stderr, "  disable    Disable transcript recording for future exec calls\n\n")
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
		fmt.Fprintf(os.Stderr, "Error: transcripts requires a subcommand\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	subcommand := remainingArgs[0]
	subArgs := remainingArgs[1:]

	switch subcommand {
	case "enable":
		transcriptsEnableCommand(ctx, subArgs)
	case "disable":
		transcriptsDisableCommand(ctx, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown transcripts subcommand '%s'\n\n", subcommand)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}
}

func transcriptsEnableCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "transcripts enable",
		Usage:       "transcripts enable",
		Description: "Enable transcript recording for future exec calls",
		FlagSet:     flag.NewFlagSet("transcripts enable", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) != 0 {
		fmt.Fprintf(os.Stderr, "Error: transcripts enable takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Get current organization
	org := ctx.ConfigMgr.GetCurrentOrg()
	if org == nil {
		fmt.Fprintf(os.Stderr, "Error: No organization configured. Please run 'sprite org auth' first\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/transcripts/enable", org.URL)
	ctx.Logger.Debug("HTTP request", "method", "POST", "url", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}
	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make HTTP request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: HTTP %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	fmt.Println("Transcript recording enabled for future exec calls.")
}

func transcriptsDisableCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "transcripts disable",
		Usage:       "transcripts disable",
		Description: "Disable transcript recording for future exec calls",
		FlagSet:     flag.NewFlagSet("transcripts disable", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) != 0 {
		fmt.Fprintf(os.Stderr, "Error: transcripts disable takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Get current organization
	org := ctx.ConfigMgr.GetCurrentOrg()
	if org == nil {
		fmt.Fprintf(os.Stderr, "Error: No organization configured. Please run 'sprite org auth' first\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/transcripts/disable", org.URL)
	ctx.Logger.Debug("HTTP request", "method", "POST", "url", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}
	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make HTTP request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: HTTP %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	fmt.Println("Transcript recording disabled.")
}
