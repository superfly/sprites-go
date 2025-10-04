package commands

import (
	"encoding/base64"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// getTerminfoData reads the local terminfo database entry for the current terminal
func getTerminfoData() string {
	term := os.Getenv("TERM")
	if term == "" {
		return ""
	}

	// Try to find the terminfo file in common locations
	// The terminfo database uses the first letter of TERM as a subdirectory
	termLetter := string(term[0])

	// Common terminfo locations
	terminfoLocations := []string{
		filepath.Join(os.Getenv("HOME"), ".terminfo", termLetter, term),
		filepath.Join("/usr/share/terminfo", termLetter, term),
		filepath.Join("/lib/terminfo", termLetter, term),
		filepath.Join("/etc/terminfo", termLetter, term),
	}

	// Try each location
	for _, path := range terminfoLocations {
		if data, err := os.ReadFile(path); err == nil {
			// Encode to base64 for safe transport
			return base64.StdEncoding.EncodeToString(data)
		}
	}

	return ""
}

// ConsoleCommand handles the console command - opens an interactive shell
func ConsoleCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "console",
		Usage:       "console [options]",
		Description: "Open an interactive shell in the sprite environment",
		FlagSet:     flag.NewFlagSet("console", flag.ContinueOnError),
		Examples: []string{
			"sprite console",
			"sprite console -o myorg -s mysprite",
			"sprite console -detachable",
		},
		Notes: []string{
			"Opens an interactive shell with a TTY allocated",
			"Uses shell environment variables to determine which shell to use",
			"Supported shells: bash, zsh, fish, tcsh, ksh",
			"Falls back to bash if shell detection fails",
			"When using -detachable, creates a tmux session that can be detached and reattached.",
		},
	}

	// Set up sprite flags (org/sprite selection)
	flags := NewSpriteFlags(cmd.FlagSet)

	// Console-specific flags
	detachable := cmd.FlagSet.Bool("detachable", true, "Create a detachable tmux session")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Console command doesn't take any additional arguments
	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: console command takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Collect shell-related environment variables to pass through
	var envVars []string
	shellEnvVars := []string{
		"BASH_VERSION",
		"ZSH_VERSION",
		"FISH_VERSION",
		"KSH_VERSION",
		"tcsh",
		"SHELL",
	}

	for _, envVar := range shellEnvVars {
		if value := os.Getenv(envVar); value != "" {
			envVars = append(envVars, envVar+"="+value)
		}
	}

	// Read and encode local terminfo if available
	if terminfoData := getTerminfoData(); terminfoData != "" {
		envVars = append(envVars, "SPRITE_TERMINFO_DATA="+terminfoData)
	}

	// Build the exec command arguments
	execArgs := []string{}

	// If org/sprite were specified, pass them through
	if flags.Org != "" {
		execArgs = append(execArgs, "-org", flags.Org)
	}
	if flags.Sprite != "" {
		execArgs = append(execArgs, "-sprite", flags.Sprite)
	}

	// Add environment variables
	if len(envVars) > 0 {
		execArgs = append(execArgs, "-env", strings.Join(envVars, ","))
	}

	// Always use tty for console
	execArgs = append(execArgs, "-tty")

	// Pass through detachable if requested
	if *detachable {
		execArgs = append(execArgs, "-detachable")
	}

	// Execute the sprite-console script which will handle shell selection
	execArgs = append(execArgs, "/.sprite/bin/sprite-console")

	// Call ExecCommand with the constructed arguments
	ExecCommand(ctx, execArgs)
}
