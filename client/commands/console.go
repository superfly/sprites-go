package commands

import (
	"flag"
	"fmt"
	"os"
	"path/filepath"
)

// detectParentShell detects the shell that invoked the sprite command
func detectParentShell() string {
	// Check shell-specific environment variables first
	// These are set when running inside the respective shell
	if os.Getenv("BASH_VERSION") != "" {
		return "/bin/bash"
	}
	if os.Getenv("ZSH_VERSION") != "" {
		return "/bin/zsh"
	}
	if os.Getenv("FISH_VERSION") != "" {
		return "/usr/bin/fish"
	}
	// tcsh sets tcsh and version variables
	if os.Getenv("tcsh") != "" {
		return "/bin/tcsh"
	}
	// ksh sets KSH_VERSION
	if os.Getenv("KSH_VERSION") != "" {
		return "/bin/ksh"
	}

	// Fall back to SHELL environment variable (user's default shell)
	// but only if it's one of our supported shells
	if shell := os.Getenv("SHELL"); shell != "" {
		shellName := filepath.Base(shell)
		switch shellName {
		case "bash", "zsh", "fish", "tcsh", "ksh":
			// Check common locations for the shell
			for _, prefix := range []string{"/bin/", "/usr/bin/"} {
				fullPath := prefix + shellName
				if _, err := os.Stat(fullPath); err == nil {
					return fullPath
				}
			}
			// If we can't find it in standard locations, use the original path
			return shell
		}
	}

	// Default to bash
	return "/bin/bash"
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
		},
		Notes: []string{
			"Opens an interactive shell with a TTY allocated",
			"Automatically detects and uses your current shell",
			"Supported shells: bash, zsh, fish, tcsh, ksh",
			"Falls back to bash if shell detection fails",
		},
	}

	// Set up sprite flags (org/sprite selection)
	flags := NewSpriteFlags(cmd.FlagSet)

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

	// Build the exec command arguments
	execArgs := []string{}

	// Always use tty for console, with detected shell
	detectedShell := detectParentShell()
	execArgs = append(execArgs, "-tty", detectedShell, "--login")

	// If org/sprite were specified, pass them through
	if flags.Org != "" {
		execArgs = append([]string{"-org", flags.Org}, execArgs...)
	}
	if flags.Sprite != "" {
		execArgs = append([]string{"-sprite", flags.Sprite}, execArgs...)
	}

	// Call ExecCommand with the constructed arguments
	ExecCommand(ctx, execArgs)
}
