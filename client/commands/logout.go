package commands

import (
	"context"
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/superfly/sprite-env/client/fly"
	"github.com/superfly/sprite-env/client/format"
)

// LogoutCommand handles logout and cleanup
func LogoutCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "logout",
		Usage:       "logout [options]",
		Description: "Remove Sprites configuration",
		FlagSet:     flag.NewFlagSet("logout", flag.ContinueOnError),
		Examples: []string{
			"sprite logout",
		},
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: logout takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	authCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// Try to get user info to clean up user-scoped keychain
	flyToken, source, err := fly.ReadFlyToken()
	var user *fly.User
	if err == nil {
		fmt.Print("Getting user info for cleanup...")
		user, err = fly.GetCurrentUser(authCtx, flyToken)
		if err == nil {
			fmt.Print("\r\033[K") // Clear the line
			fmt.Printf("✓ Logged in as: %s\n\n", user.Email)
		} else {
			fmt.Print("\r\033[K") // Clear the line
			fmt.Printf("Warning: Could not get user info: %v\n\n", err)
		}
	}

	// Clean up user and all their tokens if we have user info
	if user != nil {
		fmt.Print("Removing user and all tokens...")

		// Remove encrypted Fly token and encryption key
		if err := fly.DeleteFlyTokenEncrypted(user.ID); err != nil {
			fmt.Printf("\nWarning: Failed to remove Fly token: %v\n", err)
		}

		// Remove user's Sprite tokens and config
		if err := ctx.ConfigMgr.RemoveUser(user.ID); err != nil {
			fmt.Print("\r\033[K") // Clear the line
			fmt.Printf("Warning: Failed to remove user %s: %v\n", user.Email, err)
		} else {
			fmt.Print("\r\033[K") // Clear the line
			fmt.Printf(format.Success("✓ Removed user %s and all their tokens\n"), user.Email)
		}
	} else {
		fmt.Println("Note: Could not clean user-scoped keychain without Fly credentials")
		if source != "" {
			fmt.Printf("Found token from %s but couldn't verify user\n\n", source)
		}

		// Fallback: clean up any remaining orgs manually
		fmt.Print("Removing any remaining Sprites configuration...")
		orgs := ctx.ConfigMgr.GetOrgs()
		removedCount := 0
		for name := range orgs {
			if err := ctx.ConfigMgr.RemoveOrg(name); err != nil {
				fmt.Printf("\nWarning: Failed to remove org %s: %v\n", name, err)
			} else {
				removedCount++
			}
		}
		fmt.Print("\r\033[K") // Clear the line
		if removedCount > 0 {
			fmt.Printf(format.Success("✓ Removed %d organization(s) from Sprites config\n"), removedCount)
		}
	}

	fmt.Println()
	fmt.Println(format.Success("✓ Logout complete"))
	fmt.Println("\nNote: Run 'flyctl auth logout' to remove Fly.io credentials if needed")
}
