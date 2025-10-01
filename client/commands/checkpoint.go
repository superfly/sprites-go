package commands

import (
	"context"
	"flag"
	"fmt"
	"os"
	"strings"
	"time"

	"log/slog"

	"github.com/superfly/sprite-env/client/format"
	sprites "github.com/superfly/sprites-go"
)

// CheckpointCommand handles the checkpoint command
func CheckpointCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "checkpoint",
		Usage:       "checkpoint <subcommand> [options]",
		Description: "Manage checkpoints",
		FlagSet:     flag.NewFlagSet("checkpoint", flag.ContinueOnError),
		Examples: []string{
			"sprite checkpoint create",
			"sprite checkpoint list",
			"sprite checkpoint info <checkpoint-id>",
			"sprite checkpoint list --history VERSION",
		},
	}

	// Set up sprite flags for the main checkpoint command
	flags := NewSpriteFlags(cmd.FlagSet)

	// Custom usage to show subcommands
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		fmt.Fprintf(os.Stderr, "Subcommands:\n")
		fmt.Fprintf(os.Stderr, "  create    Create a new checkpoint\n")
		fmt.Fprintf(os.Stderr, "  list      List all checkpoints\n")
		fmt.Fprintf(os.Stderr, "  info      Show information about a specific checkpoint\n\n")
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

	// Parse flags to get org/sprite overrides
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Get organization, client, and sprite using unified function
	_, _, sprite, err := GetOrgClientAndSprite(ctx, flags.Org, flags.Sprite)
	if err != nil {
		// Check if it's a cancellation error
		if strings.Contains(err.Error(), "cancelled") {
			handlePromptError(err)
		} else {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
		os.Exit(1)
	}

	if len(remainingArgs) < 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint requires a subcommand\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	subcommand := remainingArgs[0]
	subArgs := remainingArgs[1:]

	switch subcommand {
	case "create":
		checkpointCreateCommand(ctx, sprite, subArgs)
	case "list", "ls":
		checkpointListCommandWithFlags(ctx, sprite, subArgs)
	case "info":
		if len(subArgs) < 1 {
			fmt.Fprintf(os.Stderr, "Error: checkpoint info requires a checkpoint ID\n\n")
			cmd.FlagSet.Usage()
			os.Exit(1)
		}
		checkpointInfoCommand(ctx, sprite, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown checkpoint subcommand '%s'\n\n", subcommand)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}
}

func checkpointCreateCommand(ctx *GlobalContext, sprite *sprites.Sprite, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "checkpoint create",
		Usage:       "checkpoint create",
		Description: "Create a new checkpoint",
		FlagSet:     flag.NewFlagSet("checkpoint create", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) != 0 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint create takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Client is already created by GetOrgAndClient

	// Create checkpoint using SDK
	reqCtx := context.Background()
	stream, err := sprite.Client().CreateCheckpoint(reqCtx, sprite.Name())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create checkpoint: %v\n", err)
		os.Exit(1)
	}
	defer stream.Close()

	// Process streaming response
	exitCode := 0
	hasError := false

	err = stream.ProcessAll(func(msg *sprites.StreamMessage) error {
		switch msg.Type {
		case "info":
			fmt.Println(msg.Data)
		case "stdout":
			fmt.Println(msg.Data)
		case "stderr":
			fmt.Fprintln(os.Stderr, msg.Data)
		case "error":
			fmt.Fprintf(os.Stderr, "Error: %s\n", msg.Error)
			hasError = true
			if exitCode == 0 {
				exitCode = 1
			}
		}
		return nil
	})

	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to process stream: %v\n", err)
		os.Exit(1)
	}

	// If we had errors but no specific exit code, return 1
	if hasError && exitCode == 0 {
		os.Exit(1)
	}

	os.Exit(exitCode)
}

func checkpointListCommandWithFlags(ctx *GlobalContext, sprite *sprites.Sprite, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "checkpoint list",
		Usage:       "checkpoint list [options]",
		Description: "List all checkpoints",
		FlagSet:     flag.NewFlagSet("checkpoint list", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)
	historyFilter := cmd.FlagSet.String("history", "", "Filter by history version")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint list takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	checkpointListCommand(ctx, sprite, *historyFilter)
}

func checkpointListCommand(ctx *GlobalContext, sprite *sprites.Sprite, historyFilter string) {
	// Client is already created by GetOrgAndClient

	// Debug log the request
	slog.Debug("Checkpoint list request", "sprite", sprite.Name())

	// Debug: Track request timing
	startTime := time.Now()
	if ctx.IsDebugEnabled() {
		fmt.Printf("Making checkpoint list request...\n")
	}

	// List checkpoints using SDK
	ctxReq := context.Background()
	checkpoints, err := sprite.Client().ListCheckpoints(ctxReq, sprite.Name(), historyFilter)
	if err != nil {
		// Check if it's a text response (history filter)
		if strings.Contains(err.Error(), "text response not supported") {
			// For now, we can't handle text responses with the SDK
			fmt.Fprintf(os.Stderr, "Error: History filter not supported with SDK yet\n")
			os.Exit(1)
		}
		fmt.Fprintf(os.Stderr, "Error: Failed to list checkpoints: %v\n", err)
		os.Exit(1)
	}

	// Debug: Log request timing
	if ctx.IsDebugEnabled() {
		duration := time.Since(startTime)
		fmt.Printf("Request completed in %v\n", duration)
		fmt.Printf("Parsed %d checkpoints\n", len(checkpoints))
	}

	// Display checkpoints
	if len(checkpoints) == 0 {
		fmt.Println("No checkpoints found.")
		return
	}

	// Display header
	fmt.Printf("%-30s %s\n", "ID", "CREATED")
	fmt.Printf("%-30s %s\n", strings.Repeat("-", 30), strings.Repeat("-", 25))

	for _, cp := range checkpoints {
		created := cp.CreateTime.Format("2006-01-02 15:04:05")

		// Format the ID for display
		displayID := cp.ID
		if cp.ID == "Current" {
			displayID = "→ Current (active)"
		}

		fmt.Printf("%-30s %s\n", displayID, created)
	}
}

func checkpointInfoCommand(ctx *GlobalContext, sprite *sprites.Sprite, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint info requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite checkpoint info <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Client is already created by GetOrgAndClient

	// Get checkpoint info using SDK
	reqCtx := context.Background()
	checkpoint, err := sprite.Client().GetCheckpoint(reqCtx, sprite.Name(), checkpointID)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get checkpoint info: %v\n", err)
		os.Exit(1)
	}

	// Display checkpoint information
	fmt.Printf("ID: %s\n", checkpoint.ID)
	fmt.Printf("Created: %s\n", checkpoint.CreateTime.Format(time.RFC3339))

	if len(checkpoint.History) > 0 {
		fmt.Println("History:")
		for _, entry := range checkpoint.History {
			fmt.Printf("  %s\n", entry)
		}
	} else {
		fmt.Println("History: (none)")
	}
}

// RestoreCommand handles the restore command
func RestoreCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "restore",
		Usage:       "restore [options] <checkpoint-id>",
		Description: "Restore from a checkpoint",
		FlagSet:     flag.NewFlagSet("restore", flag.ContinueOnError),
		Examples: []string{
			"sprite restore my-checkpoint-id",
			"sprite restore -o myorg -s mysprite checkpoint-123",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) != 1 {
		fmt.Fprintf(os.Stderr, "Error: restore requires exactly one argument (checkpoint ID)\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	checkpointID := remainingArgs[0]

	// Get organization, client, and sprite using unified function
	org, _, sprite, err := GetOrgClientAndSprite(ctx, flags.Org, flags.Sprite)
	if err != nil {
		// Check if it's a cancellation error
		if strings.Contains(err.Error(), "cancelled") {
			handlePromptError(err)
		} else {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
		os.Exit(1)
	}

	if sprite.Name() != "" {
		fmt.Println(format.ContextSprite(format.GetOrgDisplayName(org.Name, org.URL), fmt.Sprintf("Restoring checkpoint %s for sprite", format.Command(checkpointID)), sprite.Name()))
		fmt.Println()
	}

	// Debug log the request
	slog.Debug("Restore request", "sprite", sprite.Name(), "checkpointID", checkpointID)

	// Restore checkpoint using SDK
	ctxReq := context.Background()
	stream, err := sprite.Client().RestoreCheckpoint(ctxReq, sprite.Name(), checkpointID)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to restore checkpoint: %v\n", err)
		os.Exit(1)
	}
	defer stream.Close()

	// Process streaming response
	exitCode := 0
	hasError := false

	err = stream.ProcessAll(func(msg *sprites.StreamMessage) error {
		switch msg.Type {
		case "info":
			fmt.Println(msg.Data)
		case "stdout":
			fmt.Println(msg.Data)
		case "stderr":
			fmt.Fprintln(os.Stderr, msg.Data)
		case "error":
			fmt.Fprintf(os.Stderr, "Error: %s\n", msg.Error)
			hasError = true
			if exitCode == 0 {
				exitCode = 1
			}
		}
		return nil
	})

	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to process stream: %v\n", err)
		os.Exit(1)
	}

	// If we had errors but no specific exit code, return 1
	if hasError && exitCode == 0 {
		os.Exit(1)
	}

	os.Exit(exitCode)
}
