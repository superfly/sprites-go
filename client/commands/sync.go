package commands

import (
	"context"
	"flag"
	"fmt"
	"log/slog"
	"os"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"github.com/superfly/sprite-env/pkg/sync"
)

// SyncCommand handles the sync command
func SyncCommand(cfg *config.Manager, args []string) {
	cmd := &Command{
		Name:        "sync",
		Usage:       "sync [options] [source-path]",
		Description: "Synchronize the current git repository (or specified path) to the sprite environment.",
		Examples: []string{
			"sprite sync --target /app",
			"sprite sync --target /app --branch develop --include-uncommitted",
			"sprite sync --target /app /path/to/repo",
		},
		FlagSet: flag.NewFlagSet("sync", flag.ContinueOnError),
	}

	flags := NewSpriteFlags(cmd.FlagSet)
	var targetPath, branch string
	var includeUncommitted bool

	cmd.FlagSet.StringVar(&targetPath, "target", "", "Target directory in sprite environment")
	cmd.FlagSet.StringVar(&targetPath, "T", "", "Target directory in sprite environment (shorthand)")
	cmd.FlagSet.StringVar(&branch, "branch", "", "Specific branch to sync (defaults to current branch)")
	cmd.FlagSet.StringVar(&branch, "b", "", "Specific branch to sync (shorthand)")
	cmd.FlagSet.BoolVar(&includeUncommitted, "include-uncommitted", false, "Include uncommitted files in sync")
	cmd.FlagSet.BoolVar(&includeUncommitted, "u", false, "Include uncommitted files in sync (shorthand)")

	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if targetPath == "" {
		fmt.Fprintf(os.Stderr, "Error: target is required\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	sourcePath := "."
	if len(remainingArgs) > 0 {
		if len(remainingArgs) > 1 {
			fmt.Fprintf(os.Stderr, "Error: sync takes at most one argument\n\n")
			cmd.FlagSet.Usage()
			os.Exit(1)
		}
		sourcePath = remainingArgs[0]
	}

	org, spriteName, err := EnsureOrgAndSpriteWithContext(&GlobalContext{ConfigMgr: cfg}, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
	if spriteName != "" {
		fmt.Printf("Creating sprite %s...\n", format.Sprite(spriteName))
		if err := CreateSprite(cfg, org, spriteName); err != nil {
			fmt.Fprintf(os.Stderr, "Error creating sprite: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("%s Sprite %s created successfully!\n", format.Success("✓"), format.Sprite(spriteName))
	}

	token, err := org.GetTokenWithKeyringDisabled(cfg.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("Starting sync from %s to %s\n", sourcePath, targetPath)
	clientCfg := sync.ClientConfig{
		TargetPath:         targetPath,
		Branch:             branch,
		IncludeUncommitted: includeUncommitted,
		ProgressCallback: func(progress sync.Progress) {
			fmt.Printf("\rProgress: %d/%d files, %d/%d bytes",
				progress.FilesProcessed, progress.FilesTotal,
				progress.BytesUploaded, progress.BytesTotal)
		},
		Logger: slog.New(slog.NewTextHandler(os.Stderr,
			&slog.HandlerOptions{
				Level: slog.LevelDebug,
			})),
	}

	client := sync.NewClient(sourcePath, clientCfg)

	ctx := context.Background()
	if err := client.Sync(ctx, org.URL, token); err != nil {
		fmt.Fprintf(os.Stderr, "Error: sync failed: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("\nSync completed successfully!\n")
}
