package main

import (
	"context"
	"fmt"
	"log/slog"
	"net/url"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"github.com/superfly/sprite-env/pkg/sync"
	"github.com/superfly/sprite-env/pkg/terminal"
	"github.com/urfave/cli/v2"
	"golang.org/x/term"
)

// SpriteRunner directly executes commands in sprite environments
type SpriteRunner struct{}

// NewSpriteRunner creates a new sprite runner instance
func NewSpriteRunner() *SpriteRunner {
	return &SpriteRunner{}
}

// RunCommand executes a command directly in a sprite environment via WebSocket
func (sr *SpriteRunner) RunCommand(cmd string, args []string, spriteURL, token, workingDir string, env []string, tty bool) int {
	// Build WebSocket URL for exec endpoint
	wsURL, err := buildExecWebSocketURL(spriteURL)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to build WebSocket URL: %v\n", err)
		return 1
	}

	// Build command arguments
	cmdArgs := []string{cmd}
	cmdArgs = append(cmdArgs, args...)

	return executeWebSocket(wsURL, token, cmdArgs, workingDir, env, tty)
}

// buildExecWebSocketURL converts HTTP/HTTPS URL to WS/WSS URL for exec
func buildExecWebSocketURL(baseURL string) (*url.URL, error) {
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, err
	}

	// Convert scheme
	switch u.Scheme {
	case "http":
		u.Scheme = "ws"
	case "https":
		u.Scheme = "wss"
	case "ws", "wss":
		// Already WebSocket URL, keep as is
	default:
		return nil, fmt.Errorf("unsupported scheme: %s (supported: http, https, ws, wss)", u.Scheme)
	}

	// Append /exec to any existing path while preserving prefix paths
	cleanPath := strings.TrimRight(u.Path, "/")
	if cleanPath == "" {
		u.Path = "/exec"
	} else {
		u.Path = cleanPath + "/exec"
	}

	return u, nil
}

// executeWebSocket is the core WebSocket execution logic
func executeWebSocket(wsURL *url.URL, token string, cmd []string, workingDir string, env []string, tty bool) int {
	// Capture initial terminal state for restoration at the end
	var initialState *term.State
	if term.IsTerminal(int(os.Stdin.Fd())) {
		if state, err := term.GetState(int(os.Stdin.Fd())); err == nil {
			initialState = state
		}
	}
	defer func() {
		if initialState != nil {
			term.Restore(int(os.Stdin.Fd()), initialState)
		}
	}()

	logger := slog.Default()
	logger.Debug("Starting WebSocket exec", "url", wsURL.String(), "cmd", cmd, "workingDir", workingDir, "env", env, "tty", tty)

	// Add command arguments as query parameters
	query := wsURL.Query()
	for i, arg := range cmd {
		query.Add("cmd", arg)
		if i == 0 {
			query.Set("path", arg) // Set the main command path
		}
	}
	if workingDir != "" {
		query.Set("dir", workingDir)
		logger.Debug("Set working directory", "dir", workingDir)
	}
	if tty {
		query.Set("tty", "true")
		logger.Debug("Enabled TTY mode")

		// Send initial terminal size as part of connection setup
		if term.IsTerminal(int(os.Stdin.Fd())) {
			if width, height, err := term.GetSize(int(os.Stdin.Fd())); err == nil {
				query.Set("cols", fmt.Sprintf("%d", width))
				query.Set("rows", fmt.Sprintf("%d", height))
				logger.Debug("Set initial terminal size", "cols", width, "rows", height)
			}
		}
	}
	for _, envVar := range env {
		query.Add("env", envVar)
		logger.Debug("Added environment variable", "env", envVar)
	}
	wsURL.RawQuery = query.Encode()

	logger.Debug("Final WebSocket URL with query parameters", "url", wsURL.String())

	// Create HTTP request with auth header
	req, err := http.NewRequest("GET", wsURL.String(), nil)
	if err != nil {
		logger.Error("Failed to create HTTP request", "error", err)
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		return 1
	}
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	// Create exec command
	wsCmd := terminal.CommandContext(context.Background(), req, "placeholder")

	// Set client-side I/O configuration
	wsCmd.Stdin = os.Stdin
	wsCmd.Stdout = os.Stdout
	wsCmd.Stderr = os.Stderr
	wsCmd.Tty = tty

	logger.Debug("Created exec command", "tty", wsCmd.Tty)

	// Set up PTY mode if needed
	var cleanup func()
	if tty {
		var err error
		cleanup, err = handlePTYMode(wsCmd)
		if err != nil {
			logger.Error("Failed to set up PTY mode", "error", err)
			fmt.Fprintf(os.Stderr, "Warning: Failed to set up PTY mode: %v\n", err)
			// Continue anyway - PTY will work but without raw mode
		}
		defer func() {
			if cleanup != nil {
				cleanup()
			}
		}()
	}

	logger.Debug("Starting WebSocket command execution")

	// Start the command
	if err := wsCmd.Start(); err != nil {
		logger.Error("Failed to start WebSocket command", "error", err)
		fmt.Fprintf(os.Stderr, "Error: Failed to start command: %v\n", err)
		return 1
	}

	// Wait for command to complete
	if err := wsCmd.Wait(); err != nil {
		logger.Error("WebSocket command wait failed", "error", err)
		// Don't print error here - it's usually just context cancelled
	}

	// Gracefully close the WebSocket connection
	wsCmd.Close()

	// Get exit code
	exitCode := wsCmd.ExitCode()
	logger.Debug("Command completed", "exitCode", exitCode)

	if exitCode == -1 {
		logger.Warn("No proper exit code received, defaulting to 1")
		// If we didn't get a proper exit code, default to 1
		exitCode = 1
	}

	logger.Debug("WebSocket exec completed", "finalExitCode", exitCode)

	// Restore terminal state before exiting
	if initialState != nil {
		term.Restore(int(os.Stdin.Fd()), initialState)
	}

	return exitCode
}

// handlePTYMode sets up the terminal for PTY mode and returns a cleanup function
func handlePTYMode(wsCmd *terminal.Cmd) (cleanup func(), err error) {
	// Check if stdin is a terminal
	if !term.IsTerminal(int(os.Stdin.Fd())) {
		// Not a terminal, no special handling needed
		return func() {}, nil
	}

	// Save the current terminal state
	oldState, err := term.MakeRaw(int(os.Stdin.Fd()))
	if err != nil {
		return nil, fmt.Errorf("failed to set terminal to raw mode: %w", err)
	}

	// Set up cleanup function
	cleanup = func() {
		// Restore terminal state
		term.Restore(int(os.Stdin.Fd()), oldState)
		// Show cursor in case it was hidden
		fmt.Print("\033[?25h")
	}

	// Handle terminal resize
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGWINCH)

	go func() {
		for range sigCh {
			// Get current terminal size and send to server
			width, height, err := term.GetSize(int(os.Stdin.Fd()))
			if err == nil {
				wsCmd.Resize(uint16(width), uint16(height))
			}
		}
	}()

	return cleanup, nil
}

func main() {
	// Create sprite runner
	runner := NewSpriteRunner()

	app := &cli.App{
		Name:  "sprite-run",
		Usage: "Run programs inside sprite environments",
		Description: "sprite-run connects directly to sprite environments via WebSocket to execute programs. " +
			"Programs appear to run locally, similar to running under tmux.",
		Version: "1.0.0",
		Flags: []cli.Flag{
			&cli.StringFlag{
				Name:     "url",
				Aliases:  []string{"u"},
				Usage:    "Sprite WebSocket URL (e.g., ws://localhost:8080 or https://sprite.example.com)",
				EnvVars:  []string{"SPRITE_URL"},
				Required: true,
			},
			&cli.StringFlag{
				Name:     "token",
				Aliases:  []string{"t"},
				Usage:    "Authentication token",
				EnvVars:  []string{"SPRITE_TOKEN"},
				Required: true,
			},
			&cli.StringFlag{
				Name:    "dir",
				Aliases: []string{"d"},
				Usage:   "Working directory for the command",
			},
			&cli.StringSliceFlag{
				Name:    "env",
				Aliases: []string{"e"},
				Usage:   "Environment variables (KEY=value)",
			},
			&cli.BoolFlag{
				Name:  "tty",
				Usage: "Force TTY mode (automatically detected for interactive programs)",
			},
			&cli.BoolFlag{
				Name:  "no-tty",
				Usage: "Disable TTY mode",
			},
		},
		Commands: []*cli.Command{
			{
				Name:  "nano",
				Usage: "Run nano text editor",
				Description: "Run the nano text editor inside a sprite environment. " +
					"All nano command line options are supported.",
				ArgsUsage: "[nano-options] [file...]",
				Action: func(ctx *cli.Context) error {
					// nano always needs TTY unless explicitly disabled
					tty := !ctx.Bool("no-tty")
					if ctx.Bool("tty") {
						tty = true
					}

					exitCode := runner.RunCommand(
						"nano",
						ctx.Args().Slice(),
						ctx.String("url"),
						ctx.String("token"),
						ctx.String("dir"),
						ctx.StringSlice("env"),
						tty,
					)
					os.Exit(exitCode)
					return nil
				},
			},
			{
				Name:  "sync",
				Usage: "Synchronize git repository to sprite environment",
				Description: "Synchronize the current git repository (or specified path) to the sprite environment. " +
					"By default, only committed files are synchronized. Use --include-uncommitted to include all files.",
				ArgsUsage: "[source-path]",
				Flags: []cli.Flag{
					&cli.StringFlag{
						Name:     "target",
						Aliases:  []string{"T"},
						Usage:    "Target directory in sprite environment",
						Required: true,
					},
					&cli.StringFlag{
						Name:    "branch",
						Aliases: []string{"b"},
						Usage:   "Specific branch to sync (defaults to current branch)",
					},
					&cli.BoolFlag{
						Name:    "include-uncommitted",
						Aliases: []string{"u"},
						Usage:   "Include uncommitted files in sync",
					},
				},
				Action: func(ctx *cli.Context) error {
					sourcePath := "."
					if ctx.Args().Len() > 0 {
						sourcePath = ctx.Args().First()
					}

					return runSyncCommand(
						sourcePath,
						ctx.String("target"),
						ctx.String("branch"),
						ctx.Bool("include-uncommitted"),
						ctx.String("url"),
						ctx.String("token"),
					)
				},
			},
			{
				Name:  "run",
				Usage: "Run any command",
				Description: "Run any command inside a sprite environment. " +
					"TTY mode is automatically detected based on the command.",
				ArgsUsage: "command [args...]",
				Action: func(ctx *cli.Context) error {
					if ctx.Args().Len() == 0 {
						return cli.Exit("Error: No command specified", 1)
					}

					cmd := ctx.Args().First()
					args := ctx.Args().Slice()[1:]

					// Auto-detect TTY mode based on command
					tty := shouldUseTTY(cmd)
					if ctx.Bool("tty") {
						tty = true
					}
					if ctx.Bool("no-tty") {
						tty = false
					}

					exitCode := runner.RunCommand(
						cmd,
						args,
						ctx.String("url"),
						ctx.String("token"),
						ctx.String("dir"),
						ctx.StringSlice("env"),
						tty,
					)
					os.Exit(exitCode)
					return nil
				},
			},
		},
		Action: func(ctx *cli.Context) error {
			// Default action when no subcommand is specified
			if ctx.Args().Len() == 0 {
				cli.ShowAppHelp(ctx)
				return nil
			}

			// Treat first argument as command if no subcommand matches
			cmd := ctx.Args().First()
			args := ctx.Args().Slice()[1:]

			// Auto-detect TTY mode
			tty := shouldUseTTY(cmd)
			if ctx.Bool("tty") {
				tty = true
			}
			if ctx.Bool("no-tty") {
				tty = false
			}

			exitCode := runner.RunCommand(
				cmd,
				args,
				ctx.String("url"),
				ctx.String("token"),
				ctx.String("dir"),
				ctx.StringSlice("env"),
				tty,
			)
			os.Exit(exitCode)
			return nil
		},
		ExitErrHandler: func(ctx *cli.Context, err error) {
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
		},
	}

	// Run the CLI application
	if err := app.Run(os.Args); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
}

// shouldUseTTY determines if a command should use TTY mode by default
func shouldUseTTY(cmd string) bool {
	// Interactive editors and shells typically need TTY
	interactiveCommands := []string{
		"nano", "vim", "vi", "emacs", "pico",
		"bash", "sh", "zsh", "fish",
		"htop", "top", "less", "more",
		"tmux", "screen",
	}

	for _, interactive := range interactiveCommands {
		if strings.Contains(cmd, interactive) {
			return true
		}
	}

	return false
}

// Simple logger implementation for sync client
type cliLogger struct {
	logger *slog.Logger
}

func (l *cliLogger) Info(msg string, args ...interface{}) {
	l.logger.Info(msg, args...)
}

func (l *cliLogger) Error(msg string, args ...interface{}) {
	l.logger.Error(msg, args...)
}

func (l *cliLogger) Debug(msg string, args ...interface{}) {
	l.logger.Debug(msg, args...)
} // runSyncCommand executes the sync command to synchronize a git repository

// runSyncCommand executes the sync command using WebSocket-based sync
func runSyncCommand(sourcePath, targetPath, branch string, includeUncommitted bool, spriteURL, token string) error {
	fmt.Printf("Starting sync from %s to %s\n", sourcePath, targetPath)

	// Create logger
	logger := &cliLogger{
		logger: slog.Default(),
	}

	// Create sync client config
	config := sync.ClientConfig{
		TargetPath:         targetPath,
		Branch:             branch,
		IncludeUncommitted: includeUncommitted,
		UploadChannels:     4,         // Use 4 parallel upload channels
		ChunkSize:          64 * 1024, // 64KB chunks
		Logger:             slog.Default(),
		ProgressCallback: func(progress sync.Progress) {
			fmt.Printf("\rProgress: %d/%d files, %d/%d bytes",
				progress.FilesProcessed, progress.FilesTotal,
				progress.BytesUploaded, progress.BytesTotal)
		},
	}

	// Create sync client
	client := sync.NewClient(sourcePath, config)

	// Perform sync
	ctx := context.Background()
	if err := client.Sync(ctx, spriteURL, token); err != nil {
		return fmt.Errorf("sync failed: %w", err)
	}

	fmt.Printf("\nSync completed successfully!\n")
	return nil
}
