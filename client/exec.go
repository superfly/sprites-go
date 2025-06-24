package main

import (
	"context"
	"flag"
	"fmt"
	"log/slog"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"strings"
	"syscall"
	"time"

	"github.com/sprite-env/packages/wsexec"
	"golang.org/x/term"
)

func execCommand(baseURL, token string, args []string) {
	// Create a new flag set for the exec subcommand
	execFlags := flag.NewFlagSet("exec", flag.ExitOnError)

	var (
		workingDir = execFlags.String("dir", "", "Working directory for the command")
		tty        = execFlags.Bool("tty", false, "Allocate a pseudo-TTY")
		envVars    = execFlags.String("env", "", "Environment variables (KEY=value,KEY2=value2)")
		debug      = execFlags.Bool("debug", false, "Enable debug logging")
		help       = execFlags.Bool("h", false, "Show help")
	)

	// Custom usage for exec subcommand
	execFlags.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: sprite-client exec [options] command [args...]\n\n")
		fmt.Fprintf(os.Stderr, "Execute a command in the sprite environment.\n\n")
		fmt.Fprintf(os.Stderr, "Options:\n")
		execFlags.PrintDefaults()
		fmt.Fprintf(os.Stderr, "\nExamples:\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec ls -la\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -dir /app echo hello world\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -env KEY=value,FOO=bar env\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -tty /bin/bash\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -debug echo hello  # Enable debug logging\n")
	}

	// Parse exec flags
	err := execFlags.Parse(args)
	if err != nil {
		os.Exit(1)
	}

	// Check for help flag
	if *help {
		execFlags.Usage()
		os.Exit(0)
	}

	// Get remaining args as command
	cmdArgs := execFlags.Args()
	if len(cmdArgs) == 0 {
		fmt.Fprintf(os.Stderr, "Error: No command specified\n\n")
		execFlags.Usage()
		os.Exit(1)
	}

	// Parse environment variables
	var envList []string
	if *envVars != "" {
		pairs := strings.Split(*envVars, ",")
		for _, pair := range pairs {
			envList = append(envList, strings.TrimSpace(pair))
		}
	}

	// Execute using direct WebSocket connection
	exitCode := executeDirectWebSocket(baseURL, token, cmdArgs, *workingDir, envList, *tty, *debug)
	os.Exit(exitCode)
}

// handlePTYMode sets up the terminal for PTY mode and returns a cleanup function
func handlePTYMode(wsCmd *wsexec.Cmd, debug bool) (cleanup func(), sendInitialSize func(), err error) {
	// Check if stdin is a terminal
	if !term.IsTerminal(int(os.Stdin.Fd())) {
		// Not a terminal, no special handling needed
		return func() {}, func() {}, nil
	}

	// Save the current terminal state
	oldState, err := term.MakeRaw(int(os.Stdin.Fd()))
	if err != nil {
		return nil, nil, fmt.Errorf("failed to set terminal to raw mode: %w", err)
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
			// Get current terminal size
			width, height, err := term.GetSize(int(os.Stdout.Fd()))
			if err != nil {
				if debug {
					fmt.Fprintf(os.Stderr, "Failed to get terminal size: %v\n", err)
				}
				continue
			}

			// Send resize command
			if err := wsCmd.Resize(uint16(width), uint16(height)); err != nil {
				if debug {
					fmt.Fprintf(os.Stderr, "Failed to send resize: %v\n", err)
				}
			}
		}
	}()

	// Function to send initial size (to be called after WebSocket is connected)
	sendInitialSize = func() {
		if width, height, err := term.GetSize(int(os.Stdout.Fd())); err == nil {
			if debug {
				fmt.Fprintf(os.Stderr, "Sending initial terminal size: %dx%d\n", width, height)
			}
			if err := wsCmd.Resize(uint16(width), uint16(height)); err != nil && debug {
				fmt.Fprintf(os.Stderr, "Failed to send initial size: %v\n", err)
			}
		}
	}

	return cleanup, sendInitialSize, nil
}

func executeDirectWebSocket(baseURL, token string, cmd []string, workingDir string, env []string, tty bool, debug bool) int {
	// Set up debug logging if enabled
	var logger *slog.Logger
	if debug {
		logger = slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
			Level: slog.LevelDebug,
		}))
		logger.Info("Debug mode enabled")
		logger.Debug("Starting WebSocket exec",
			"baseURL", baseURL,
			"cmd", cmd,
			"workingDir", workingDir,
			"env", env,
			"tty", tty)
	}

	// Build WebSocket URL - directly to /exec endpoint
	wsURL, err := buildExecWebSocketURL(baseURL)
	if err != nil {
		if debug {
			logger.Error("Failed to build WebSocket URL", "error", err)
		}
		fmt.Fprintf(os.Stderr, "Error: Failed to build WebSocket URL: %v\n", err)
		return 1
	}

	if debug {
		logger.Debug("Built WebSocket URL", "url", wsURL.String())
	}

	// Add command arguments as query parameters
	// This is how wsexec expects command configuration to be sent
	query := wsURL.Query()
	for i, arg := range cmd {
		query.Add("cmd", arg)
		if i == 0 {
			query.Set("path", arg) // Set the main command path
		}
	}
	if workingDir != "" {
		query.Set("dir", workingDir)
		if debug {
			logger.Debug("Set working directory", "dir", workingDir)
		}
	}
	if tty {
		query.Set("tty", "true")
		if debug {
			logger.Debug("Enabled TTY mode")
		}
	}
	for _, envVar := range env {
		query.Add("env", envVar)
		if debug {
			logger.Debug("Added environment variable", "env", envVar)
		}
	}
	wsURL.RawQuery = query.Encode()

	if debug {
		logger.Debug("Final WebSocket URL with query parameters", "url", wsURL.String())
	}

	// Create HTTP request with auth header
	req, err := http.NewRequest("GET", wsURL.String(), nil)
	if err != nil {
		if debug {
			logger.Error("Failed to create HTTP request", "error", err)
		}
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		return 1
	}
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	if debug {
		logger.Debug("Created HTTP request", "method", req.Method, "url", req.URL.String())
		logger.Debug("Request headers", "headers", req.Header)
	}

	// Create wsexec command - don't duplicate the command arguments
	// wsexec will get the command info from the URL query parameters
	wsCmd := wsexec.CommandContext(context.Background(), req, "placeholder")

	// Set client-side I/O configuration
	wsCmd.Stdin = os.Stdin
	wsCmd.Stdout = os.Stdout
	wsCmd.Stderr = os.Stderr

	if debug {
		logger.Debug("Created wsexec command",
			"request_url", wsCmd.Request.URL.String())

		// Set a shorter ping interval for debug mode
		wsCmd.PingInterval = 1 * time.Second
		logger.Debug("Set ping interval for debug mode", "interval", wsCmd.PingInterval)
	}

	if debug {
		logger.Info("Starting WebSocket command execution")
	}

	// Set up PTY mode if needed
	var cleanup func()
	var sendInitialSize func()
	if tty {
		var err error
		cleanup, sendInitialSize, err = handlePTYMode(wsCmd, debug)
		if err != nil {
			if debug {
				logger.Error("Failed to set up PTY mode", "error", err)
			}
			fmt.Fprintf(os.Stderr, "Warning: Failed to set up PTY mode: %v\n", err)
			// Continue anyway - PTY will work but without raw mode
		}
		defer func() {
			if cleanup != nil {
				cleanup()
			}
		}()
	}

	// Start the command
	if err := wsCmd.Start(); err != nil {
		if debug {
			logger.Error("Failed to start WebSocket command", "error", err)
		}
		fmt.Fprintf(os.Stderr, "Error: Failed to start command: %v\n", err)
		return 1
	}

	// Send initial terminal size after connection is established
	if sendInitialSize != nil {
		// Give the connection a moment to establish
		time.Sleep(100 * time.Millisecond)
		sendInitialSize()
	}

	// Wait for command to complete
	if err := wsCmd.Wait(); err != nil {
		if debug {
			logger.Error("WebSocket command wait failed", "error", err)
		}
		// Don't print error here - it's usually just context cancelled
	}

	// Get exit code
	exitCode := wsCmd.ExitCode()
	if debug {
		logger.Debug("Command completed", "exitCode", exitCode)
	}

	if exitCode == -1 {
		if debug {
			logger.Warn("No proper exit code received, defaulting to 1")
		}
		// If we didn't get a proper exit code, default to 1
		exitCode = 1
	}

	if debug {
		logger.Info("WebSocket exec completed", "finalExitCode", exitCode)
	}

	return exitCode
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
	default:
		return nil, fmt.Errorf("unsupported scheme: %s", u.Scheme)
	}

	// Set path to simple /exec endpoint
	u.Path = "/exec"

	return u, nil
}
