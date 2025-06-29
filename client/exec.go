package main

import (
	"context"
	"flag"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"os/signal"
	"strings"
	"sync"
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
		help       = execFlags.Bool("h", false, "Show help")
	)

	// Custom usage for exec subcommand
	execFlags.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: sprite-client exec [options] command [args...]\n\n")
		fmt.Fprintf(os.Stderr, "Execute a command in the sprite environment.\n\n")
		fmt.Fprintf(os.Stderr, "Options:\n")
		execFlags.PrintDefaults()
		fmt.Fprintf(os.Stderr, "\nNotes:\n")
		fmt.Fprintf(os.Stderr, "  When using -tty, terminal environment variables (TERM, COLORTERM, LANG, LC_ALL)\n")
		fmt.Fprintf(os.Stderr, "  are automatically passed through from your local environment.\n")
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

	// When using TTY mode, automatically include essential terminal environment variables
	if *tty {
		terminalEnvVars := []string{"TERM", "COLORTERM", "LANG", "LC_ALL"}
		for _, envVar := range terminalEnvVars {
			if value := os.Getenv(envVar); value != "" {
				// Check if this env var is already explicitly set
				envVar = envVar + "=" + value
				alreadySet := false
				for _, existing := range envList {
					if strings.HasPrefix(existing, strings.Split(envVar, "=")[0]+"=") {
						alreadySet = true
						break
					}
				}
				if !alreadySet {
					envList = append(envList, envVar)
				}
			}
		}
	}

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

	// Logger instance shared across client
	logger := slog.Default()
	logger.Debug("Starting WebSocket exec",
		"baseURL", baseURL,
		"cmd", cmdArgs,
		"workingDir", *workingDir,
		"env", envList,
		"tty", *tty)

	// Build WebSocket URL - directly to /exec endpoint
	wsURL, err := buildExecWebSocketURL(baseURL)
	if err != nil {
		logger.Error("Failed to build WebSocket URL", "error", err)
		fmt.Fprintf(os.Stderr, "Error: Failed to build WebSocket URL: %v\n", err)
		return
	}

	logger.Debug("Built WebSocket URL", "url", wsURL.String())

	// Add command arguments as query parameters
	// This is how wsexec expects command configuration to be sent
	query := wsURL.Query()
	for i, arg := range cmdArgs {
		query.Add("cmd", arg)
		if i == 0 {
			query.Set("path", arg) // Set the main command path
		}
	}
	if *workingDir != "" {
		query.Set("dir", *workingDir)
		logger.Debug("Set working directory", "dir", *workingDir)
	}
	if *tty {
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
	for _, envVar := range envList {
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
		return
	}
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	logger.Debug("Created HTTP request", "method", req.Method, "url", req.URL.String())
	// Log headers but redact Authorization for security
	headersCopy := make(map[string][]string)
	for k, v := range req.Header {
		if k == "Authorization" {
			headersCopy[k] = []string{"[REDACTED]"}
		} else {
			headersCopy[k] = v
		}
	}
	logger.Debug("Request headers", "headers", headersCopy)

	// Create wsexec command
	wsCmd := wsexec.CommandContext(context.Background(), req, "placeholder")

	// Set client-side I/O configuration
	wsCmd.Stdin = os.Stdin
	wsCmd.Stdout = os.Stdout
	wsCmd.Stderr = os.Stderr
	wsCmd.Tty = *tty

	// Set up browser handler for TTY mode
	if *tty {
		wsCmd.BrowserOpen = handleBrowserOpen
	}

	logger.Debug("Created wsexec command", "tty", wsCmd.Tty)

	// Set up PTY mode if needed
	var cleanup func()
	if *tty {
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

	logger.Info("Starting WebSocket command execution")

	// Start the command
	if err := wsCmd.Start(); err != nil {
		logger.Error("Failed to start WebSocket command", "error", err)
		fmt.Fprintf(os.Stderr, "Error: Failed to start command: %v\n", err)
		return
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

	logger.Info("WebSocket exec completed", "finalExitCode", exitCode)

	// Restore terminal state before exiting
	if initialState != nil {
		term.Restore(int(os.Stdin.Fd()), initialState)
	}

	os.Exit(exitCode)
}

// handlePTYMode sets up the terminal for PTY mode and returns a cleanup function
func handlePTYMode(wsCmd *wsexec.Cmd) (cleanup func(), err error) {
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

	// Note: Initial terminal size is now sent as part of WebSocket connection setup,
	// so we don't need to send it again here. The Resize call would be redundant.

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

func executeDirectWebSocket(baseURL, token string, cmd []string, workingDir string, env []string, tty bool) int {
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
	logger.Info("Debug mode enabled")
	logger.Debug("Starting WebSocket exec", "baseURL", baseURL, "cmd", cmd, "workingDir", workingDir, "env", env, "tty", tty)

	// Build WebSocket URL - directly to /exec endpoint
	wsURL, err := buildExecWebSocketURL(baseURL)
	if err != nil {
		logger.Error("Failed to build WebSocket URL", "error", err)
		fmt.Fprintf(os.Stderr, "Error: Failed to build WebSocket URL: %v\n", err)
		return 1
	}

	logger.Debug("Built WebSocket URL", "url", wsURL.String())

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

	logger.Debug("Created HTTP request", "method", req.Method, "url", req.URL.String())
	// Log headers but redact Authorization for security
	headersCopy := make(map[string][]string)
	for k, v := range req.Header {
		if k == "Authorization" {
			headersCopy[k] = []string{"[REDACTED]"}
		} else {
			headersCopy[k] = v
		}
	}
	logger.Debug("Request headers", "headers", headersCopy)

	// Create wsexec command
	wsCmd := wsexec.CommandContext(context.Background(), req, "placeholder")

	// Set client-side I/O configuration
	wsCmd.Stdin = os.Stdin
	wsCmd.Stdout = os.Stdout
	wsCmd.Stderr = os.Stderr
	wsCmd.Tty = tty

	// Set up browser handler for TTY mode
	if tty {
		wsCmd.BrowserOpen = handleBrowserOpen
	}

	logger.Debug("Created wsexec command", "tty", wsCmd.Tty)

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

	logger.Info("Starting WebSocket command execution")

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

	logger.Info("WebSocket exec completed", "finalExitCode", exitCode)

	// Restore terminal state before exiting
	if initialState != nil {
		term.Restore(int(os.Stdin.Fd()), initialState)
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

	// Append /exec to any existing path while preserving prefix paths
	cleanPath := strings.TrimRight(u.Path, "/")
	if cleanPath == "" {
		u.Path = "/exec"
	} else {
		u.Path = cleanPath + "/exec"
	}

	return u, nil
}

// handleBrowserOpen handles browser open requests from the container
func handleBrowserOpen(url string, ports []string) {
	logger := slog.Default()
	logger.Info("Browser open request received", "url", url, "ports", ports)

	// Start HTTP servers on specified ports if any are provided
	var servers []*http.Server
	var serverReady sync.WaitGroup

	if len(ports) > 0 {
		logger.Info("Starting callback servers", "ports", ports)

		for _, portStr := range ports {
			port := strings.TrimSpace(portStr)
			if port == "" {
				continue
			}

			// Start server for this port
			server := &http.Server{
				Addr: ":" + port,
			}

			// Set up handler for this server
			mux := http.NewServeMux()
			mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
				logger.Info("OAuth callback received", "port", port, "url", r.URL.String(), "method", r.Method)

				// Show notification using AppleScript
				notificationTitle := "OAuth Callback Received"
				notificationText := fmt.Sprintf("Received request on port %s: %s", port, r.URL.Path)
				cmd := exec.Command("osascript", "-e",
					fmt.Sprintf(`display notification "%s" with title "%s"`, notificationText, notificationTitle))
				if err := cmd.Run(); err != nil {
					logger.Warn("Failed to show notification", "error", err)
				}

				// Serve "not implemented" response
				w.Header().Set("Content-Type", "text/html")
				w.WriteHeader(http.StatusNotImplemented)
				fmt.Fprintf(w, `<!DOCTYPE html>
<html>
<head>
    <title>OAuth Callback - Not Implemented</title>
    <style>
        body { font-family: Arial, sans-serif; max-width: 600px; margin: 50px auto; padding: 20px; }
        .message { background: #f0f0f0; padding: 20px; border-radius: 5px; }
        .details { margin-top: 20px; font-size: 0.9em; color: #666; }
    </style>
</head>
<body>
    <div class="message">
        <h2>OAuth Callback Received</h2>
        <p>The OAuth callback was successfully received but is not yet implemented.</p>
        <div class="details">
            <strong>Port:</strong> %s<br>
            <strong>Path:</strong> %s<br>
            <strong>Method:</strong> %s<br>
            <strong>Time:</strong> %s
        </div>
    </div>
</body>
</html>`, port, r.URL.Path, r.Method, time.Now().Format("2006-01-02 15:04:05"))

				// Shutdown this server after serving the response
				go func() {
					time.Sleep(100 * time.Millisecond) // Give response time to be sent
					logger.Info("Shutting down callback server", "port", port)
					server.Shutdown(context.Background())
				}()
			})
			server.Handler = mux

			// Start server in background
			serverReady.Add(1)
			go func(s *http.Server, p string) {
				defer serverReady.Done()

				// Try to start the server
				listener, err := net.Listen("tcp", s.Addr)
				if err != nil {
					logger.Error("Failed to start callback server", "port", p, "error", err)
					return
				}

				logger.Info("Callback server ready", "port", p, "addr", listener.Addr())

				// Server is ready, signal completion
				go func() {
					if err := s.Serve(listener); err != nil && err != http.ErrServerClosed {
						logger.Error("Callback server error", "port", p, "error", err)
					}
				}()
			}(server, port)

			servers = append(servers, server)
		}

		// Wait for all servers to be ready
		logger.Info("Waiting for callback servers to be ready...")
		serverReady.Wait()
		logger.Info("All callback servers ready, opening browser")
	}

	// Open the browser
	var cmd *exec.Cmd
	switch {
	case os.Getenv("WSL_DISTRO_NAME") != "":
		// WSL - use Windows browser
		cmd = exec.Command("cmd.exe", "/c", "start", url)
	case isCommandAvailable("xdg-open"):
		// Linux
		cmd = exec.Command("xdg-open", url)
	case isCommandAvailable("open"):
		// macOS
		cmd = exec.Command("open", url)
	default:
		logger.Error("Unable to detect browser command")
		fmt.Fprintf(os.Stderr, "sprite: unable to detect browser command\n")
		return
	}

	logger.Info("Opening browser", "url", url)
	if err := cmd.Start(); err != nil {
		logger.Error("Failed to open browser", "error", err)
		fmt.Fprintf(os.Stderr, "sprite: failed to open browser: %v\n", err)
	} else {
		logger.Info("Browser opened successfully")
	}

	// Clean up servers after a reasonable timeout if they haven't shut down already
	if len(servers) > 0 {
		go func() {
			time.Sleep(5 * time.Minute) // Give OAuth flow time to complete
			for _, server := range servers {
				server.Shutdown(context.Background())
			}
			logger.Info("Cleaned up callback servers after timeout")
		}()
	}
}

// isCommandAvailable checks if a command is available in PATH
func isCommandAvailable(name string) bool {
	_, err := exec.LookPath(name)
	return err == nil
}
