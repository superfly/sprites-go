package commands

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"time"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/pkg/terminal"
	"golang.org/x/term"
)

// PortNotificationMessage represents a port event notification from the server
type PortNotificationMessage struct {
	Type    string `json:"type"`    // "port_opened" or "port_closed"
	Port    int    `json:"port"`    // Port number
	Address string `json:"address"` // Address (e.g., "127.0.0.1", "0.0.0.0")
	PID     int    `json:"pid"`     // Process ID
}

// portManager manages active port proxies
type portManager struct {
	proxies map[int]*portProxy // key: port number
	logger  *slog.Logger
	config  ProxyConfig // Proxy configuration for WebSocket connections

	// Channel-based communication instead of mutexes
	actionCh chan portAction
	stopCh   chan struct{}
}

type portProxy struct {
	port     int
	address  string
	listener net.Listener
	cancel   context.CancelFunc
}

type portAction struct {
	action   string // "start", "stop", "cleanup"
	port     int
	address  string
	response chan error // for synchronous operations
}

func newPortManager(logger *slog.Logger, config ProxyConfig) *portManager {
	pm := &portManager{
		proxies:  make(map[int]*portProxy),
		logger:   logger,
		config:   config,
		actionCh: make(chan portAction, 10),
		stopCh:   make(chan struct{}),
	}

	// Start the management goroutine
	go pm.run()

	return pm
}

func (pm *portManager) run() {
	for {
		select {
		case <-pm.stopCh:
			// Cleanup all proxies before shutting down
			for port, proxy := range pm.proxies {
				pm.logger.Debug("Cleaning up proxy during shutdown", "port", port)
				proxy.cancel()
				proxy.listener.Close()
			}
			pm.proxies = make(map[int]*portProxy)
			return

		case action := <-pm.actionCh:
			var err error

			switch action.action {
			case "start":
				err = pm.doStartProxy(action.port, action.address)
			case "stop":
				err = pm.doStopProxy(action.port)
			case "cleanup":
				pm.doCleanup()
			}

			if action.response != nil {
				action.response <- err
			}
		}
	}
}

func (pm *portManager) handlePortNotification(data []byte) {
	var notification PortNotificationMessage
	if err := json.Unmarshal(data, &notification); err != nil {
		pm.logger.Debug("Failed to parse port notification", "error", err, "data", string(data))
		return
	}

	pm.logger.Debug("Received port notification", "type", notification.Type, "port", notification.Port, "address", notification.Address, "pid", notification.PID)

	switch notification.Type {
	case "port_opened":
		pm.logger.Info("Port opened, starting proxy", "port", notification.Port, "address", notification.Address, "pid", notification.PID)
		pm.startProxy(notification.Port, notification.Address)
	case "port_closed":
		pm.logger.Info("Port closed, stopping proxy", "port", notification.Port, "pid", notification.PID)
		pm.stopProxy(notification.Port)
	default:
		pm.logger.Debug("Unknown port notification type", "type", notification.Type)
	}
}

func (pm *portManager) startProxy(port int, address string) {
	// Send async action
	select {
	case pm.actionCh <- portAction{action: "start", port: port, address: address}:
	case <-pm.stopCh:
	}
}

func (pm *portManager) stopProxy(port int) {
	// Send async action
	select {
	case pm.actionCh <- portAction{action: "stop", port: port}:
	case <-pm.stopCh:
	}
}

func (pm *portManager) cleanup() {
	// Send stop signal
	close(pm.stopCh)
}

func (pm *portManager) doStartProxy(port int, address string) error {
	// Check if we're already proxying this port
	if _, exists := pm.proxies[port]; exists {
		pm.logger.Debug("Port proxy already active", "port", port)
		return nil
	}

	// Validate and normalize the address for logging
	normalizedAddress := address
	if address == "" || address == "0.0.0.0" || address == "::" {
		normalizedAddress = "127.0.0.1"
	}

	pm.logger.Info("Starting automatic proxy", "port", port, "originalAddress", address, "normalizedAddress", normalizedAddress)

	// Start local listener
	listener, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", port))
	if err != nil {
		pm.logger.Error("Failed to start proxy listener", "port", port, "error", err)
		return err
	}

	// Create context for cancellation
	ctx, cancel := context.WithCancel(context.Background())

	proxy := &portProxy{
		port:     port,
		address:  address,
		listener: listener,
		cancel:   cancel,
	}

	pm.proxies[port] = proxy

	// Start proxy in background
	go func() {
		defer func() {
			// Remove from map when proxy stops
			select {
			case pm.actionCh <- portAction{action: "stop", port: port}:
			case <-pm.stopCh:
			}
		}()

		pm.logger.Debug("Proxy listener started", "localAddr", listener.Addr().String(), "remotePort", port)

		for {
			select {
			case <-ctx.Done():
				return
			default:
			}

			conn, err := listener.Accept()
			if err != nil {
				select {
				case <-ctx.Done():
					return // Context cancelled, expected error
				default:
					pm.logger.Error("Failed to accept proxy connection", "port", port, "error", err)
					return
				}
			}

			// Handle connection in background
			go pm.handleProxyConnection(ctx, conn, port, address)
		}
	}()

	fmt.Printf("🔗 Automatically proxying port %d → http://localhost:%d\n", port, port)

	if false /* this should be triggered by OSC */ {

		// Auto-open browser to the proxied port
		handleBrowserOpen(fmt.Sprintf("http://localhost:%d", port), nil)
		// don't pass the port in:
		// 	[]string{fmt.Sprintf("%d", port)},
		// )
	}

	return nil
}

func (pm *portManager) doStopProxy(port int) error {
	proxy, exists := pm.proxies[port]
	if !exists {
		pm.logger.Debug("No proxy found for port", "port", port)
		return nil
	}

	pm.logger.Info("Stopping automatic proxy", "port", port)

	// Cancel the context to stop accepting new connections
	proxy.cancel()

	// Close the listener
	proxy.listener.Close()

	// Remove from map
	delete(pm.proxies, port)

	fmt.Printf("🔌 Stopped proxying port %d\n", port)
	return nil
}

func (pm *portManager) doCleanup() {
	for port, proxy := range pm.proxies {
		pm.logger.Debug("Cleaning up proxy", "port", port)
		proxy.cancel()
		proxy.listener.Close()
	}
	pm.proxies = make(map[int]*portProxy)
}

func (pm *portManager) handleProxyConnection(ctx context.Context, localConn net.Conn, port int, address string) {
	// Use the existing proxy implementation
	HandleProxyConnection(localConn, port, pm.config)
}

// ExecCommand handles the exec command
func ExecCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "exec",
		Usage:       "exec [options] command [args...]",
		Description: "Execute a command in the sprite environment",
		FlagSet:     flag.NewFlagSet("exec", flag.ContinueOnError),
		Examples: []string{
			"sprite exec ls -la",
			"sprite exec -dir /app echo hello world",
			"sprite exec -env KEY=value,FOO=bar env",
			"sprite exec -tty /bin/bash",
			"sprite exec -o myorg -s mysprite npm start",
			"sprite exec -detachable /bin/bash  # Create detachable session (auto ID: 1, 2, 3...)",
			"sprite exec -detachable -cc /bin/bash  # Create with tmux control mode",
			"sprite exec -id 3  # Attach to existing tmux session",
			"sprite exec -id 3 -cc  # Attach with tmux control mode",
		},
		Notes: []string{
			"When using -tty, terminal environment variables (TERM, COLORTERM, LANG, LC_ALL)",
			"are automatically passed through from your local environment.",
			"",
			"Detachable sessions create tmux sessions with auto-incrementing IDs (1, 2, 3, etc).",
			"Use -id with a numeric ID to attach to an existing tmux session.",
			"Both -detachable and -id automatically enable TTY mode.",
			"",
			"The -cc flag enables tmux control mode, allowing compatible terminals to use",
			"native tabs and windows. Requires -detachable or -id flag.",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)
	workingDir := cmd.FlagSet.String("dir", "", "Working directory for the command")
	tty := cmd.FlagSet.Bool("tty", false, "Allocate a pseudo-TTY")
	envVars := cmd.FlagSet.String("env", "", "Environment variables (KEY=value,KEY2=value2)")
	detachable := cmd.FlagSet.Bool("detachable", false, "Create a detachable tmux session")
	sessionID := cmd.FlagSet.String("id", "", "Attach to existing tmux session by numeric ID")
	controlMode := cmd.FlagSet.Bool("cc", false, "Use tmux control mode (requires -detachable or -id)")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Use global context overrides if available
	orgOverride := flags.Org
	if ctx.OrgOverride != "" {
		orgOverride = ctx.OrgOverride
	}
	spriteOverride := flags.Sprite
	if ctx.SpriteOverride != "" {
		spriteOverride = ctx.SpriteOverride
	}

	// Validate control mode flag
	if *controlMode && *sessionID == "" && !*detachable {
		fmt.Fprintf(os.Stderr, "Error: -cc flag requires either -detachable or -id flag\n")
		os.Exit(1)
	}

	// Ensure we have an org and sprite (needed for all operations)
	org, spriteName, err := EnsureOrgAndSpriteWithContext(ctx, orgOverride, spriteOverride)
	if err != nil {
		// Check if it's a cancellation error
		if strings.Contains(err.Error(), "cancelled") {
			handlePromptError(err)
		} else {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
		os.Exit(1)
	}

	// Check for remaining args as command
	// When using -id, we're attaching to an existing session and don't need a command
	// When using -detachable, we need a command to run
	// When no args and no session flags, list available sessions
	if len(remainingArgs) == 0 {
		if *sessionID == "" && !*detachable {
			// No command specified and no session flags - list available sessions from server

			// Build the API URL for listing sessions
			apiURL := fmt.Sprintf("%s/exec", org.URL)

			// Create HTTP request
			httpReq, err := http.NewRequest("GET", apiURL, nil)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error creating request: %v\n", err)
				os.Exit(1)
			}

			// Add authentication
			token, err := org.GetToken()
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: Failed to get authentication token: %v\n", err)
				os.Exit(1)
			}
			httpReq.Header.Set("Authorization", "Bearer "+token)

			// Make the request
			client := &http.Client{Timeout: 30 * time.Second}
			resp, err := client.Do(httpReq)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error listing sessions: %v\n", err)
				os.Exit(1)
			}
			defer resp.Body.Close()

			// Check response status
			if resp.StatusCode != http.StatusOK {
				body, _ := io.ReadAll(resp.Body)
				fmt.Fprintf(os.Stderr, "Error: Server returned %d: %s\n", resp.StatusCode, string(body))
				os.Exit(1)
			}

			// Parse JSON response
			var result map[string]interface{}
			if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
				fmt.Fprintf(os.Stderr, "Error parsing response: %v\n", err)
				os.Exit(1)
			}

			// Display sessions
			sessions, ok := result["sessions"].([]interface{})
			if !ok {
				sessions = []interface{}{}
			}

			if len(sessions) == 0 {
				fmt.Println("No active tmux sessions found.")
				fmt.Println("\nTo create a new detachable session:")
				fmt.Println("  sprite exec -detachable /bin/bash")
				fmt.Println("  sprite exec -detachable <command>")
			} else {
				// Display sessions in a table
				fmt.Printf("Active tmux sessions (%d):\n\n", len(sessions))

				// Print table header
				fmt.Printf("%-6s %-20s %-30s\n", "ID", "Command", "Started")
				fmt.Printf("%-6s %-20s %-30s\n", "──", "───────", "───────")

				// Print each session
				for _, s := range sessions {
					if session, ok := s.(map[string]interface{}); ok {
						id := session["id"]
						command := session["command"]

						// Parse and format the created time
						var startedStr string
						if created, ok := session["created"].(string); ok {
							if t, err := time.Parse(time.RFC3339, created); err == nil {
								// Calculate duration
								duration := time.Since(t)
								if duration < time.Minute {
									startedStr = fmt.Sprintf("%d seconds ago", int(duration.Seconds()))
								} else if duration < time.Hour {
									startedStr = fmt.Sprintf("%d minutes ago", int(duration.Minutes()))
								} else if duration < 24*time.Hour {
									startedStr = fmt.Sprintf("%d hours ago", int(duration.Hours()))
								} else {
									startedStr = fmt.Sprintf("%d days ago", int(duration.Hours()/24))
								}
							} else {
								startedStr = created
							}
						}

						// Truncate command if too long
						cmdStr := fmt.Sprintf("%v", command)
						if len(cmdStr) > 20 {
							cmdStr = cmdStr[:17] + "..."
						}

						fmt.Printf("%-6v %-20s %-30s\n", id, cmdStr, startedStr)
					}
				}

				fmt.Println("\nTo attach to a session:")
				fmt.Println("  sprite exec -id <session_id>")
				fmt.Println("\nTo create a new detachable session:")
				fmt.Println("  sprite exec -detachable <command>")
			}

			os.Exit(0)
		}
		// If only -id is specified, we're attaching to an existing session
		// No command needed in this case
	}

	// Session attachments and detachable sessions require TTY
	if *sessionID != "" || *detachable {
		*tty = true
	}

	// Debug: Log what we got
	if ctx.IsDebugEnabled() {
		fmt.Printf("DEBUG: After EnsureOrgAndSpriteWithContext:\n")
		fmt.Printf("  org.Name='%s', org.URL='%s'\n", org.Name, org.URL)
		fmt.Printf("  spriteName='%s'\n", spriteName)
		fmt.Printf("  flags.Sprite='%s' (from command flags)\n", flags.Sprite)
		fmt.Printf("  spriteOverride='%s' (final override used)\n", spriteOverride)
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

	// Build command string for display
	cmdStr := strings.Join(remainingArgs, " ")
	if len(cmdStr) > 50 {
		cmdStr = cmdStr[:47] + "..."
	}

	// Only print connection messages if debug logging is enabled
	if ctx.IsDebugEnabled() || *sessionID != "" || *detachable {
		fmt.Println()
		if spriteName != "" {
			// Config-based connection with org and sprite
			if org.Name != "env" {
				fmt.Printf("Connecting to %s sprite %s...\n",
					format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
					format.Sprite(spriteName))
			} else {
				// Just sprite name if using env vars
				fmt.Printf("Connecting to sprite %s...\n", format.Sprite(spriteName))
			}
			fmt.Printf("Running: %s\n", format.Command(cmdStr))
		} else {
			// Environment variable based connection (no sprite tracking)
			fmt.Printf("Running: %s\n", format.Command(cmdStr))
		}

		// Print session information
		if *detachable {
			fmt.Printf("\n📌 Creating detachable tmux session...\n")
		} else if *sessionID != "" {
			fmt.Printf("\n🔗 Attaching to tmux session: %s\n", format.Sprite(*sessionID))
		}

		fmt.Println()
	}

	// Execute the command
	var exitCode int
	if spriteName != "" {
		// Use the new sprite proxy endpoint when we have a sprite name
		exitCode = executeSpriteProxy(org, spriteName, remainingArgs, *workingDir, envList, *tty, *detachable, *sessionID, *controlMode)
	} else {
		// Use direct WebSocket for backward compatibility with SPRITE_URL/SPRITE_TOKEN
		token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
			os.Exit(1)
		}
		exitCode = executeDirectWebSocket(org.URL, token, remainingArgs, *workingDir, envList, *tty, *detachable, *sessionID, *controlMode)
	}

	os.Exit(exitCode)
}

// executeSpriteProxy executes a command through the sprite proxy endpoint
func executeSpriteProxy(org *config.Organization, spriteName string, cmd []string, workingDir string, env []string, tty bool, detachable bool, sessionID string, controlMode bool) int {
	// Build the proxy URL for exec endpoint
	baseURL := buildSpriteProxyURL(org, spriteName, "/exec")

	// Convert to WebSocket URL
	wsURL, err := convertToWebSocketURL(baseURL)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to build WebSocket URL: %v\n", err)
		return 1
	}

	// Use the existing WebSocket execution logic
	token, err := org.GetToken()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		return 1
	}
	return executeWebSocket(wsURL, token, cmd, workingDir, env, tty, detachable, sessionID, controlMode)
}

func executeDirectWebSocket(baseURL, token string, cmd []string, workingDir string, env []string, tty bool, detachable bool, sessionID string, controlMode bool) int {
	// Build WebSocket URL - directly to /exec endpoint
	wsURL, err := buildExecWebSocketURL(baseURL)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to build WebSocket URL: %v\n", err)
		return 1
	}

	return executeWebSocket(wsURL, token, cmd, workingDir, env, tty, detachable, sessionID, controlMode)
}

// executeWebSocket is the common WebSocket execution logic
func executeWebSocket(wsURL *url.URL, token string, cmd []string, workingDir string, env []string, tty bool, detachable bool, sessionID string, controlMode bool) int {
	// We need to build a proxy config based on the exec URL
	// Convert the exec WebSocket URL back to HTTP for the proxy
	proxyBaseURL := strings.Replace(wsURL.String(), "/exec", "/proxy", 1)
	proxyBaseURL = strings.Replace(proxyBaseURL, "ws://", "http://", 1)
	proxyBaseURL = strings.Replace(proxyBaseURL, "wss://", "https://", 1)
	// Remove query parameters
	if idx := strings.Index(proxyBaseURL, "?"); idx != -1 {
		proxyBaseURL = proxyBaseURL[:idx]
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
	if detachable {
		query.Set("detachable", "true")
		logger.Debug("Enabled detachable session")
	}
	if sessionID != "" {
		query.Set("id", sessionID)
		logger.Debug("Set session ID", "sessionID", sessionID)
	}
	if controlMode {
		query.Set("cc", "true")
		logger.Debug("Enabled tmux control mode")
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

	// Set up browser handler for TTY mode
	if tty {
		wsCmd.BrowserOpen = handleBrowserOpen
	}

	// Set up port manager for automatic proxying
	proxyConfig := ProxyConfig{
		BaseURL: proxyBaseURL,
		Token:   token,
		Logger:  logger,
	}
	portMgr := newPortManager(logger, proxyConfig)
	defer portMgr.cleanup()

	// Set up text message handler for port notifications
	wsCmd.TextMessageHandler = portMgr.handlePortNotification

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

	// Handle terminal resize (platform-specific)
	handleTerminalResize(wsCmd)

	return cleanup, nil
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

// convertToWebSocketURL converts HTTP/HTTPS URL to WS/WSS URL
func convertToWebSocketURL(httpURL string) (*url.URL, error) {
	u, err := url.Parse(httpURL)
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

	return u, nil
}

// handleBrowserOpen handles browser open requests from the container
func handleBrowserOpen(url string, ports []string) {
	logger := slog.Default()
	logger.Debug("Browser open request received", "url", url, "ports", ports)

	// Start HTTP servers on specified ports if any are provided
	var servers []*http.Server
	var serverReady sync.WaitGroup

	if len(ports) > 0 {
		logger.Debug("Starting callback servers", "ports", ports)

		for _, portStr := range ports {
			port := strings.TrimSpace(portStr)
			if port == "" {
				continue
			}

			listener, err := net.Listen("tcp", fmt.Sprintf(":%s", port))
			if err != nil {
				logger.Error("Failed to start callback server", "port", port, "error", err)
				continue
			}

			srv := &http.Server{
				Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
					logger.Debug("Received browser callback",
						"port", port,
						"method", r.Method,
						"url", r.URL.String(),
						"remoteAddr", r.RemoteAddr)

					// Send a simple response
					w.Header().Set("Content-Type", "text/plain")
					w.WriteHeader(http.StatusOK)
					fmt.Fprintf(w, "Callback received successfully\n")
					fmt.Fprintf(w, "You can close this window and return to your terminal.\n")
				}),
			}

			servers = append(servers, srv)
			serverReady.Add(1)

			go func(srv *http.Server, listener net.Listener) {
				defer serverReady.Done()
				logger.Debug("Callback server listening", "addr", listener.Addr().String())
				if err := srv.Serve(listener); err != http.ErrServerClosed {
					logger.Error("Callback server error", "error", err)
				}
			}(srv, listener)
		}

		// Wait a moment for servers to start
		go func() {
			serverReady.Wait()
			time.Sleep(100 * time.Millisecond)
		}()
	}

	// Attempt to open the URL in the default browser
	if err := openBrowser(url); err != nil {
		logger.Error("Failed to open browser", "error", err, "url", url)
		fmt.Fprintf(os.Stderr, "\nCould not open browser automatically.\n")
		fmt.Fprintf(os.Stderr, "Please open this URL manually:\n%s\n\n", url)
	} else {
		logger.Debug("Browser opened successfully", "url", url)
		fmt.Fprintf(os.Stderr, "\nOpened browser to: %s\n", url)
		if len(ports) > 0 {
			fmt.Fprintf(os.Stderr, "Waiting for browser callback on ports: %s\n", strings.Join(ports, ", "))
		}
	}

	// If we started servers, keep them running for a while
	if len(servers) > 0 {
		// Wait for a reasonable time for the browser callback
		time.Sleep(30 * time.Second)

		// Shutdown all servers
		for _, srv := range servers {
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			srv.Shutdown(ctx)
			cancel()
		}
		logger.Debug("Callback servers shut down")
	}
}

// openBrowser opens the URL in the default browser
func openBrowser(url string) error {
	var cmd *exec.Cmd

	switch os := getOS(); os {
	case "darwin":
		cmd = exec.Command("open", url)
	case "linux":
		// Try xdg-open first, fall back to other options
		if isCommandAvailable("xdg-open") {
			cmd = exec.Command("xdg-open", url)
		} else if isCommandAvailable("gnome-open") {
			cmd = exec.Command("gnome-open", url)
		} else if isCommandAvailable("kde-open") {
			cmd = exec.Command("kde-open", url)
		} else {
			return fmt.Errorf("no suitable browser opener found")
		}
	case "windows":
		cmd = exec.Command("cmd", "/c", "start", url)
	default:
		return fmt.Errorf("unsupported platform: %s", os)
	}

	return cmd.Start()
}

// getOS returns the operating system
func getOS() string {
	// Check for WSL
	if _, err := os.Stat("/proc/sys/fs/binfmt_misc/WSLInterop"); err == nil {
		return "wsl"
	}
	return runtime.GOOS
}

// isCommandAvailable checks if a command is available in PATH
func isCommandAvailable(name string) bool {
	_, err := exec.LookPath(name)
	return err == nil
}
