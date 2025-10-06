package commands

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"os"
	osexec "os/exec"
	"os/signal"
	"runtime"
	"strings"
	"sync"
	"syscall"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/pkg/terminal"
	sprites "github.com/superfly/sprites-go"
	"golang.org/x/term"
)

// ExecCommand handles the exec command - executes a command in the sprite environment
func ExecCommand(ctx *GlobalContext, args []string) int {
	// Create command structure
	cmd := &Command{
		Name:        "exec",
		Usage:       "exec [options] [command] [args...]",
		Description: "Execute a command in the sprite environment or list running sessions",
		FlagSet:     flag.NewFlagSet("exec", flag.ContinueOnError),
		Examples: []string{
			"sprite exec                  # List running sessions",
			"sprite exec ls -la",
			"sprite exec -dir /app echo hello world",
			"sprite exec -env KEY=value,FOO=bar env",
			"sprite exec -tty /bin/bash",
			"sprite exec -detachable /bin/bash --login",
			"sprite exec -o myorg -s mysprite npm start",
		},
		Notes: []string{
			"When no command is specified, lists all running sessions in the sprite.",
			"When using -tty, terminal environment variables (TERM, COLORTERM, LANG, LC_ALL)",
			"are automatically passed through from your local environment.",
			"When using -detachable, creates a tmux session that can be detached and reattached.",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)
	workingDir := cmd.FlagSet.String("dir", "", "Working directory for the command")
	tty := cmd.FlagSet.Bool("tty", false, "Allocate a pseudo-TTY")
	detachable := cmd.FlagSet.Bool("detachable", false, "Create a detachable tmux session")
	envVars := cmd.FlagSet.String("env", "", "Environment variables (KEY=value,KEY2=value2)")
	sessionID := cmd.FlagSet.String("id", "", "Attach to existing session by ID")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		return 1
	}

	// Get organization, client, and sprite using unified function
	org, _, sprite, err := GetOrgClientAndSprite(ctx, flags.Org, flags.Sprite)
	if err != nil {
		// Check if it's a cancellation error
		if strings.Contains(err.Error(), "cancelled") {
			handlePromptError(err)
		} else {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
		return 1
	}

	// Check if we're attaching to an existing session
	if *sessionID != "" {
		return attachToSession(ctx, sprite, *sessionID)
	}

	// Check for command to execute
	if len(remainingArgs) == 0 {
		// No command specified - list running sessions
		return listExecSessions(ctx, org, sprite)
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

	// Build command string for display and title
	fullCmdStr := strings.Join(remainingArgs, " ")
	cmdStr := fullCmdStr
	if len(cmdStr) > 50 {
		cmdStr = cmdStr[:47] + "..."
	}

	// Print connection info if not in TTY mode (in TTY mode, output should be clean)
	if !*tty {
		fmt.Println()
		if sprite.Name() != "" {
			fmt.Printf("Connecting to %s sprite %s...\n",
				format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
				format.Sprite(sprite.Name()))
		}
		fmt.Printf("Running: %s\n", format.Command(cmdStr))
	}

	// Create the command using sprite instance
	execCtx := context.Background()
	spriteCmd := sprite.CommandContext(execCtx, remainingArgs[0], remainingArgs[1:]...)

	// Set working directory if specified
	if *workingDir != "" {
		spriteCmd.Dir = *workingDir
	}

	// Set environment variables
	if len(envList) > 0 {
		spriteCmd.Env = envList
	}

	// Configure detachable mode
	if *detachable {
		spriteCmd.SetDetachable(true)
	}

	// Configure TTY mode
	if *tty {
		spriteCmd.SetTTY(true)

		// Get terminal size if available
		if term.IsTerminal(int(os.Stdin.Fd())) {
			width, height, err := term.GetSize(int(os.Stdin.Fd()))
			if err == nil {
				spriteCmd.SetTTYSize(uint16(height), uint16(width))
			}
		}

		// Set up stdin/stdout/stderr for TTY mode
		spriteCmd.Stdin = os.Stdin
		browserHandler := makeBrowserOSCHandler()
		oscMonitor := terminal.NewOSCMonitor(browserHandler)
		// Filter remote OSC title updates so our local title stays consistent
		titleWriter := newOSCTitleFilterWriter(os.Stdout, buildTitle(sprite.Name(), "", ""), ctx.Logger)
		spriteCmd.Stdout = io.MultiWriter(titleWriter, oscMonitor)
		spriteCmd.Stderr = os.Stderr

		// Set terminal/tab title for TTY sessions
		// No session ID yet; if detachable, the server will create one and attach path will set it
		setTerminalTitle(buildTitle(sprite.Name(), "", fullCmdStr), ctx.Logger)

		// Handle terminal resize events
		go handleSpriteTerminalResize(spriteCmd)
	} else {
		// Non-TTY mode - standard I/O
		spriteCmd.Stdin = os.Stdin
		spriteCmd.Stdout = os.Stdout
		spriteCmd.Stderr = os.Stderr
	}

	// Handle port notifications and auto-proxy. Ensure cleanup on exit.
	cleanupProxies := setPortNotificationHandler(spriteCmd, sprite)
	defer cleanupProxies()

	// Prepare terminal for raw mode if using TTY
	var oldState *term.State
	if *tty && term.IsTerminal(int(os.Stdin.Fd())) {
		oldState, err = term.MakeRaw(int(os.Stdin.Fd()))
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to set terminal to raw mode: %v\n", err)
			return 1
		}
		// Ensure terminal is restored on exit
		defer func() {
			if oldState != nil {
				term.Restore(int(os.Stdin.Fd()), oldState)
			}
		}()
	}

	// Set up signal handling for graceful shutdown
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)
	defer signal.Stop(sigCh)

	// Run the command with signal handling
	cmdDone := make(chan error, 1)
	go func() {
		cmdDone <- spriteCmd.Run()
	}()

	// Wait for command completion or signal
	select {
	case err := <-cmdDone:
		if err != nil {
			// Extract exit code if available
			if exitErr, ok := err.(*sprites.ExitError); ok {
				return exitErr.ExitCode()
			}
			// For other errors, print and return 1
			if !*tty {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			}
			return 1
		}
		// Command succeeded
		return 0

	case <-sigCh:
		// Handle interrupt signal
		// The SDK should handle killing the remote process
		// Return standard interrupt exit code
		return 130
	}
}

// handleSpriteTerminalResize monitors for terminal resize events and updates the remote TTY size
func handleSpriteTerminalResize(cmd *sprites.Cmd) {
	// This is a simplified version - in production you'd want to use
	// syscall.SIGWINCH on Unix systems to detect resize events
	// For now, this is a placeholder
}

// setPortNotificationHandler sets a TextMessageHandler to decode port notifications,
// automatically start/stop local proxies via the SDK, and returns a cleanup function.
func setPortNotificationHandler(cmd *sprites.Cmd, sprite *sprites.Sprite) func() {
	var mu sync.Mutex
	// Track by remote host + port (e.g., "127.0.0.1:3000")
	active := make(map[string]*sprites.ProxySession)

	startProxy := func(remoteHost string, remotePort int) {
		key := fmt.Sprintf("%s:%d", remoteHost, remotePort)
		mu.Lock()
		if _, exists := active[key]; exists {
			mu.Unlock()
			return
		}
		mu.Unlock()

		// Use same local and remote port by default; include RemoteHost
		ctx := context.Background()
		mappings := []sprites.PortMapping{{
			LocalPort:  remotePort,
			RemotePort: remotePort,
			RemoteHost: remoteHost,
		}}
		sessions, err := sprite.ProxyPorts(ctx, mappings)
		if err != nil || len(sessions) == 0 {
			slog.Default().Debug("Failed to start proxy",
				"remote_host", remoteHost,
				"remote_port", remotePort,
				"error", err,
			)
			return
		}
		session := sessions[0]
		mu.Lock()
		active[key] = session
		mu.Unlock()
		slog.Default().Debug("Started proxy",
			"local", session.LocalAddr().String(),
			"remote_host", remoteHost,
			"remote_port", remotePort,
		)
	}

	stopProxy := func(remoteHost string, remotePort int) {
		key := fmt.Sprintf("%s:%d", remoteHost, remotePort)
		mu.Lock()
		if sess, exists := active[key]; exists {
			sess.Close()
			delete(active, key)
			mu.Unlock()
			slog.Default().Debug("Stopped proxy", "remote_host", remoteHost, "remote_port", remotePort)
			return
		}
		mu.Unlock()
	}

	cmd.TextMessageHandler = func(data []byte) {
		var msg map[string]interface{}
		if err := json.Unmarshal(data, &msg); err != nil {
			// Not JSON control message
			return
		}
		typeVal, _ := msg["type"].(string)
		switch typeVal {
		case "port_opened":
			if p, ok := msg["port"].(float64); ok {
				remotePort := int(p)
				remoteHost, _ := msg["address"].(string)
				if remoteHost == "" {
					remoteHost = "localhost"
				}
				startProxy(remoteHost, remotePort)
			}
		case "port_closed":
			if p, ok := msg["port"].(float64); ok {
				remotePort := int(p)
				remoteHost, _ := msg["address"].(string)
				if remoteHost == "" {
					remoteHost = "localhost"
				}
				stopProxy(remoteHost, remotePort)
			}
		}
	}

	// Cleanup function to close any active proxies
	return func() {
		mu.Lock()
		defer mu.Unlock()
		for key, sess := range active {
			_ = sess.Close()
			delete(active, key)
		}
	}
}

// makeBrowserOSCHandler returns a handler that parses our OSC browser-open sequence
// and opens the provided URL in the user's default browser.
func makeBrowserOSCHandler() func(string) {
	return func(sequence string) {
		// Expected format: "9999;browser-open;{url};{port1,port2,...}"
		slog.Default().Debug("Received OSC sequence", "sequence", sequence)
		parts := strings.Split(sequence, ";")
		if len(parts) < 3 {
			slog.Default().Debug("OSC sequence too short", "parts_len", len(parts))
			return
		}
		if parts[0] != "9999" || parts[1] != "browser-open" {
			slog.Default().Debug("OSC not browser-open", "code", parts[0], "action", parts[1])
			return
		}
		url := parts[2]
		var ports []string
		if len(parts) >= 4 && parts[3] != "" {
			for _, port := range strings.Split(parts[3], ",") {
				if trimmed := strings.TrimSpace(port); trimmed != "" {
					ports = append(ports, trimmed)
				}
			}
		}
		slog.Default().Debug("Opening browser from OSC", "url", url, "ports", ports)
		if url == "" {
			return
		}
		if err := openBrowser(url); err != nil {
			fmt.Fprintf(os.Stderr, "Failed to open browser: %v\n", err)
		}
	}
}

// openBrowser opens the specified URL in the default system browser.
func openBrowser(url string) error {
	switch runtime.GOOS {
	case "darwin":
		return osexec.Command("open", url).Start()
	case "windows":
		return osexec.Command("rundll32", "url.dll,FileProtocolHandler", url).Start()
	default:
		return osexec.Command("xdg-open", url).Start()
	}
}

// listExecSessions lists running execution sessions in the sprite and allows interactive selection
func listExecSessions(ctx *GlobalContext, org *config.Organization, sprite *sprites.Sprite) int {
	// Get sessions list
	sessionsCtx := context.Background()
	sessions, err := sprite.Client().ListSessions(sessionsCtx, sprite.Name())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to list sessions: %v\n", err)
		return 1
	}

	// Convert to SessionItem structs
	sessionItems := make([]SessionItem, 0, len(sessions))
	for _, session := range sessions {
		item := SessionItem{
			ID:             session.ID,
			Command:        session.Command,
			Created:        session.Created,
			BytesPerSecond: session.BytesPerSecond,
			IsActive:       session.IsActive,
			LastActivity:   session.LastActivity,
		}
		sessionItems = append(sessionItems, item)
	}

	// Check if we're in an interactive terminal
	isInteractive := term.IsTerminal(int(os.Stdout.Fd()))

	if isInteractive {
		// Run the interactive session selector
		selectedID, err := runSessionSelector(sessionItems, org, sprite)
		if err != nil {
			// User cancelled or no sessions
			return 0
		}

		// Attach to the selected session
		return attachToSession(ctx, sprite, selectedID)
	} else {
		// Non-interactive mode - just list the sessions
		return listSessionsNonInteractive(sessionItems, org, sprite)
	}
}

// attachToSession attaches to an existing execution session
func attachToSession(ctx *GlobalContext, sprite *sprites.Sprite, sessionID string) int {

	// Print connection info
	fmt.Printf("Attaching to session %s in sprite %s...\n",
		format.Command(sessionID),
		format.Sprite(sprite.Name()))

	// Best-effort: lookup command for this session for the tab title
	var cmdForTitle string
	{
		sessionsCtx := context.Background()
		if sessions, err := sprite.Client().ListSessions(sessionsCtx, sprite.Name()); err == nil {
			for _, s := range sessions {
				if s.ID == sessionID {
					cmdForTitle = s.Command
					break
				}
			}
		}
	}

	// Create attach command using sprite instance
	execCtx := context.Background()
	attachCmd := sprite.AttachSessionContext(execCtx, sessionID)

	// Attach always uses TTY - set up terminal environment variables
	var envList []string
	terminalEnvVars := []string{"TERM", "COLORTERM", "LANG", "LC_ALL"}
	for _, envVar := range terminalEnvVars {
		if value := os.Getenv(envVar); value != "" {
			envList = append(envList, envVar+"="+value)
		}
	}
	if len(envList) > 0 {
		attachCmd.Env = envList
	}

	attachCmd.Stdin = os.Stdin
	browserHandler := makeBrowserOSCHandler()
	oscMonitor := terminal.NewOSCMonitor(browserHandler)
	// Filter remote OSC title updates so our local title stays consistent
	titleWriter := newOSCTitleFilterWriter(os.Stdout, buildTitle(sprite.Name(), sessionID, cmdForTitle), ctx.Logger)
	attachCmd.Stdout = io.MultiWriter(titleWriter, oscMonitor)
	attachCmd.Stderr = os.Stderr
	// Update terminal/tab title with sprite name, session id, and command (if known)
	setTerminalTitle(buildTitle(sprite.Name(), sessionID, cmdForTitle), ctx.Logger)

	// Handle port notifications and auto-proxy. Ensure cleanup on exit.
	cleanupProxies := setPortNotificationHandler(attachCmd, sprite)
	defer cleanupProxies()

	// Get terminal size if available
	if term.IsTerminal(int(os.Stdin.Fd())) {
		width, height, err := term.GetSize(int(os.Stdin.Fd()))
		if err == nil {
			attachCmd.SetTTYSize(uint16(height), uint16(width))
		}
	}

	// Handle terminal resize events
	go handleSpriteTerminalResize(attachCmd)

	// Prepare terminal for raw mode
	var oldState *term.State
	if term.IsTerminal(int(os.Stdin.Fd())) {
		var err error
		oldState, err = term.MakeRaw(int(os.Stdin.Fd()))
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to set terminal to raw mode: %v\n", err)
			return 1
		}
		// Ensure terminal is restored on exit
		defer func() {
			if oldState != nil {
				term.Restore(int(os.Stdin.Fd()), oldState)
			}
		}()
	}

	// Set up signal handling for graceful shutdown
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)
	defer signal.Stop(sigCh)

	// Run the attach command
	cmdDone := make(chan error, 1)
	go func() {
		cmdDone <- attachCmd.Run()
	}()

	// Wait for command completion or signal
	select {
	case err := <-cmdDone:
		if err != nil {
			// Extract exit code if available
			if exitErr, ok := err.(*sprites.ExitError); ok {
				return exitErr.ExitCode()
			}
			// For other errors, return 1
			return 1
		}
		// Command succeeded
		return 0

	case <-sigCh:
		// Handle interrupt signal
		// Return standard interrupt exit code
		return 130
	}
}
