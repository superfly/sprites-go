package commands

import (
	"crypto/tls"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/url"
	"os"
	"strconv"
	"strings"
	"sync"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/client/format"
)

// ProxyInitMessage represents the initial message sent to specify the target
type ProxyInitMessage struct {
	Host string `json:"host"`
	Port int    `json:"port"`
}

// ProxyResponseMessage represents the response from the server
type ProxyResponseMessage struct {
	Status string `json:"status"`
	Target string `json:"target"`
}

// PortMapping represents a mapping from local to remote port
type PortMapping struct {
	LocalPort  int
	RemotePort int
}

// ProxyConfig holds configuration for proxy connections
type ProxyConfig struct {
	BaseURL string
	Token   string
	Logger  *slog.Logger
}

// StartProxyListener starts a proxy listener for a single port mapping
// Returns a function to stop the proxy
func StartProxyListener(mapping PortMapping, config ProxyConfig) (func(), error) {
	// Start local listener
	listener, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", mapping.LocalPort))
	if err != nil {
		return nil, fmt.Errorf("failed to listen: %w", err)
	}

	logger := config.Logger
	if logger == nil {
		logger = slog.Default()
	}
	logger.Info("Listening on port", "local", mapping.LocalPort, "remote", mapping.RemotePort)

	// Channel to signal stop
	stopCh := make(chan struct{})
	stopped := make(chan struct{})

	go func() {
		defer close(stopped)
		defer listener.Close()

		for {
			select {
			case <-stopCh:
				return
			default:
				// Set a short deadline so we can check stopCh regularly
				// This is a simplified approach - production code might use context
				localConn, err := listener.Accept()
				if err != nil {
					if strings.Contains(err.Error(), "use of closed network connection") {
						return // Listener was closed
					}
					logger.Debug("Failed to accept connection on port", "port", mapping.LocalPort, "error", err)
					continue
				}

				// Handle connection in goroutine
				go HandleProxyConnection(localConn, mapping, config)
			}
		}
	}()

	// Return stop function
	return func() {
		close(stopCh)
		listener.Close()
		<-stopped // Wait for goroutine to finish
	}, nil
}

// HandleProxyConnection handles a single proxy connection
func HandleProxyConnection(localConn net.Conn, mapping PortMapping, config ProxyConfig) {
	defer localConn.Close()

	logger := config.Logger
	if logger == nil {
		logger = slog.Default()
	}
	logger.Debug("Starting proxy connection", "local", mapping.LocalPort, "remote", mapping.RemotePort, "baseURL", config.BaseURL)

	// Parse base URL and convert to WebSocket URL
	parsedURL, err := url.Parse(config.BaseURL)
	if err != nil {
		logger.Debug("Failed to parse base URL", "error", err)
		return
	}

	// Build WebSocket URL for proxy endpoint
	wsScheme := "ws"
	if parsedURL.Scheme == "https" {
		wsScheme = "wss"
	}
	wsURL := fmt.Sprintf("%s://%s%s", wsScheme, parsedURL.Host, parsedURL.Path)

	logger.Debug("Connecting to WebSocket", "url", wsURL)

	// Set up WebSocket dialer
	dialer := &gorillaws.Dialer{
		ReadBufferSize:  1024 * 1024, // 1MB buffer
		WriteBufferSize: 1024 * 1024, // 1MB buffer
	}

	// Add TLS config if needed
	if wsScheme == "wss" {
		dialer.TLSClientConfig = &tls.Config{
			InsecureSkipVerify: false, // Set to true if using self-signed certs
		}
	}

	// Set headers including auth
	headers := make(map[string][]string)
	headers["Authorization"] = []string{"Bearer " + config.Token}
	headers["User-Agent"] = []string{"sprite-client/1.0"}

	// Connect to WebSocket
	wsConn, _, err := dialer.Dial(wsURL, headers)
	if err != nil {
		logger.Debug("Failed to connect to WebSocket", "error", err)
		return
	}
	defer wsConn.Close()

	logger.Debug("WebSocket connected, sending initialization message")

	// Send initialization message with target host:port
	initMsg := ProxyInitMessage{
		Host: "localhost",
		Port: mapping.RemotePort,
	}
	initData, err := json.Marshal(initMsg)
	if err != nil {
		logger.Debug("Failed to marshal init message", "error", err)
		return
	}

	err = wsConn.WriteMessage(gorillaws.TextMessage, initData)
	if err != nil {
		logger.Debug("Failed to send init message", "error", err)
		return
	}

	logger.Debug("Initialization message sent, waiting for response")

	// Read response
	messageType, responseData, err := wsConn.ReadMessage()
	if err != nil {
		logger.Debug("Failed to read response", "error", err)
		return
	}

	if messageType != gorillaws.TextMessage {
		logger.Debug("Expected text response", "messageType", messageType)
		return
	}

	var response ProxyResponseMessage
	if err := json.Unmarshal(responseData, &response); err != nil {
		logger.Debug("Failed to parse response", "error", err)
		return
	}

	if response.Status != "connected" {
		logger.Debug("Proxy connection failed", "status", response.Status)
		return
	}

	logger.Debug("Proxy connection established", "local", mapping.LocalPort, "remote", mapping.RemotePort, "target", response.Target)

	// Start bidirectional data forwarding
	var wg sync.WaitGroup
	wg.Add(2)

	// Copy from local TCP to WebSocket
	go func() {
		defer wg.Done()
		defer wsConn.Close()

		buffer := make([]byte, 32*1024) // 32KB buffer
		for {
			n, err := localConn.Read(buffer)
			if err != nil {
				if err != io.EOF {
					logger.Debug("Local read error", "error", err)
				}
				return
			}

			err = wsConn.WriteMessage(gorillaws.BinaryMessage, buffer[:n])
			if err != nil {
				logger.Debug("WebSocket write error", "error", err)
				return
			}
		}
	}()

	// Copy from WebSocket to local TCP
	go func() {
		defer wg.Done()
		defer localConn.Close()

		for {
			messageType, data, err := wsConn.ReadMessage()
			if err != nil {
				if !gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
					logger.Debug("WebSocket read error", "error", err)
				}
				return
			}

			// Only forward binary messages as data
			if messageType == gorillaws.BinaryMessage {
				_, err := localConn.Write(data)
				if err != nil {
					logger.Debug("Local write error", "error", err)
					return
				}
			}
		}
	}()

	wg.Wait()
	logger.Debug("Proxy connection closed", "local", mapping.LocalPort, "remote", mapping.RemotePort)
}

// ProxyCommand handles the proxy command
func ProxyCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "proxy",
		Usage:       "proxy [options] <port1> [port2] ... or <local1:remote1> [local2:remote2] ...",
		Description: "Forward local ports through the remote server proxy",
		FlagSet:     flag.NewFlagSet("proxy", flag.ContinueOnError),
		Examples: []string{
			"sprite proxy 8080",
			"sprite proxy 3000 8080",
			"sprite proxy 4005:4000",
			"sprite proxy 3001:3000 8081:8080",
			"sprite proxy -o myorg -s mysprite 8080",
		},
		Notes: []string{
			"Each port will be forwarded from localhost to the remote environment",
			"Use LOCAL:REMOTE syntax to map different local and remote ports",
			"Multiple ports can be specified to forward multiple services simultaneously",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Check for port arguments after flag parsing
	if len(remainingArgs) == 0 {
		fmt.Fprintf(os.Stderr, "Error: proxy requires at least one port number\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Parse and validate port mappings
	mappings := make([]PortMapping, 0, len(remainingArgs))
	for _, arg := range remainingArgs {
		var mapping PortMapping

		// Check if it's a LOCAL:REMOTE format
		if strings.Contains(arg, ":") {
			parts := strings.Split(arg, ":")
			if len(parts) != 2 {
				fmt.Fprintf(os.Stderr, "Error: Invalid port mapping format: %s (expected LOCAL:REMOTE)\n", arg)
				os.Exit(1)
			}

			localPort, err := strconv.Atoi(parts[0])
			if err != nil || localPort < 1 || localPort > 65535 {
				fmt.Fprintf(os.Stderr, "Error: Invalid local port number: %s\n", parts[0])
				os.Exit(1)
			}

			remotePort, err := strconv.Atoi(parts[1])
			if err != nil || remotePort < 1 || remotePort > 65535 {
				fmt.Fprintf(os.Stderr, "Error: Invalid remote port number: %s\n", parts[1])
				os.Exit(1)
			}

			mapping.LocalPort = localPort
			mapping.RemotePort = remotePort
		} else {
			// Simple port format - use same port for local and remote
			port, err := strconv.Atoi(arg)
			if err != nil || port < 1 || port > 65535 {
				fmt.Fprintf(os.Stderr, "Error: Invalid port number: %s\n", arg)
				os.Exit(1)
			}
			mapping.LocalPort = port
			mapping.RemotePort = port
		}

		mappings = append(mappings, mapping)
	}

	// Ensure we have an org
	org, spriteName, err := EnsureOrgAndSpriteWithContext(ctx, flags.Org, flags.Sprite)
	if err != nil {
		// Check if it's a cancellation error
		if strings.Contains(err.Error(), "cancelled") {
			handlePromptError(err)
		} else {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
		os.Exit(1)
	}

	// Get the base URL for the proxy
	var baseURL string
	if spriteName != "" && org.Name != "env" {
		// Use sprite proxy endpoint
		baseURL = buildSpriteProxyURL(org, spriteName, "/proxy")
	} else {
		// Use direct endpoint for backward compatibility
		baseURL = strings.TrimRight(org.URL, "/") + "/proxy"
	}

	// Get auth token
	token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}

	logger := ctx.Logger
	logger.Info("Starting proxy for port mappings", "mappings", mappings)

	// Print connection info
	fmt.Println()
	if spriteName != "" {
		fmt.Printf("Proxying through %s sprite %s...\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
			format.Sprite(spriteName))
	} else {
		fmt.Printf("Proxying through %s...\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)))
	}

	for _, mapping := range mappings {
		if mapping.LocalPort == mapping.RemotePort {
			fmt.Printf("  Port %d: localhost:%d -> remote:%d\n", mapping.LocalPort, mapping.LocalPort, mapping.RemotePort)
		} else {
			fmt.Printf("  Port mapping: localhost:%d -> remote:%d\n", mapping.LocalPort, mapping.RemotePort)
		}
	}
	fmt.Println()

	// Create proxy config
	proxyConfig := ProxyConfig{
		BaseURL: baseURL,
		Token:   token,
		Logger:  logger,
	}

	// Start listeners for each port mapping using the new public functions
	var stopFuncs []func()
	var wg sync.WaitGroup

	for _, mapping := range mappings {
		stopFunc, err := StartProxyListener(mapping, proxyConfig)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error starting proxy on port %d: %v\n", mapping.LocalPort, err)
			// Stop any previously started proxies
			for _, sf := range stopFuncs {
				sf()
			}
			os.Exit(1)
		}
		stopFuncs = append(stopFuncs, stopFunc)
	}

	// Wait indefinitely (until interrupted)
	wg.Add(1)
	wg.Wait()
}

func proxyPort(port int, baseURL, token string) error {
	config := ProxyConfig{
		BaseURL: baseURL,
		Token:   token,
		Logger:  slog.Default(),
	}

	mapping := PortMapping{
		LocalPort:  port,
		RemotePort: port,
	}

	stopFunc, err := StartProxyListener(mapping, config)
	if err != nil {
		return err
	}
	defer stopFunc()

	// This will run forever until the process is killed
	select {}
}

func handleProxyConnection(localConn net.Conn, port int, baseURL, token string) {
	config := ProxyConfig{
		BaseURL: baseURL,
		Token:   token,
		Logger:  slog.Default(),
	}
	mapping := PortMapping{
		LocalPort:  port,
		RemotePort: port,
	}
	HandleProxyConnection(localConn, mapping, config)
}
