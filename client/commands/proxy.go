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
	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
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

// ProxyConfig holds configuration for proxy connections
type ProxyConfig struct {
	BaseURL string
	Token   string
	Logger  *slog.Logger
}

// StartProxyListener starts a proxy listener for a single port
// Returns a function to stop the proxy
func StartProxyListener(port int, config ProxyConfig) (func(), error) {
	// Start local listener
	listener, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", port))
	if err != nil {
		return nil, fmt.Errorf("failed to listen: %w", err)
	}

	logger := config.Logger
	if logger == nil {
		logger = slog.Default()
	}
	logger.Info("Listening on port", "port", port)

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
					debugLog("Failed to accept connection on port %d: %v", port, err)
					continue
				}

				// Handle connection in goroutine
				go HandleProxyConnection(localConn, port, config)
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
func HandleProxyConnection(localConn net.Conn, port int, config ProxyConfig) {
	defer localConn.Close()

	debugLog("Starting proxy connection for port %d to %s", port, config.BaseURL)

	// Parse base URL and convert to WebSocket URL
	parsedURL, err := url.Parse(config.BaseURL)
	if err != nil {
		debugLog("Failed to parse base URL: %v", err)
		return
	}

	// Build WebSocket URL for proxy endpoint
	wsScheme := "ws"
	if parsedURL.Scheme == "https" {
		wsScheme = "wss"
	}
	wsURL := fmt.Sprintf("%s://%s%s", wsScheme, parsedURL.Host, parsedURL.Path)

	debugLog("Connecting to WebSocket: %s", wsURL)

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
		debugLog("Failed to connect to WebSocket: %v", err)
		return
	}
	defer wsConn.Close()

	debugLog("WebSocket connected, sending initialization message")

	// Send initialization message with target host:port
	initMsg := ProxyInitMessage{
		Host: "localhost",
		Port: port,
	}
	initData, err := json.Marshal(initMsg)
	if err != nil {
		debugLog("Failed to marshal init message: %v", err)
		return
	}

	err = wsConn.WriteMessage(gorillaws.TextMessage, initData)
	if err != nil {
		debugLog("Failed to send init message: %v", err)
		return
	}

	debugLog("Initialization message sent, waiting for response")

	// Read response
	messageType, responseData, err := wsConn.ReadMessage()
	if err != nil {
		debugLog("Failed to read response: %v", err)
		return
	}

	if messageType != gorillaws.TextMessage {
		debugLog("Expected text response, got message type: %d", messageType)
		return
	}

	var response ProxyResponseMessage
	if err := json.Unmarshal(responseData, &response); err != nil {
		debugLog("Failed to parse response: %v", err)
		return
	}

	if response.Status != "connected" {
		debugLog("Proxy connection failed: %s", response.Status)
		return
	}

	debugLog("Proxy connection established for port %d to %s", port, response.Target)

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
					debugLog("Local read error: %v", err)
				}
				return
			}

			err = wsConn.WriteMessage(gorillaws.BinaryMessage, buffer[:n])
			if err != nil {
				debugLog("WebSocket write error: %v", err)
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
					debugLog("WebSocket read error: %v", err)
				}
				return
			}

			// Only forward binary messages as data
			if messageType == gorillaws.BinaryMessage {
				_, err := localConn.Write(data)
				if err != nil {
					debugLog("Local write error: %v", err)
					return
				}
			}
		}
	}()

	wg.Wait()
	debugLog("Proxy connection closed for port %d", port)
}

// ProxyCommand handles the proxy command
func ProxyCommand(cfg *config.Manager, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "proxy",
		Usage:       "proxy [options] <port1> [port2] [port3] ...",
		Description: "Forward local ports through the remote server proxy",
		FlagSet:     flag.NewFlagSet("proxy", flag.ContinueOnError),
		Examples: []string{
			"sprite proxy 8080",
			"sprite proxy 3000 8080",
			"sprite proxy -o myorg -s mysprite 8080",
		},
		Notes: []string{
			"Each port will be forwarded from localhost:<port> to the remote environment",
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

	// Parse and validate ports
	ports := make([]int, 0, len(remainingArgs))
	for _, arg := range remainingArgs {
		port, err := strconv.Atoi(arg)
		if err != nil || port < 1 || port > 65535 {
			fmt.Fprintf(os.Stderr, "Error: Invalid port number: %s\n", arg)
			os.Exit(1)
		}
		ports = append(ports, port)
	}

	// Ensure we have an org
	org, spriteName, isNewSprite, err := EnsureOrgAndSprite(cfg, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Handle sprite creation if needed
	if isNewSprite && spriteName != "" {
		fmt.Printf("Creating sprite %s...\n", format.Sprite(spriteName))
		if err := CreateSprite(cfg, org, spriteName); err != nil {
			fmt.Fprintf(os.Stderr, "Error creating sprite: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("%s Sprite %s created successfully!\n", format.Success("✓"), format.Sprite(spriteName))
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
	token, err := org.GetTokenWithKeyringDisabled(cfg.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}

	logger := slog.Default()
	logger.Info("Starting proxy for ports", "ports", ports)

	// Print connection info
	fmt.Println()
	if spriteName != "" && org.Name != "env" {
		fmt.Printf("Proxying through %s sprite %s...\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
			format.Sprite(spriteName))
	} else if org.Name == "env" {
		fmt.Println("Proxying through sprite environment...")
	} else {
		fmt.Printf("Proxying through %s...\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)))
	}

	for _, port := range ports {
		fmt.Printf("  Port %d: localhost:%d -> remote:%d\n", port, port, port)
	}
	fmt.Println()

	// Create proxy config
	proxyConfig := ProxyConfig{
		BaseURL: baseURL,
		Token:   token,
		Logger:  logger,
	}

	// Start listeners for each port using the new public functions
	var stopFuncs []func()
	var wg sync.WaitGroup

	for _, port := range ports {
		stopFunc, err := StartProxyListener(port, proxyConfig)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error starting proxy on port %d: %v\n", port, err)
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

	stopFunc, err := StartProxyListener(port, config)
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
	HandleProxyConnection(localConn, port, config)
}

// debugLog logs debug messages (helper function)
func debugLog(format string, args ...interface{}) {
	logger := slog.Default()
	if logger.Enabled(nil, slog.LevelDebug) {
		logger.Debug(fmt.Sprintf(format, args...))
	}
}
