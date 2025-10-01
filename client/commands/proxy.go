package commands

import (
	"context"
	"flag"
	"fmt"
	"os"
	"os/signal"
	"strconv"
	"strings"
	"syscall"

	"github.com/superfly/sprite-env/client/format"
	sprites "github.com/superfly/sprites-go"
)

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
	mappings := make([]sprites.PortMapping, 0, len(remainingArgs))
	for _, arg := range remainingArgs {
		var mapping sprites.PortMapping

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

	// Client is already created by GetOrgAndClient

	// Print connection info
	fmt.Println()
	if sprite.Name() != "" {
		fmt.Printf("Proxying through %s sprite %s...\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
			format.Sprite(sprite.Name()))
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

	// Create proxy sessions using SDK
	ctxProxy := context.Background()
	sessions, err := sprite.Client().ProxyPorts(ctxProxy, sprite.Name(), mappings)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create proxy sessions: %v\n", err)
		os.Exit(1)
	}

	// Set up signal handling for graceful shutdown
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)

	// Wait for interrupt signal
	<-sigChan
	fmt.Println("\nShutting down proxy...")

	// Clean up sessions
	for _, session := range sessions {
		session.Close()
	}

	fmt.Println("Proxy stopped.")
}
