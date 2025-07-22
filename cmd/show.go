package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"os/exec"
	"strings"

	"github.com/superfly/fly-go/flaps"
	"github.com/superfly/fly-go/tokens"
)

func main() {
	var appName string
	var machineID string
	flag.StringVar(&appName, "a", "", "Fly app name")
	flag.StringVar(&machineID, "m", "", "Machine ID (optional, will look for sprite_compute if not specified)")
	flag.Parse()

	log.Printf("App name from flag: %s", appName)

	// Check for app name from flag or env var
	if appName == "" {
		appName = os.Getenv("FLY_APP_NAME")
		log.Printf("App name from env: %s", appName)
	}
	if appName == "" {
		log.Fatal("App name required: use -a flag or set FLY_APP_NAME env var")
	}

	// Get Fly API token
	token := os.Getenv("FLY_API_TOKEN")
	if token == "" {
		// Try to get token from flyctl
		cmd := exec.Command("flyctl", "auth", "token")
		output, err := cmd.Output()
		if err != nil {
			log.Fatal("FLY_API_TOKEN not set and couldn't get from flyctl: ", err)
		}
		token = strings.TrimSpace(string(output))
	}

	ctx := context.Background()

	// Create flaps client for machine management
	flapsClient, err := flaps.NewWithOptions(ctx, flaps.NewClientOpts{
		AppName: appName,
		Tokens:  tokens.Parse(token),
	})
	if err != nil {
		log.Fatal("Failed to create flaps client: ", err)
	}

	// If no machine ID specified, look for sprite_compute
	if machineID == "" {
		machines, err := flapsClient.List(ctx, "")
		if err != nil {
			log.Fatal("Failed to list machines: ", err)
		}

		// Look for sprite_compute machine
		for _, m := range machines {
			log.Printf("Machine: %s\n", m.Name)
			if m.Name == "sprite_compute" {
				machineID = m.ID
				log.Printf("Found sprite_compute machine: %s\n", machineID)
				break
			}
		}

		if machineID == "" {
			log.Fatal("No sprite_compute machine found and no machine ID specified")
		}
	}

	// Get the machine details
	machine, err := flapsClient.Get(ctx, machineID)
	if err != nil {
		log.Fatalf("Failed to get machine %s: %v", machineID, err)
	}

	// Pretty print the machine info
	fmt.Printf("\n=== Machine Information ===\n")
	fmt.Printf("ID: %s\n", machine.ID)
	fmt.Printf("Name: %s\n", machine.Name)
	fmt.Printf("State: %s\n", machine.State)
	fmt.Printf("Region: %s\n", machine.Region)
	fmt.Printf("Instance ID: %s\n", machine.InstanceID)
	fmt.Printf("Private IP: %s\n", machine.PrivateIP)
	fmt.Printf("Created: %s\n", machine.CreatedAt)
	fmt.Printf("Updated: %s\n", machine.UpdatedAt)

	// Pretty print the machine configuration
	fmt.Printf("\n=== Machine Configuration ===\n")
	configJSON, err := json.MarshalIndent(machine.Config, "", "  ")
	if err != nil {
		log.Fatal("Failed to marshal config: ", err)
	}
	fmt.Println(string(configJSON))

	// Show events if any
	if len(machine.Events) > 0 {
		fmt.Printf("\n=== Recent Events ===\n")
		for _, event := range machine.Events {
			fmt.Printf("%s: %s - %s\n", event.Timestamp, event.Type, event.Status)
			if event.Request != nil {
				fmt.Printf("  Request: %v\n", event.Request)
			}
		}
	}

	// Show checks if any
	if machine.Checks != nil && len(machine.Checks) > 0 {
		fmt.Printf("\n=== Health Checks ===\n")
		for name, check := range machine.Checks {
			fmt.Printf("%s: Status=%s Updated=%s\n", name, check.Status, check.UpdatedAt)
			if check.Output != "" {
				fmt.Printf("  Output: %s\n", check.Output)
			}
		}
	}
}
