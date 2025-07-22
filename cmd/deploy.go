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
	"time"

	"github.com/superfly/fly-go"
	"github.com/superfly/fly-go/flaps"
	"github.com/superfly/fly-go/tokens"
)

// waitForMachineStarted waits for a machine to reach "started" state
// Returns an error if the machine is in "creating" or "updating" state
func waitForMachineStarted(ctx context.Context, client *flaps.Client, machineID string, timeout time.Duration) error {
	start := time.Now()
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-ticker.C:
			machine, err := client.Get(ctx, machineID)
			if err != nil {
				return fmt.Errorf("failed to get machine status: %w", err)
			}

			log.Printf("Machine %s is in state: %s", machineID, machine.State)

			// Check for bad states
			if machine.State == "creating" || machine.State == "updating" {
				return fmt.Errorf("machine is stuck in %s state", machine.State)
			}

			// Check for success
			if machine.State == "started" {
				log.Printf("Machine %s successfully started", machineID)
				return nil
			}

			// Check for other terminal states
			if machine.State == "destroyed" {
				return fmt.Errorf("machine entered unexpected state: %s", machine.State)
			}

			// Check timeout
			if time.Since(start) > timeout {
				return fmt.Errorf("timeout waiting for machine to start (current state: %s)", machine.State)
			}
		}
	}
}

func main() {
	var appName string
	var skipBuild bool
	flag.StringVar(&appName, "a", "", "Fly app name")
	flag.BoolVar(&skipBuild, "skip-build", false, "Skip docker build step and just push the image")
	flag.Parse()

	// Check for app name from flag or env var
	if appName == "" {
		appName = os.Getenv("FLY_APP_NAME")
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

	// Build and push Docker image
	label := fmt.Sprintf("%d", time.Now().Unix())
	imageRef := fmt.Sprintf("registry.fly.io/%s:%s", appName, label)

	if !skipBuild {
		log.Println("Building Docker image...")
		// Use buildx for better cross-platform support
		buildCmd := exec.Command("fly", "deploy", "-a", appName, "--build-only", "--push", "--image-label", label)
		buildCmd.Dir = "../"
		buildCmd.Stdout = os.Stdout
		buildCmd.Stderr = os.Stderr
		if err := buildCmd.Run(); err != nil {
			log.Fatal("Failed to build Docker image: ", err)
		}
	} else {
		log.Println("Skipping docker image build.")
	}

	// Create flaps client for machine management
	flapsClient, err := flaps.NewWithOptions(ctx, flaps.NewClientOpts{
		AppName: appName,
		Tokens:  tokens.Parse(token),
	})
	if err != nil {
		log.Fatal("Failed to create flaps client: ", err)
	}

	// First, find existing machine
	var machineID string
	var existingMachine *fly.Machine
	machines, err := flapsClient.List(ctx, "")
	if err != nil {
		log.Fatal("Failed to list machines: ", err)
	}

	// Look for existing sprite_compute machine
	for _, m := range machines {
		if m.Name == "sprite_compute" || strings.HasPrefix(m.Name, "sprites-") {
			machineID = m.ID
			existingMachine = m
			log.Printf("Found existing machine: %s (name: %s)\n", machineID, m.Name)
			break
		}
	}

	// Handle volume based on whether we found a machine
	var volumeID string
	var existingEnvVars map[string]string

	if existingMachine != nil {
		// Extract existing environment variables
		if existingMachine.Config.Env != nil {
			existingEnvVars = make(map[string]string)
			for k, v := range existingMachine.Config.Env {
				existingEnvVars[k] = v
				log.Printf("Found existing env var: %s\n", k)
			}
		}

		// Check if the existing machine has a volume attached
		for _, mount := range existingMachine.Config.Mounts {
			if mount.Volume != "" {
				volumeID = mount.Volume
				log.Printf("Machine has attached volume: %s (mounted at %s)\n", volumeID, mount.Path)
				break
			}
		}
	}

	// If no volume found (either no machine or machine has no volume), check all volumes
	if volumeID == "" {
		log.Println("No volume attached to machine, checking all volumes...")
		volumes, err := flapsClient.GetVolumes(ctx)
		if err != nil {
			log.Fatal("Failed to list volumes: ", err)
		}

		log.Printf("Found %d volumes total\n", len(volumes))
		// Look for existing sprite_data or data volume
		for _, v := range volumes {
			log.Printf("  - Volume: %s (name: %s, size: %dGB, state: %s)\n", v.ID, v.Name, v.SizeGb, v.State)
			if v.Name == "sprite_data" || v.Name == "data" {
				volumeID = v.ID
				log.Printf("Using unattached volume: %s (name: %s)\n", volumeID, v.Name)
				break
			}
		}
	}

	// Create volume if still not found
	if volumeID == "" {
		log.Println("Creating new sprite_data volume...")
		sizeGb := 10
		encrypted := true
		volInput := fly.CreateVolumeRequest{
			Name:      "sprite_data",
			Region:    "ord",
			SizeGb:    &sizeGb,
			Encrypted: &encrypted,
		}

		volume, err := flapsClient.CreateVolume(ctx, volInput)
		if err != nil {
			log.Fatal("Failed to create volume: ", err)
		}
		volumeID = volume.ID
		log.Printf("Created volume: %s\n", volumeID)

		// Wait a bit for volume to be ready
		time.Sleep(5 * time.Second)
	}

	// Read machine config
	configData, err := os.ReadFile("machine-config.json")
	if err != nil {
		log.Fatal("Failed to read machine-config.json: ", err)
	}

	// Replace placeholders in memory
	configStr := string(configData)
	configStr = strings.ReplaceAll(configStr, "<volume_id>", volumeID)
	configStr = strings.ReplaceAll(configStr, "<image_ref>", imageRef)

	// Parse the config into machine config
	var machineConfig fly.MachineConfig
	if err := json.Unmarshal([]byte(configStr), &machineConfig); err != nil {
		log.Fatal("Failed to parse machine config: ", err)
	}

	// Merge existing environment variables with new config
	if existingEnvVars != nil && len(existingEnvVars) > 0 {
		log.Printf("Merging %d existing environment variables into new config\n", len(existingEnvVars))

		// Initialize the env map if it doesn't exist
		if machineConfig.Env == nil {
			machineConfig.Env = make(map[string]string)
		}

		// Copy existing env vars that aren't already in the new config
		for k, v := range existingEnvVars {
			if _, exists := machineConfig.Env[k]; !exists {
				machineConfig.Env[k] = v
				log.Printf("  - Preserving env var: %s\n", k)
			} else {
				log.Printf("  - Keeping new value for env var: %s\n", k)
			}
		}
	}

	// Print the config that will be sent
	log.Printf("\n=== Machine Config to Deploy ===")
	configJSON, err := json.MarshalIndent(machineConfig, "", "  ")
	if err != nil {
		log.Fatal("Failed to marshal config for display: ", err)
	}
	log.Printf("%s\n", string(configJSON))

	if existingMachine != nil {
		// Update existing machine
		log.Printf("Updating machine %s...\n", machineID)

		// Update the machine
		updateInput := fly.LaunchMachineInput{
			ID:     machineID,
			Config: &machineConfig,
		}
		machine, err := flapsClient.Update(ctx, updateInput, "")
		if err != nil {
			log.Fatal("Failed to update machine: ", err)
		}

		log.Printf("Updated machine: %s\n", machine.ID)
	} else {
		// Create new machine
		log.Println("Creating new sprite_compute machine...")

		launchInput := fly.LaunchMachineInput{
			Name:   "sprite_compute",
			Region: "ord",
			Config: &machineConfig,
		}

		machine, err := flapsClient.Launch(ctx, launchInput)
		if err != nil {
			log.Fatal("Failed to create machine: ", err)
		}

		log.Printf("Created machine: %s\n", machine.ID)
		machineID = machine.ID
	}

	// Wait for machine to be started
	log.Printf("Waiting for machine to start...")
	if err := waitForMachineStarted(ctx, flapsClient, machineID, 60*time.Second); err != nil {
		// If machine is stuck in creating/updating, force delete it
		if strings.Contains(err.Error(), "stuck in") {
			log.Printf("Machine is stuck, attempting to force delete...")
			if delErr := flapsClient.Destroy(ctx, fly.RemoveMachineInput{
				ID: machineID,
			}, ""); delErr != nil {
				log.Printf("Failed to force delete machine: %v", delErr)
			}
		}
		log.Fatalf("Failed to wait for machine to start: %v", err)
	}

	log.Printf("\nDeployment complete!")
	log.Printf("App: %s", appName)
	log.Printf("Volume: %s", volumeID)
	log.Printf("Machine: %s", machineID)
	log.Printf("Image: %s", imageRef)
}
