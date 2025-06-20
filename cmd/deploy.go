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
	imageRef := fmt.Sprintf("registry.fly.io/%s:latest", appName)

	if !skipBuild {
		log.Println("Building Docker image...")
		// Use buildx for better cross-platform support
		buildCmd := exec.Command("docker", "buildx", "build", "--platform", "linux/amd64", "--load", "-t", imageRef, "..")
		buildCmd.Stdout = os.Stdout
		buildCmd.Stderr = os.Stderr
		if err := buildCmd.Run(); err != nil {
			log.Fatal("Failed to build Docker image: ", err)
		}
	} else {
		log.Println("Skipping docker image build.")
	}

	log.Println("Authenticating with Docker...")
	authCmd := exec.Command("flyctl", "auth", "docker")
	authCmd.Stdout = os.Stdout
	authCmd.Stderr = os.Stderr
	if err := authCmd.Run(); err != nil {
		log.Fatal("Failed to authenticate with Docker: ", err)
	}

	log.Println("Pushing Docker image...")
	pushCmd := exec.Command("docker", "push", imageRef)
	pushCmd.Stdout = os.Stdout
	pushCmd.Stderr = os.Stderr
	if err := pushCmd.Run(); err != nil {
		log.Fatal("Failed to push Docker image: ", err)
	}

	// Create flaps client for machine management
	flapsClient, err := flaps.NewWithOptions(ctx, flaps.NewClientOpts{
		AppName: appName,
		Tokens:  tokens.Parse(token),
	})
	if err != nil {
		log.Fatal("Failed to create flaps client: ", err)
	}

	// Handle volume
	var volumeID string
	volumes, err := flapsClient.GetVolumes(ctx)
	if err != nil {
		log.Fatal("Failed to list volumes: ", err)
	}

	// Look for existing sprite_data volume
	for _, v := range volumes {
		if v.Name == "sprite_data" {
			volumeID = v.ID
			log.Printf("Found existing volume: %s\n", volumeID)
			break
		}
	}

	// Create volume if not found
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

	// Handle machine
	var machineID string
	machines, err := flapsClient.List(ctx, "")
	if err != nil {
		log.Fatal("Failed to list machines: ", err)
	}

	// Look for existing sprite_compute machine
	for _, m := range machines {
		if m.Name == "sprite_compute" {
			machineID = m.ID
			log.Printf("Found existing machine: %s\n", machineID)
			break
		}
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

	// Print the config that will be sent
	log.Printf("\n=== Machine Config to Deploy ===")
	configJSON, err := json.MarshalIndent(machineConfig, "", "  ")
	if err != nil {
		log.Fatal("Failed to marshal config for display: ", err)
	}
	log.Printf("%s\n", string(configJSON))

	if machineID != "" {
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

	log.Printf("\nDeployment complete!")
	log.Printf("App: %s", appName)
	log.Printf("Volume: %s", volumeID)
	log.Printf("Machine: %s", machineID)
	log.Printf("Image: %s", imageRef)
}
