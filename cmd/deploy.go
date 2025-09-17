package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"sync"
	"time"

	"github.com/superfly/fly-go"
	"github.com/superfly/fly-go/flaps"
	"github.com/superfly/fly-go/tokens"
)

// Global mutex for coordinating console output
var outputMutex sync.Mutex

// buildOutputWriter manages the output of build processes
// It shows only the last N lines during progress and collapses on success
type buildOutputWriter struct {
	label        string
	lines        []string
	maxLines     int
	allOutput    bytes.Buffer
	mu           sync.Mutex
	lastUpdate   time.Time
	startTime    time.Time
	isError      bool
	done         bool
	showProgress bool
}

func newBuildOutputWriter(label string, showProgress bool) *buildOutputWriter {
	return &buildOutputWriter{
		label:        label,
		lines:        make([]string, 0, 10),
		maxLines:     10,
		startTime:    time.Now(),
		lastUpdate:   time.Now(),
		showProgress: showProgress,
	}
}

func (w *buildOutputWriter) Write(p []byte) (n int, err error) {
	w.mu.Lock()
	defer w.mu.Unlock()

	// Store all output for error cases
	w.allOutput.Write(p)

	// Process new lines
	scanner := bufio.NewScanner(bytes.NewReader(p))
	for scanner.Scan() {
		line := scanner.Text()
		w.lines = append(w.lines, line)
		if len(w.lines) > w.maxLines {
			w.lines = w.lines[len(w.lines)-w.maxLines:]
		}
	}

	// Update display if showing progress and enough time has passed
	if w.showProgress && time.Since(w.lastUpdate) > 500*time.Millisecond && !w.done {
		outputMutex.Lock()
		w.display()
		outputMutex.Unlock()
		w.lastUpdate = time.Now()
	}

	return len(p), nil
}

func (w *buildOutputWriter) display() {
	// Clear previous lines (move cursor up and clear)
	fmt.Printf("\033[%dA\033[J", w.maxLines+2)

	// Show header
	elapsed := time.Since(w.startTime).Round(time.Second)
	fmt.Printf("[%s] Building %s... (%s)\n", time.Now().Format("15:04:05"), w.label, elapsed)
	fmt.Println(strings.Repeat("-", 80))

	// Show last N lines
	for _, line := range w.lines {
		// Truncate long lines
		if len(line) > 100 {
			line = line[:97] + "..."
		}
		fmt.Printf(" %s\n", line)
	}

	// Pad if we have fewer lines
	for i := len(w.lines); i < w.maxLines; i++ {
		fmt.Println()
	}
}

func (w *buildOutputWriter) setupProgressDisplay() {
	if !w.showProgress {
		return
	}

	outputMutex.Lock()
	defer outputMutex.Unlock()

	// Reserve space for progress display
	for i := 0; i < w.maxLines+2; i++ {
		fmt.Println()
	}
	w.display()
}

func (w *buildOutputWriter) finish(err error) {
	w.mu.Lock()
	w.done = true
	w.isError = err != nil
	elapsed := time.Since(w.startTime).Round(time.Second)
	w.mu.Unlock()

	outputMutex.Lock()
	defer outputMutex.Unlock()

	if w.showProgress {
		// Clear the progress display
		fmt.Printf("\033[%dA\033[J", w.maxLines+2)
	}

	if err != nil {
		// On error, show all output
		fmt.Printf("[%s] ❌ Failed building %s after %s\n", time.Now().Format("15:04:05"), w.label, elapsed)
		fmt.Println(strings.Repeat("=", 80))
		fmt.Print(w.allOutput.String())
		fmt.Println(strings.Repeat("=", 80))
	} else {
		// On success, show single line
		fmt.Printf("[%s] ✓ Successfully built %s in %s\n", time.Now().Format("15:04:05"), w.label, elapsed)
	}
}

// apiRequest makes a request to the Fly.io API
func apiRequest(method, url string, token string, body interface{}) (*http.Response, error) {
	var reqBody io.Reader
	if body != nil {
		jsonBody, err := json.Marshal(body)
		if err != nil {
			return nil, fmt.Errorf("failed to marshal request body: %w", err)
		}
		reqBody = bytes.NewReader(jsonBody)
	}

	req, err := http.NewRequest(method, url, reqBody)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Authorization", "Bearer "+token)
	req.Header.Set("Content-Type", "application/json")

	client := &http.Client{Timeout: 30 * time.Second}
	return client.Do(req)
}

// getMachineConfig fetches the current machine config via direct API call
func getMachineConfig(appName, machineID, token string) (*fly.MachineConfig, error) {
	url := fmt.Sprintf("https://api.machines.dev/v1/apps/%s/machines/%s", appName, machineID)

	resp, err := apiRequest("GET", url, token, nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("failed to get machine config: status %d, body: %s", resp.StatusCode, string(body))
	}

	var machine struct {
		Config fly.MachineConfig `json:"config"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&machine); err != nil {
		return nil, fmt.Errorf("failed to decode machine response: %w", err)
	}

	return &machine.Config, nil
}

// updateMachineImageOnly updates only the image reference in an existing machine config
func updateMachineImageOnly(config *fly.MachineConfig, newImageRef string) {
	// Update top-level image reference
	config.Image = newImageRef

	// Update image reference in the first container
	if config.Containers != nil && len(config.Containers) > 0 {
		config.Containers[0].Image = newImageRef
	}
}

// updateVolumeImages updates the image references for system-base and languages-image volumes
func updateVolumeImages(config *fly.MachineConfig, ubuntuImageRef, languagesImageRef string) {
	if config.Volumes == nil {
		return
	}

	for i := range config.Volumes {
		switch config.Volumes[i].Name {
		case "system-base":
			if ubuntuImageRef != "" {
				config.Volumes[i].Image = ubuntuImageRef
				log.Printf("Updated system-base volume to use image: %s\n", ubuntuImageRef)
			}
		case "languages-image":
			if languagesImageRef != "" {
				config.Volumes[i].Image = languagesImageRef
				log.Printf("Updated languages-image volume to use image: %s\n", languagesImageRef)
			}
		}
	}
}

// updateMachine updates a machine config via direct API call
func updateMachine(appName, machineID, token string, config *fly.MachineConfig) error {
	url := fmt.Sprintf("https://api.machines.dev/v1/apps/%s/machines/%s", appName, machineID)

	updatePayload := map[string]interface{}{
		"config": config,
	}

	resp, err := apiRequest("POST", url, token, updatePayload)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("failed to update machine: status %d, body: %s", resp.StatusCode, string(body))
	}

	return nil
}

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

// buildImage builds and pushes a Docker image
func buildImage(appName, label, dockerfile, buildTarget, workDir string, showProgress bool) error {
	imageRef := fmt.Sprintf("registry.fly.io/%s:%s", appName, label)

	args := []string{
		"deploy",
		"-a", appName,
		"--build-only",
		"--buildkit",
		"--push",
		"--image-label", label,
	}

	if dockerfile != "" {
		args = append(args, "--dockerfile", dockerfile)
	}

	if buildTarget != "" {
		args = append(args, "--build-target", buildTarget)
	}

	// Create output writer for this build
	outputWriter := newBuildOutputWriter(imageRef, showProgress)

	buildCmd := exec.Command("fly", args...)
	buildCmd.Dir = workDir
	buildCmd.Stdout = outputWriter
	buildCmd.Stderr = outputWriter

	// Setup progress display if enabled
	outputWriter.setupProgressDisplay()

	err := buildCmd.Run()
	outputWriter.finish(err)

	if err != nil {
		return fmt.Errorf("failed to build image %s: %w", label, err)
	}

	return nil
}

func main() {
	var appName string
	var skipBuild bool
	var replaceConfig bool
	var updateBase bool
	var updateLanguages bool
	flag.StringVar(&appName, "a", "", "Fly app name")
	flag.BoolVar(&skipBuild, "skip-build", false, "Skip docker build step and just push the image")
	flag.BoolVar(&replaceConfig, "replace-config", false, "Replace entire machine config instead of just updating the image")
	flag.BoolVar(&updateBase, "update-base", false, "Build and push base Ubuntu image")
	flag.BoolVar(&updateLanguages, "update-languages", false, "Build and push languages image")
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

	// Build and push Docker images
	label := fmt.Sprintf("%d", time.Now().Unix())
	imageRef := fmt.Sprintf("registry.fly.io/%s:%s", appName, label)

	// Prepare image refs for base images
	var ubuntuImageRef, languagesImageRef string
	if updateBase {
		ubuntuImageRef = fmt.Sprintf("registry.fly.io/%s:%s-ubuntu", appName, label)
	}
	if updateLanguages {
		languagesImageRef = fmt.Sprintf("registry.fly.io/%s:%s-languages", appName, label)
	}

	// Build all images in parallel
	if !skipBuild || updateBase || updateLanguages {
		var wg sync.WaitGroup
		errChan := make(chan error, 3) // Buffer for up to 3 errors

		// Count how many builds we're doing
		buildCount := 0
		if !skipBuild {
			buildCount++
		}
		if updateBase {
			buildCount++
		}
		if updateLanguages {
			buildCount++
		}

		// For single builds, show progress; for multiple builds, don't show progress to avoid conflicts
		showProgress := buildCount == 1

		if buildCount > 1 {
			log.Printf("Starting %d parallel builds...\n", buildCount)
		}

		// Build main image if not skipping
		if !skipBuild {
			wg.Add(1)
			go func() {
				defer wg.Done()
				if !showProgress {
					log.Println("  • Building main Docker image...")
				}
				if err := buildImage(appName, label, "", "", "../", showProgress); err != nil {
					errChan <- fmt.Errorf("main image: %w", err)
				}
			}()
		} else if buildCount == 0 {
			log.Println("Skipping main docker image build.")
		}

		// Build Ubuntu base image if requested
		if updateBase {
			wg.Add(1)
			go func() {
				defer wg.Done()
				if !showProgress {
					log.Println("  • Building Ubuntu base image...")
				}
				ubuntuLabel := fmt.Sprintf("%s-ubuntu", label)
				if err := buildImage(appName, ubuntuLabel, "Dockerfile", "", "../base-env/images/ubuntu-devtools", showProgress); err != nil {
					errChan <- fmt.Errorf("ubuntu base image: %w", err)
				}
			}()
		}

		// Build languages image if requested
		if updateLanguages {
			wg.Add(1)
			go func() {
				defer wg.Done()
				if !showProgress {
					log.Println("  • Building languages image...")
				}
				languagesLabel := fmt.Sprintf("%s-languages", label)
				if err := buildImage(appName, languagesLabel, "Dockerfile", "languages", "../base-env/images/ubuntu-devtools", showProgress); err != nil {
					errChan <- fmt.Errorf("languages image: %w", err)
				}
			}()
		}

		// Wait for all builds to complete
		wg.Wait()
		close(errChan)

		// Check for errors
		var errors []string
		for err := range errChan {
			errors = append(errors, err.Error())
		}

		if len(errors) > 0 {
			log.Fatal("Failed to build images:\n  - ", strings.Join(errors, "\n  - "))
		}

		if buildCount > 1 {
			log.Println("\nAll images built successfully!")
		}
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

	// If only one machine exists, use it regardless of name
	if len(machines) == 1 {
		machineID = machines[0].ID
		existingMachine = machines[0]
		log.Printf("Found single machine in app: %s (name: %s)\n", machineID, machines[0].Name)
	} else if len(machines) > 1 {
		// Look for existing sprite_compute machine
		for _, m := range machines {
			if m.Name == "sprite_compute" || strings.HasPrefix(m.Name, "sprites-") {
				machineID = m.ID
				existingMachine = m
				log.Printf("Found existing machine: %s (name: %s)\n", machineID, m.Name)
				break
			}
		}
		if existingMachine == nil {
			log.Fatal("Multiple machines found but none match expected naming pattern (sprite_compute or sprites-*)")
		}
	}

	// Handle volume based on whether we found a machine
	var volumeID string
	var existingContainerEnvVars map[string]string
	var existingSpriteToken string

	if existingMachine != nil {
		// Extract existing container environment variables
		if existingMachine.Config != nil && len(existingMachine.Config.Containers) > 0 {
			// Look for the main container (usually named "sprite" or the first one)
			for _, container := range existingMachine.Config.Containers {
				// Check ExtraEnv for environment variables
				if container.ExtraEnv != nil && len(container.ExtraEnv) > 0 {
					existingContainerEnvVars = make(map[string]string)
					for k, v := range container.ExtraEnv {
						existingContainerEnvVars[k] = v
						log.Printf("Found existing container env var: %s\n", k)
						// Capture SPRITE_HTTP_API_TOKEN if present
						if k == "SPRITE_HTTP_API_TOKEN" {
							existingSpriteToken = v
							log.Printf("Found existing SPRITE_HTTP_API_TOKEN in container\n")
						}
					}
					// Use env vars from first container with env vars
					break
				}
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

		// If existing machine has no volume, fail
		if volumeID == "" {
			log.Fatal("Existing machine has no volume attached. Cannot deploy to a machine without persistent storage.")
		}
	}

	// If no machine found, check all volumes
	if existingMachine == nil && volumeID == "" {
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

	var machineConfig fly.MachineConfig

	// Only read and process machine config if we're replacing the entire config
	if replaceConfig || existingMachine == nil {
		// Read machine config
		configData, err := os.ReadFile("machine-config.json")
		if err != nil {
			log.Fatal("Failed to read machine-config.json: ", err)
		}

		// Use existing SPRITE_HTTP_API_TOKEN if available, otherwise check environment
		spriteToken := existingSpriteToken
		if spriteToken == "" {
			spriteToken = os.Getenv("SPRITE_HTTP_API_TOKEN")
			if spriteToken == "" {
				log.Fatal("SPRITE_HTTP_API_TOKEN not found in existing machine config or environment variable")
			}
			log.Printf("Using SPRITE_HTTP_API_TOKEN from environment variable\n")
		} else {
			log.Printf("Using SPRITE_HTTP_API_TOKEN from existing machine config\n")
		}

		// Replace placeholders in memory
		configStr := string(configData)
		configStr = strings.ReplaceAll(configStr, "<volume_id>", volumeID)
		configStr = strings.ReplaceAll(configStr, "<image_ref>", imageRef)
		configStr = strings.ReplaceAll(configStr, "<sprite_token>", spriteToken)

		// Parse the config into machine config
		if err := json.Unmarshal([]byte(configStr), &machineConfig); err != nil {
			log.Fatal("Failed to parse machine config: ", err)
		}

		// Update volume images if base images were built
		if updateBase || updateLanguages {
			updateVolumeImages(&machineConfig, ubuntuImageRef, languagesImageRef)
		}

		// Only preserve specific environment variables from existing config
		preserveEnvVars := []string{"SPRITE_HTTP_API_TOKEN", "SPRITE_PRIMARY_REGION"}
		if existingContainerEnvVars != nil && len(existingContainerEnvVars) > 0 {
			log.Printf("Checking %d existing container environment variables for preservation\n", len(existingContainerEnvVars))

			// Ensure we have at least one container in the new config
			if machineConfig.Containers == nil || len(machineConfig.Containers) == 0 {
				log.Printf("Warning: No containers found in new config, cannot preserve environment variables\n")
			} else {
				// Initialize the env map if it doesn't exist
				if machineConfig.Containers != nil && len(machineConfig.Containers) > 0 {
					for i := range machineConfig.Containers {
						if machineConfig.Containers[i].ExtraEnv == nil {
							machineConfig.Containers[i].ExtraEnv = make(map[string]string)
						}
					}
				}

				// Only preserve specific env vars
				for _, envVar := range preserveEnvVars {
					if value, exists := existingContainerEnvVars[envVar]; exists {
						// Check if already in new config
						found := false
						for i := range machineConfig.Containers {
							if _, exists := machineConfig.Containers[i].ExtraEnv[envVar]; exists {
								found = true
								log.Printf("  - Keeping new value for env var: %s\n", envVar)
								break
							}
						}
						if !found {
							machineConfig.Containers[0].ExtraEnv[envVar] = value
							log.Printf("  - Preserving env var: %s\n", envVar)
						}
					}
				}

				// Log what we're dropping
				for k := range existingContainerEnvVars {
					preserve := false
					for _, envVar := range preserveEnvVars {
						if k == envVar {
							preserve = true
							break
						}
					}
					if !preserve {
						log.Printf("  - Dropping env var: %s\n", k)
					}
				}
			}
		}

		// Print the merged environment variables
		if machineConfig.Containers != nil && len(machineConfig.Containers) > 0 && machineConfig.Containers[0].ExtraEnv != nil {
			log.Printf("\n=== Final Merged Environment Variables ===")
			log.Printf("Total env vars: %d\n", len(machineConfig.Containers[0].ExtraEnv))
			for k, v := range machineConfig.Containers[0].ExtraEnv {
				// Mask sensitive values
				displayValue := v
				if strings.Contains(strings.ToLower(k), "token") ||
					strings.Contains(strings.ToLower(k), "secret") ||
					strings.Contains(strings.ToLower(k), "password") {
					displayValue = "***MASKED***"
				}
				log.Printf("  %s = %s\n", k, displayValue)
			}
		} else {
			log.Printf("\n=== No container environment variables found ===")
		}

		// Print the config that will be sent
		log.Printf("\n=== Machine Config to Deploy ===")
		configJSON, err := json.MarshalIndent(machineConfig, "", "  ")
		if err != nil {
			log.Fatal("Failed to marshal config for display: ", err)
		}
		log.Printf("%s\n", string(configJSON))

		// Save config to tmp file
		tmpDir := "tmp"
		if err := os.MkdirAll(tmpDir, 0755); err != nil {
			log.Printf("Warning: Failed to create tmp directory: %v", err)
		} else {
			configFile := fmt.Sprintf("%s/machine-%s-config.json", tmpDir, appName)
			if err := os.WriteFile(configFile, configJSON, 0644); err != nil {
				log.Printf("Warning: Failed to save config to %s: %v", configFile, err)
			} else {
				log.Printf("Config saved to: %s", configFile)
			}
		}
	}

	if existingMachine != nil {
		// Update existing machine
		log.Printf("Updating machine %s...\n", machineID)

		if !replaceConfig {
			// Fetch current config and only update the image
			log.Printf("Fetching current machine config to preserve settings...")
			currentConfig, err := getMachineConfig(appName, machineID, token)
			if err != nil {
				log.Fatal("Failed to get current machine config: ", err)
			}

			// Update only the image references
			updateMachineImageOnly(currentConfig, imageRef)

			// Update volume images if base images were built
			if updateBase || updateLanguages {
				updateVolumeImages(currentConfig, ubuntuImageRef, languagesImageRef)
			}

			// Save the updated config to tmp file
			tmpDir := "tmp"
			if err := os.MkdirAll(tmpDir, 0755); err != nil {
				log.Printf("Warning: Failed to create tmp directory: %v", err)
			} else {
				configJSON, err := json.MarshalIndent(currentConfig, "", "  ")
				if err != nil {
					log.Printf("Warning: Failed to marshal config for saving: %v", err)
				} else {
					configFile := fmt.Sprintf("%s/machine-%s-config.json", tmpDir, appName)
					if err := os.WriteFile(configFile, configJSON, 0644); err != nil {
						log.Printf("Warning: Failed to save config to %s: %v", configFile, err)
					} else {
						log.Printf("Config saved to: %s", configFile)
					}
				}
			}

			// Update the machine using direct API
			log.Printf("Updating machine with new image: %s\n", imageRef)
			if err := updateMachine(appName, machineID, token, currentConfig); err != nil {
				log.Fatal("Failed to update machine: ", err)
			}

			log.Printf("Updated machine: %s (image only)\n", machineID)
		} else {
			// Use the existing behavior - replace entire config
			log.Printf("Replacing entire machine config...")
			updateInput := fly.LaunchMachineInput{
				ID:     machineID,
				Config: &machineConfig,
			}
			machine, err := flapsClient.Update(ctx, updateInput, "")
			if err != nil {
				log.Fatal("Failed to update machine: ", err)
			}

			log.Printf("Updated machine: %s (full config)\n", machine.ID)
		}
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
