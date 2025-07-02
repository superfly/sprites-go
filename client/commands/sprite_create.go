package commands

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"time"

	"github.com/sprite-env/client/config"
)

// SpriteCreateRequest represents the request to create a sprite
type SpriteCreateRequest struct {
	Name        string            `json:"name"`
	Config      *SpriteConfig     `json:"config,omitempty"`
	Environment map[string]string `json:"environment,omitempty"`
}

// SpriteConfig represents sprite configuration
type SpriteConfig struct {
	RamMB     int    `json:"ram_mb,omitempty"`
	CPUs      int    `json:"cpus,omitempty"`
	Region    string `json:"region,omitempty"`
	StorageGB int    `json:"storage_gb,omitempty"`
}

// SpriteCreateResponse represents the response from sprite creation
type SpriteCreateResponse struct {
	Name string `json:"name"`
}

// SpriteInfo represents sprite information from the API
type SpriteInfo struct {
	ID            string            `json:"id"`
	Name          string            `json:"name"`
	Organization  string            `json:"organization"`
	Status        string            `json:"status"`
	Config        *SpriteConfig     `json:"config,omitempty"`
	Environment   map[string]string `json:"environment,omitempty"`
	CreatedAt     time.Time         `json:"created_at"`
	UpdatedAt     time.Time         `json:"updated_at"`
	BucketName    string            `json:"bucket_name,omitempty"`
	PrimaryRegion string            `json:"primary_region,omitempty"`
}

// CreateSprite creates a new sprite on the server
// TODO: Implement this function when the server API is ready
//
// This function should:
// 1. Make an API call to create the sprite with the given name
// 2. Poll or wait for the sprite to be ready
// 3. Get the sprite ID from the server
// 4. Call SaveSprite to update the local config
// 5. Return any errors that occur
//
// Expected usage:
//
//	if isNewSprite {
//	    if err := CreateSprite(cfg, org, sprite.Name); err != nil {
//	        fmt.Fprintf(os.Stderr, "Error creating sprite: %v\n", err)
//	        os.Exit(1)
//	    }
//	    // Sprite is now created and ready to use
//	}
func CreateSprite(cfg *config.Manager, org *config.Organization, spriteName string) error {
	// Create the request
	req := SpriteCreateRequest{
		Name: spriteName,
		// TODO: Add config and environment based on user preferences or defaults
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		return fmt.Errorf("failed to marshal request: %w", err)
	}

	// Build the URL
	url := fmt.Sprintf("%s/v1/sprites", getSpritesAPIURL(org))

	// Create HTTP request
	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	token, err := org.GetToken()
	if err != nil {
		return fmt.Errorf("failed to get auth token: %w", err)
	}
	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Make the request
	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to create sprite: %w", err)
	}
	defer resp.Body.Close()

	// Read response body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("failed to read response: %w", err)
	}

	// Check status code
	if resp.StatusCode != http.StatusCreated {
		return fmt.Errorf("failed to create sprite (status %d): %s", resp.StatusCode, string(body))
	}

	// Parse response
	var createResp SpriteCreateResponse
	if err := json.Unmarshal(body, &createResp); err != nil {
		return fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for sprite to be ready by polling its status
	if err := waitForSpriteReady(org, spriteName); err != nil {
		return fmt.Errorf("sprite created but failed to become ready: %w", err)
	}

	// Get the sprite details to get its ID
	sprite, err := getSpriteInfo(org, spriteName)
	if err != nil {
		return fmt.Errorf("failed to get sprite info: %w", err)
	}

	// Save to local config
	if err := SaveSprite(cfg, spriteName, sprite.ID); err != nil {
		return fmt.Errorf("failed to save sprite to config: %w", err)
	}

	return nil
}

// waitForSpriteReady polls the sprite status until it's ready
func waitForSpriteReady(org *config.Organization, spriteName string) error {
	maxAttempts := 60 // 5 minutes with 5 second intervals
	for i := 0; i < maxAttempts; i++ {
		sprite, err := getSpriteInfo(org, spriteName)
		if err != nil {
			return err
		}

		if sprite.Status == "ready" || sprite.Status == "running" {
			return nil
		}

		if sprite.Status == "failed" || sprite.Status == "error" {
			return fmt.Errorf("sprite failed to start: %s", sprite.Status)
		}

		// Wait before next attempt
		time.Sleep(5 * time.Second)
	}

	return fmt.Errorf("timeout waiting for sprite to be ready")
}

// getSpriteInfo gets information about a specific sprite
func getSpriteInfo(org *config.Organization, spriteName string) (*SpriteInfo, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s", getSpritesAPIURL(org), spriteName)

	httpReq, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	token, err := org.GetToken()
	if err != nil {
		return nil, fmt.Errorf("failed to get auth token: %w", err)
	}
	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to get sprite info: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("failed to get sprite info (status %d): %s", resp.StatusCode, string(body))
	}

	var sprite SpriteInfo
	if err := json.Unmarshal(body, &sprite); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &sprite, nil
}
