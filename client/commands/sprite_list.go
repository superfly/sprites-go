package commands

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"
	"time"

	"github.com/sprite-env/client/config"
)

// SpritesListResponse represents the response from listing sprites
type SpritesListResponse struct {
	Sprites               []SpriteInfo `json:"sprites"`
	HasMore               bool         `json:"has_more"`
	NextContinuationToken string       `json:"next_continuation_token,omitempty"`
}

// ListSprites fetches the list of sprites from the API
func ListSprites(org *config.Organization) ([]SpriteInfo, error) {
	var allSprites []SpriteInfo
	continuationToken := ""

	for {
		// Build URL with query parameters
		baseURL := fmt.Sprintf("%s/v1/sprites", getSpritesAPIURL(org))
		u, err := url.Parse(baseURL)
		if err != nil {
			return nil, fmt.Errorf("failed to parse URL: %w", err)
		}

		q := u.Query()
		q.Set("max_results", "100")
		if continuationToken != "" {
			q.Set("continuation_token", continuationToken)
		}
		u.RawQuery = q.Encode()

		// Create request
		httpReq, err := http.NewRequest("GET", u.String(), nil)
		if err != nil {
			return nil, fmt.Errorf("failed to create request: %w", err)
		}

		token, err := org.GetToken()
		if err != nil {
			return nil, fmt.Errorf("failed to get auth token: %w", err)
		}
		httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

		// Make request
		client := &http.Client{Timeout: 30 * time.Second}
		resp, err := client.Do(httpReq)
		if err != nil {
			return nil, fmt.Errorf("failed to list sprites: %w", err)
		}
		defer resp.Body.Close()

		// Read response
		body, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, fmt.Errorf("failed to read response: %w", err)
		}

		// Check status
		if resp.StatusCode != http.StatusOK {
			return nil, fmt.Errorf("failed to list sprites (status %d): %s", resp.StatusCode, string(body))
		}

		// Parse response
		var listResp SpritesListResponse
		if err := json.Unmarshal(body, &listResp); err != nil {
			return nil, fmt.Errorf("failed to parse response: %w", err)
		}

		allSprites = append(allSprites, listResp.Sprites...)

		// Check if there are more results
		if !listResp.HasMore || listResp.NextContinuationToken == "" {
			break
		}

		continuationToken = listResp.NextContinuationToken
	}

	return allSprites, nil
}

// SyncSpritesWithConfig updates the local config with sprites from the API
func SyncSpritesWithConfig(cfg *config.Manager, org *config.Organization) error {
	// Only sync for organizations using the new API
	if !strings.Contains(getSpritesAPIURL(org), "sprites.dev") {
		return nil
	}

	sprites, err := ListSprites(org)
	if err != nil {
		return fmt.Errorf("failed to list sprites: %w", err)
	}

	// Update the organization's sprites in config
	currentOrg := cfg.GetCurrentOrg()
	if currentOrg != nil && currentOrg.Name == org.Name {
		// Clear existing sprites
		currentOrg.Sprites = make(map[string]*config.Sprite)

		// Add sprites from API
		for _, sprite := range sprites {
			currentOrg.Sprites[sprite.Name] = &config.Sprite{
				Name: sprite.Name,
				ID:   sprite.ID,
			}
		}

		// Save the updated config
		if err := cfg.Save(); err != nil {
			return fmt.Errorf("failed to save config: %w", err)
		}
	}

	return nil
}
