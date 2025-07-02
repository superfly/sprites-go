package prompts

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"os"
	"strings"
	"time"

	"github.com/sprite-env/client/config"
)

// SpriteInfo represents basic sprite information
type SpriteInfo struct {
	ID     string `json:"id"`
	Name   string `json:"name"`
	Status string `json:"status"`
}

// SpritesListResponse represents the response from listing sprites
type SpritesListResponse struct {
	Sprites               []SpriteInfo `json:"sprites"`
	HasMore               bool         `json:"has_more"`
	NextContinuationToken string       `json:"next_continuation_token,omitempty"`
}

// OrganizationResponse represents the response from the organization endpoint
type OrganizationResponse struct {
	Organization string                 `json:"organization"`
	Resources    map[string]interface{} `json:"resources,omitempty"` // Ignored as requested
}

// fetchOrganizationInfo validates the token and fetches organization information
func fetchOrganizationInfo(token, apiURL string) (*OrganizationResponse, error) {
	// Build URL
	baseURL := fmt.Sprintf("%s/v1/organization", strings.TrimRight(apiURL, "/"))

	// Create request
	httpReq, err := http.NewRequest("GET", baseURL, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	// Make request
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch organization info: %w", err)
	}
	defer resp.Body.Close()

	// Read response
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check status
	if resp.StatusCode == http.StatusUnauthorized {
		return nil, fmt.Errorf("invalid API token")
	}
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Parse response
	var orgResp OrganizationResponse
	if err := json.Unmarshal(body, &orgResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	if orgResp.Organization == "" {
		return nil, fmt.Errorf("organization name not found in response")
	}

	return &orgResp, nil
}

// fetchSpritesFromAPI fetches sprites from the API
func fetchSpritesFromAPI(org *config.Organization) ([]SpriteInfo, error) {
	// Get API URL from environment or use default
	apiURL := org.URL
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		apiURL = strings.TrimRight(envURL, "/")
	} else if !strings.Contains(apiURL, "sprites.dev") {
		// If not using sprites.dev, use the default
		apiURL = "https://api.sprites.dev"
	}

	var allSprites []SpriteInfo
	continuationToken := ""

	for {
		// Build URL with query parameters
		baseURL := fmt.Sprintf("%s/v1/sprites", apiURL)
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

		httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", org.Token))

		// Make request
		client := &http.Client{Timeout: 10 * time.Second}
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
			return nil, fmt.Errorf("API returned status %d", resp.StatusCode)
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
