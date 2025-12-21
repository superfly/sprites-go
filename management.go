package sprites

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strconv"
)

// CreateSprite creates a new sprite with the given name and optional configuration
func (c *Client) CreateSprite(ctx context.Context, name string, config *SpriteConfig) (*Sprite, error) {
	return c.CreateSpriteWithOrg(ctx, name, config, nil)
}

// CreateSpriteWithOrg creates a new sprite with the given name, optional configuration, and organization information
func (c *Client) CreateSpriteWithOrg(ctx context.Context, name string, config *SpriteConfig, org *OrganizationInfo) (*Sprite, error) {
	req := CreateSpriteRequest{
		Name:   name,
		Config: config,
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	// Build URL
	url := fmt.Sprintf("%s/v1/sprites", c.baseURL)

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to create sprite: %w", err)
	}
	defer resp.Body.Close()

	// Read response body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check status code
	if resp.StatusCode != http.StatusCreated {
		return nil, fmt.Errorf("failed to create sprite (status %d): %s", resp.StatusCode, string(body))
	}

	// Parse response
	var createResp CreateSpriteResponse
	if err := json.Unmarshal(body, &createResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Return a sprite object with the name
	sprite := &Sprite{
		name:   createResp.Name,
		Status: "created",
		client: c,
		org:    org,
	}

	return sprite, nil
}

// GetSprite retrieves information about a specific sprite
func (c *Client) GetSprite(ctx context.Context, name string) (*Sprite, error) {
	return c.GetSpriteWithOrg(ctx, name, nil)
}

// GetSpriteWithOrg retrieves information about a specific sprite with organization information
func (c *Client) GetSpriteWithOrg(ctx context.Context, name string, org *OrganizationInfo) (*Sprite, error) {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s", c.baseURL, name)

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to get sprite: %w", err)
	}
	defer resp.Body.Close()

	// Check status code
	if resp.StatusCode == http.StatusNotFound {
		return nil, fmt.Errorf("sprite not found: %s", name)
	}
	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("failed to get sprite (status %d): %s", resp.StatusCode, string(body))
	}

	// Parse response
	var info SpriteInfo
	if err := json.NewDecoder(resp.Body).Decode(&info); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Convert to Sprite
	sprite := &Sprite{
		name:             info.Name,
		client:           c,
		org:              org,
		ID:               info.ID,
		OrganizationName: info.Organization,
		Status:           info.Status,
		Config:           info.Config,
		Environment:      info.Environment,
		CreatedAt:        info.CreatedAt,
		UpdatedAt:        info.UpdatedAt,
		BucketName:       info.BucketName,
		PrimaryRegion:    info.PrimaryRegion,
		URL:              info.URL,
		URLSettings:      info.URLSettings,
	}
	return sprite, nil
}

// ListSprites retrieves a list of sprites with optional filtering
func (c *Client) ListSprites(ctx context.Context, opts *ListOptions) (*SpriteList, error) {
	if opts == nil {
		opts = &ListOptions{
			MaxResults: 100,
		}
	}

	// Build URL with query parameters
	baseURL := fmt.Sprintf("%s/v1/sprites", c.baseURL)
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("failed to parse URL: %w", err)
	}

	q := u.Query()
	if opts.MaxResults > 0 {
		q.Set("max_results", strconv.Itoa(opts.MaxResults))
	}
	if opts.ContinuationToken != "" {
		q.Set("continuation_token", opts.ContinuationToken)
	}
	if opts.Prefix != "" {
		q.Set("prefix", opts.Prefix)
	}
	u.RawQuery = q.Encode()

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "GET", u.String(), nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to list sprites: %w", err)
	}
	defer resp.Body.Close()

	// Check status
	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("failed to list sprites (status %d): %s", resp.StatusCode, string(body))
	}

	// Parse response
	var listResp SpriteList
	if err := json.NewDecoder(resp.Body).Decode(&listResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Note: Sprites in the list response are SpriteInfo, not Sprite objects
	// They don't have a client reference

	return &listResp, nil
}

// ListAllSprites retrieves all sprites, handling pagination automatically
func (c *Client) ListAllSprites(ctx context.Context, prefix string) ([]*Sprite, error) {
	return c.ListAllSpritesWithOrg(ctx, prefix, nil)
}

// ListAllSpritesWithOrg retrieves all sprites with organization information, handling pagination automatically
func (c *Client) ListAllSpritesWithOrg(ctx context.Context, prefix string, org *OrganizationInfo) ([]*Sprite, error) {
	var allSprites []*Sprite
	continuationToken := ""

	for {
		opts := &ListOptions{
			Prefix:            prefix,
			MaxResults:        100,
			ContinuationToken: continuationToken,
		}

		list, err := c.ListSprites(ctx, opts)
		if err != nil {
			return nil, err
		}

		// Convert SpriteInfo to Sprite objects
		for _, info := range list.Sprites {
			sprite := &Sprite{
				name:             info.Name,
				client:           c,
				org:              org,
				ID:               info.ID,
				OrganizationName: info.Organization,
				Status:           info.Status,
				Config:           info.Config,
				Environment:      info.Environment,
				CreatedAt:        info.CreatedAt,
				UpdatedAt:        info.UpdatedAt,
				BucketName:       info.BucketName,
				PrimaryRegion:    info.PrimaryRegion,
				URL:              info.URL,
				URLSettings:      info.URLSettings,
			}
			allSprites = append(allSprites, sprite)
		}

		if !list.HasMore || list.NextContinuationToken == "" {
			break
		}

		continuationToken = list.NextContinuationToken
	}

	return allSprites, nil
}

// DeleteSprite deletes a sprite
func (c *Client) DeleteSprite(ctx context.Context, name string) error {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s", c.baseURL, name)

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "DELETE", url, nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to delete sprite: %w", err)
	}
	defer resp.Body.Close()

	// Check status
	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusNoContent {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("failed to delete sprite (status %d): %s", resp.StatusCode, string(body))
	}

	return nil
}

// DestroySprite is an alias for DeleteSprite to match the client's naming
func (c *Client) DestroySprite(ctx context.Context, name string) error {
	return c.DeleteSprite(ctx, name)
}

// Delete deletes this sprite
func (s *Sprite) Delete(ctx context.Context) error {
	return s.client.DeleteSprite(ctx, s.name)
}

// UpgradeSprite upgrades a sprite to the latest version
func (c *Client) UpgradeSprite(ctx context.Context, name string) error {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s/upgrade", c.baseURL, name)

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to upgrade sprite: %w", err)
	}
	defer resp.Body.Close()

	// Check status
	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusNoContent {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("failed to upgrade sprite (status %d): %s", resp.StatusCode, string(body))
	}

	return nil
}

// Upgrade upgrades this sprite to the latest version
func (s *Sprite) Upgrade(ctx context.Context) error {
	return s.client.UpgradeSprite(ctx, s.name)
}

// UpdateURLSettings updates the URL authentication settings for a sprite
func (c *Client) UpdateURLSettings(ctx context.Context, spriteName string, settings *URLSettings) error {
	req := UpdateURLSettingsRequest{
		URLSettings: settings,
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		return fmt.Errorf("failed to marshal request: %w", err)
	}

	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s", c.baseURL, spriteName)

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "PUT", url, bytes.NewReader(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to update URL settings: %w", err)
	}
	defer resp.Body.Close()

	// Check status code
	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("failed to update URL settings (status %d): %s", resp.StatusCode, string(body))
	}

	return nil
}

// UpdateURLSettings updates the URL authentication settings for this sprite
func (s *Sprite) UpdateURLSettings(ctx context.Context, settings *URLSettings) error {
	return s.client.UpdateURLSettings(ctx, s.name, settings)
}
