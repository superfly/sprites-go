package sprites

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
)

// GetNetworkPolicy retrieves the current network policy for a sprite
func (c *Client) GetNetworkPolicy(ctx context.Context, spriteName string) (*NetworkPolicy, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s/policy/network", c.baseURL, spriteName)

	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	var policy NetworkPolicy
	if err := json.NewDecoder(resp.Body).Decode(&policy); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &policy, nil
}

// GetNetworkPolicy retrieves the current network policy for this sprite
func (s *Sprite) GetNetworkPolicy(ctx context.Context) (*NetworkPolicy, error) {
	return s.client.GetNetworkPolicy(ctx, s.name)
}

// UpdateNetworkPolicy updates the network policy for a sprite
func (c *Client) UpdateNetworkPolicy(ctx context.Context, spriteName string, policy *NetworkPolicy) error {
	url := fmt.Sprintf("%s/v1/sprites/%s/policy/network", c.baseURL, spriteName)

	jsonData, err := json.Marshal(policy)
	if err != nil {
		return fmt.Errorf("failed to marshal policy: %w", err)
	}

	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	httpReq.Header.Set("Content-Type", "application/json")

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusBadRequest {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("invalid policy: %s", string(body))
	}

	if resp.StatusCode != http.StatusNoContent {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	return nil
}

// UpdateNetworkPolicy updates the network policy for this sprite
func (s *Sprite) UpdateNetworkPolicy(ctx context.Context, policy *NetworkPolicy) error {
	return s.client.UpdateNetworkPolicy(ctx, s.name, policy)
}
