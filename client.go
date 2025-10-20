// Package sprites provides an idiomatic Go API for working with sprites.
package sprites

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"strings"
	"sync"
	"time"
)

// Client is the main SDK client for interacting with the sprite API.
type Client struct {
	baseURL    string
	token      string
	httpClient *http.Client

	// Control connection pools per sprite
	poolsMu sync.RWMutex
	pools   map[string]*controlPool

	// Control initialization behavior
	controlInitTimeout time.Duration
}

// Option is a functional option for configuring the SDK client.
type Option func(*Client)

// New creates a new SDK client with the given token and options.
func New(token string, opts ...Option) *Client {
	c := &Client{
		baseURL: "https://api.sprites.dev",
		token:   token,
		httpClient: &http.Client{
			Timeout: 30 * time.Second,
		},
		pools:              make(map[string]*controlPool),
		controlInitTimeout: 2 * time.Second,
	}

	for _, opt := range opts {
		opt(c)
	}

	// Normalize baseURL
	c.baseURL = strings.TrimRight(c.baseURL, "/")

	return c
}

// NewClient creates a new Sprites API client with explicit parameters.
// This is an alternative constructor for compatibility.
func NewClient(baseURL, token string) *Client {
	return New(token, WithBaseURL(baseURL))
}

// WithBaseURL sets a custom base URL for the sprite API.
func WithBaseURL(url string) Option {
	return func(c *Client) {
		c.baseURL = url
	}
}

// WithHTTPClient sets a custom HTTP client.
func WithHTTPClient(client *http.Client) Option {
	return func(c *Client) {
		c.httpClient = client
	}
}

// WithLogger sets the slog.Logger used by the SDK. This affects debug/info/error logs emitted by the SDK.
// If not set, a default error-level logger to stderr is used; set a different handler/level as desired.
func WithLogger(l *slog.Logger) Option {
	return func(c *Client) {
		SetLogger(l)
	}
}

// WithControlInitTimeout sets how long Sprite() will wait to establish a control connection
// before falling back to legacy endpoint API for that Sprite. Defaults to 2s.
func WithControlInitTimeout(d time.Duration) Option {
	return func(c *Client) {
		c.controlInitTimeout = d
	}
}

// Sprite returns a Sprite instance for the given name.
// This doesn't create the sprite on the server, it just returns a handle to work with it.
func (c *Client) Sprite(name string) *Sprite {
	s := &Sprite{name: name, client: c}
	// Eagerly probe control support; return sprite even if probe errors with 502
	// Callers can examine errors on first operation via s.lastProbeErr
	_ = s.probeControlSupport(context.Background())
	return s
}

// SpriteWithOrg returns a Sprite instance for the given name with organization information.
// This doesn't create the sprite on the server, it just returns a handle to work with it.
func (c *Client) SpriteWithOrg(name string, org *OrganizationInfo) *Sprite {
	s := &Sprite{name: name, client: c, org: org}
	_ = s.probeControlSupport(context.Background())
	return s
}

// Create creates a new sprite with the given name and returns a handle to it.
// Deprecated: Use CreateSprite with context instead.
func (c *Client) Create(name string) (*Sprite, error) {
	return c.CreateSprite(context.Background(), name, nil)
}

// List returns a list of available sprites.
// Deprecated: Use ListSprites with context instead.
func (c *Client) List() ([]*Sprite, error) {
	return c.ListAllSprites(context.Background(), "")
}

// CreateToken creates a sprite access token using a Fly.io macaroon token.
// This is a static method that doesn't require a client instance.
//
// The flyMacaroon should be a valid Fly.io authentication token (starts with "FlyV1").
// The orgSlug is the organization slug (e.g., "personal" or organization name).
// The inviteCode is optional and only needed for organizations that require it.
//
// This method is typically used during initial setup to exchange Fly.io credentials
// for sprite-specific access tokens.
func CreateToken(ctx context.Context, flyMacaroon, orgSlug string, inviteCode string) (string, error) {
	// Default API URL
	apiURL := "https://api.sprites.dev"

	// Build request URL
	url := fmt.Sprintf("%s/v1/organizations/%s/tokens", apiURL, orgSlug)

	// Create request body
	reqBody := struct {
		Description string `json:"description,omitempty"`
		InviteCode  string `json:"invite_code,omitempty"`
	}{
		Description: "Sprite SDK Token",
	}

	if inviteCode != "" {
		reqBody.InviteCode = inviteCode
	}

	jsonData, err := json.Marshal(reqBody)
	if err != nil {
		return "", fmt.Errorf("failed to marshal request: %w", err)
	}

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return "", fmt.Errorf("failed to create request: %w", err)
	}

	// Set headers - Fly tokens use "FlyV1" prefix
	httpReq.Header.Set("Authorization", "FlyV1 "+flyMacaroon)
	httpReq.Header.Set("Content-Type", "application/json")

	// Make request
	client := &http.Client{Timeout: 30 * time.Second}
	spritesDbg("sprites: http request", "method", "POST", "url", url)
	resp, err := client.Do(httpReq)
	if err != nil {
		return "", fmt.Errorf("failed to create token: %w", err)
	}
	defer resp.Body.Close()

	// Read response
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", fmt.Errorf("failed to read response: %w", err)
	}

	// Check status
	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusCreated {
		return "", fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Parse response
	var tokenResp struct {
		Token string `json:"token"`
	}
	if err := json.Unmarshal(body, &tokenResp); err != nil {
		return "", fmt.Errorf("failed to parse response: %w", err)
	}

	if tokenResp.Token == "" {
		return "", fmt.Errorf("no token returned in response")
	}

	return tokenResp.Token, nil
}

// getOrCreatePool gets or creates a control pool for the given sprite
func (c *Client) getOrCreatePool(spriteName string) *controlPool {
	c.poolsMu.RLock()
	pool, exists := c.pools[spriteName]
	c.poolsMu.RUnlock()

	if exists {
		return pool
	}

	c.poolsMu.Lock()
	defer c.poolsMu.Unlock()

	// Check again in case another goroutine created it
	pool, exists = c.pools[spriteName]
	if exists {
		return pool
	}

	pool = newControlPool(c, spriteName)
	c.pools[spriteName] = pool
	return pool
}

// Close closes the client and all pooled connections
func (c *Client) Close() error {
	c.poolsMu.Lock()
	defer c.poolsMu.Unlock()

	for _, pool := range c.pools {
		pool.close()
	}
	c.pools = nil

	return nil
}
