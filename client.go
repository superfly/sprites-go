// Package sprites provides an idiomatic Go API for working with sprites.
package sprites

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// Client is the main SDK client for interacting with the sprite API.
type Client struct {
	baseURL       string
	token         string
	httpClient    *http.Client
	spriteVersion atomic.Value // stores string, empty until captured from response header

	// Control connection pools per sprite
	poolsMu sync.RWMutex
	pools   map[string]*controlPool

	// Control initialization behavior
	controlInitTimeout time.Duration

	// disableControl prevents automatic control connection usage
	disableControl bool
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

	// Wrap transport to capture Sprite-Version header from responses
	transport := c.httpClient.Transport
	if transport == nil {
		transport = http.DefaultTransport
	}
	c.httpClient.Transport = &versionCapturingTransport{
		wrapped:       transport,
		versionHolder: &c.spriteVersion,
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

// WithControlInitTimeout sets how long Sprite() will wait to establish a control connection
// before falling back to legacy endpoint API for that Sprite. Defaults to 2s.
func WithControlInitTimeout(d time.Duration) Option {
	return func(c *Client) {
		c.controlInitTimeout = d
	}
}

// WithDisableControl prevents the SDK from using control connections.
// When disabled, all operations use direct WebSocket connections per request.
func WithDisableControl() Option {
	return func(c *Client) {
		c.disableControl = true
	}
}

// Sprite returns a Sprite instance for the given name.
// This doesn't create the sprite on the server, it just returns a handle to work with it.
func (c *Client) Sprite(name string) *Sprite {
	s := &Sprite{
		name:   name,
		client: c,
	}
	// Attempt to establish control connection upfront; block until success or timeout/404
	ctx, cancel := context.WithTimeout(context.Background(), c.controlInitTimeout)
	defer cancel()
	s.ensureControlSupport(ctx)
	return s
}

// SpriteWithOrg returns a Sprite instance for the given name with organization information.
// This doesn't create the sprite on the server, it just returns a handle to work with it.
func (c *Client) SpriteWithOrg(name string, org *OrganizationInfo) *Sprite {
	s := &Sprite{
		name:   name,
		client: c,
		org:    org,
	}
	ctx, cancel := context.WithTimeout(context.Background(), c.controlInitTimeout)
	defer cancel()
	s.ensureControlSupport(ctx)
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

// SpriteVersion returns the captured server version, or empty string if unknown.
func (c *Client) SpriteVersion() string {
	if v := c.spriteVersion.Load(); v != nil {
		return v.(string)
	}
	return ""
}

// supportsPathAttach returns true if the server supports path-based attach endpoint.
func (c *Client) supportsPathAttach() bool {
	return supportsPathAttach(c.SpriteVersion())
}

// FetchVersion makes a lightweight API call to capture the sprite's version.
// This is called automatically before attach operations if the version is unknown.
// The spriteName parameter is required to route the request to the specific sprite,
// since each sprite has its own version.
func (c *Client) FetchVersion(ctx context.Context, spriteName string) error {
	url := fmt.Sprintf("%s/v1/sprites/%s/exec", c.baseURL, spriteName)

	req, err := http.NewRequestWithContext(ctx, "HEAD", url, nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(req)
	if err != nil {
		return fmt.Errorf("failed to fetch version: %w", err)
	}
	defer resp.Body.Close()

	// Version is captured by the transport wrapper
	return nil
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
func CreateToken(ctx context.Context, flyMacaroon, orgSlug string, inviteCode string, apiURL ...string) (string, error) {
	// Default API URL if not provided
	baseURL := "https://api.sprites.dev"
	if len(apiURL) > 0 && apiURL[0] != "" {
		baseURL = apiURL[0]
	}

	// Build request URL
	url := fmt.Sprintf("%s/v1/organizations/%s/tokens", baseURL, orgSlug)

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
	authHeader := "FlyV1 " + flyMacaroon
	httpReq.Header.Set("Authorization", authHeader)
	httpReq.Header.Set("Content-Type", "application/json")

	// Make request
	// Force HTTP/1.1 to avoid HTTP/2 header size limits in Fly.io's edge proxy
	// The edge proxy rejects HTTP/2 requests with large headers (>16KB) even though
	// the backend supports much larger headers (256KB)
	// Setting TLSNextProto to a non-nil empty map disables HTTP/2 in the transport
	client := &http.Client{
		Timeout: 30 * time.Second,
		Transport: &http.Transport{
			TLSNextProto: make(map[string]func(authority string, c *tls.Conn) http.RoundTripper),
		},
	}
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
		// Parse structured error for 4xx/5xx responses
		if apiErr := parseAPIError(resp, body); apiErr != nil {
			return "", apiErr
		}
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

// signalSession sends a signal to a session via HTTP POST.
// This is used as a fallback when the server doesn't support WebSocket signals.
func (c *Client) signalSession(ctx context.Context, spriteName, sessionID, signal string) error {
	url := fmt.Sprintf("%s/v1/sprites/%s/exec/%s/kill?signal=%s&timeout=0s",
		c.baseURL, spriteName, sessionID, signal)

	req, err := http.NewRequestWithContext(ctx, "POST", url, nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(req)
	if err != nil {
		return fmt.Errorf("failed to send signal: %w", err)
	}
	defer resp.Body.Close()

	// 410 Gone means session already exited - not an error
	if resp.StatusCode == http.StatusGone {
		return nil
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("signal failed (status %d): %s", resp.StatusCode, strings.TrimSpace(string(body)))
	}

	return nil
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
