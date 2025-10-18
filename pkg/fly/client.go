package fly

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"time"
)

// LocalAPI is a singleton HTTP client for making requests to the Fly local API socket
var LocalAPI = &Client{
	socketPath: "/.fly/api",
	timeout:    10 * time.Second,
}

// Client is an HTTP client for the Fly local API
type Client struct {
	socketPath string
	timeout    time.Duration
}

// Get performs a GET request to the local API
func (c *Client) Get(ctx context.Context, path string) (*http.Response, error) {
	return c.Do(ctx, http.MethodGet, path, nil)
}

// Head performs a HEAD request to the local API
func (c *Client) Head(ctx context.Context, path string) (*http.Response, error) {
	return c.Do(ctx, http.MethodHead, path, nil)
}

// Post performs a POST request to the local API
func (c *Client) Post(ctx context.Context, path string, body io.Reader) (*http.Response, error) {
	return c.Do(ctx, http.MethodPost, path, body)
}

// Do performs an HTTP request to the local API
func (c *Client) Do(ctx context.Context, method, path string, body io.Reader) (*http.Response, error) {
	dialer := &net.Dialer{Timeout: 2 * time.Second}
	socketPath := c.socketPath
	transport := &http.Transport{
		DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
			return dialer.DialContext(ctx, "unix", socketPath)
		},
	}
	client := &http.Client{
		Transport: transport,
		Timeout:   c.timeout,
	}

	// Build the URL - use http://flaps as the host for the unix socket
	reqURL := fmt.Sprintf("http://flaps%s", path)

	req, err := http.NewRequestWithContext(ctx, method, reqURL, body)
	if err != nil {
		return nil, err
	}

	return client.Do(req)
}

// parseURL parses a URL path and adds query parameters
func parseURL(basePath string, params map[string]string) string {
	if len(params) == 0 {
		return basePath
	}

	u, err := url.Parse(basePath)
	if err != nil {
		return basePath
	}

	q := u.Query()
	for k, v := range params {
		q.Set(k, v)
	}
	u.RawQuery = q.Encode()
	return u.String()
}

// getAppName returns the app name from the environment
func getAppName() (string, error) {
	app := os.Getenv("FLY_APP_NAME")
	if app == "" {
		return "", fmt.Errorf("FLY_APP_NAME environment variable not set")
	}
	return app, nil
}

// getMachineID returns the machine ID from the environment
func getMachineID() (string, error) {
	mid := os.Getenv("FLY_MACHINE_ID")
	if mid == "" {
		return "", fmt.Errorf("FLY_MACHINE_ID environment variable not set")
	}
	return mid, nil
}

// Info holds Fly environment information
type Info struct {
	AppName   string
	MachineID string
}

// Environment returns information about the Fly environment from environment variables
func Environment() *Info {
	return &Info{
		AppName:   os.Getenv("FLY_APP_NAME"),
		MachineID: os.Getenv("FLY_MACHINE_ID"),
	}
}

// Suspend suspends the current machine
func Suspend(ctx context.Context) error {
	app, err := getAppName()
	if err != nil {
		return err
	}

	mid, err := getMachineID()
	if err != nil {
		return err
	}

	path := fmt.Sprintf("/v1/apps/%s/machines/%s/suspend", app, mid)
	resp, err := LocalAPI.Post(ctx, path, nil)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("suspend failed with status %d: %s", resp.StatusCode, string(body))
	}

	return nil
}

// Secret represents a Fly secret
type Secret struct {
	CreatedAt string `json:"created_at"`
	Digest    string `json:"digest"`
	Name      string `json:"name"`
	UpdatedAt string `json:"updated_at"`
	Value     string `json:"value"`
}

// SecretsResponse represents the response from the secrets list API
type SecretsResponse struct {
	Secrets []Secret `json:"secrets"`
}

// Secrets provides access to the Fly secrets API
var Secrets = &SecretsAPI{}

// SecretsAPI provides methods for interacting with Fly secrets
type SecretsAPI struct{}

// List returns all secrets for the current app
func (s *SecretsAPI) List(ctx context.Context, minVersion string) ([]Secret, error) {
	app, err := getAppName()
	if err != nil {
		return nil, err
	}

	params := map[string]string{
		"show_secrets": "true",
	}
	if minVersion != "" {
		params["min_version"] = minVersion
	}

	path := parseURL(fmt.Sprintf("/v1/apps/%s/secrets", app), params)
	resp, err := LocalAPI.Get(ctx, path)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("list secrets failed with status %d: %s", resp.StatusCode, string(body))
	}

	var secretsResp SecretsResponse
	if err := json.NewDecoder(resp.Body).Decode(&secretsResp); err != nil {
		return nil, fmt.Errorf("failed to decode secrets response: %w", err)
	}

	return secretsResp.Secrets, nil
}

// Get returns a specific secret by name
func (s *SecretsAPI) Get(ctx context.Context, key string, minVersion string) (*Secret, error) {
	app, err := getAppName()
	if err != nil {
		return nil, err
	}

	params := map[string]string{
		"show_secrets": "true",
	}
	if minVersion != "" {
		params["min_version"] = minVersion
	}

	path := parseURL(fmt.Sprintf("/v1/apps/%s/secrets/%s", app, key), params)
	resp, err := LocalAPI.Get(ctx, path)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("get secret failed with status %d: %s", resp.StatusCode, string(body))
	}

	var secret Secret
	if err := json.NewDecoder(resp.Body).Decode(&secret); err != nil {
		return nil, fmt.Errorf("failed to decode secret response: %w", err)
	}

	return &secret, nil
}
