// Package sprites provides an idiomatic Go API for working with sprites.
package sprites

import (
	"fmt"
	"net/http"
	"time"
)

// Client is the main SDK client for interacting with the sprite API.
type Client struct {
	baseURL    string
	token      string
	httpClient *http.Client
}

// Option is a functional option for configuring the SDK client.
type Option func(*Client)

// New creates a new SDK client with the given token and options.
func New(token string, opts ...Option) *Client {
	c := &Client{
		baseURL: "https://api.sprite.dev",
		token:   token,
		httpClient: &http.Client{
			Timeout: 30 * time.Second,
		},
	}

	for _, opt := range opts {
		opt(c)
	}

	return c
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

// Sprite returns a Sprite instance for the given name.
// This doesn't create the sprite on the server, it just returns a handle to work with it.
func (c *Client) Sprite(name string) *Sprite {
	return &Sprite{
		name:   name,
		client: c,
	}
}

// Create creates a new sprite with the given name and returns a handle to it.
// This is a placeholder for the actual sprite creation API call.
func (c *Client) Create(name string) (*Sprite, error) {
	// TODO: Implement actual sprite creation API call
	// For now, just return a sprite handle
	return &Sprite{
		name:   name,
		client: c,
	}, nil
}

// List returns a list of available sprites.
// This is a placeholder for the actual sprite listing API call.
func (c *Client) List() ([]*Sprite, error) {
	// TODO: Implement actual sprite listing API call
	return nil, fmt.Errorf("not implemented")
}

