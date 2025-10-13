package sprites

import (
	"context"
	"time"
)

// OrganizationInfo represents organization information attached to a sprite
type OrganizationInfo struct {
	Name string
	URL  string
}

// Sprite represents a sprite instance.
type Sprite struct {
	name   string
	client *Client
	org    *OrganizationInfo

	// Additional fields from API responses
	ID               string
	OrganizationName string
	Status           string
	Config           *SpriteConfig
	Environment      map[string]string
	CreatedAt        time.Time
	UpdatedAt        time.Time
	BucketName       string
	PrimaryRegion    string
	URL              string
	URLSettings      *URLSettings

	// Control connection support
	supportsControl bool
	controlChecked  bool
}

// Name returns the sprite's name.
func (s *Sprite) Name() string {
	return s.name
}

// Client returns the client associated with this sprite.
func (s *Sprite) Client() *Client {
	return s.client
}

// Organization returns the organization information associated with this sprite.
func (s *Sprite) Organization() *OrganizationInfo {
	return s.org
}

// Destroy destroys the sprite.
func (s *Sprite) Destroy() error {
	return s.Delete(context.Background())
}

// ensureControlSupport checks if the sprite supports control connections
// This is called lazily on first exec/proxy operation
func (s *Sprite) ensureControlSupport(ctx context.Context) {
	if s.controlChecked {
		return
	}
	s.controlChecked = true

	// Try to establish a control connection to test support
	pool := s.client.getOrCreatePool(s.name)
	conn, err := pool.dial(ctx)
	if err != nil {
		// Control connections not supported (404 or other error)
		s.supportsControl = false
		return
	}

	// Success - control connections are supported
	s.supportsControl = true

	// Add this initial connection to the pool
	conn.mu.Lock()
	conn.busy = false
	conn.mu.Unlock()

	// Connection is already in pool.conns from dial()
}
