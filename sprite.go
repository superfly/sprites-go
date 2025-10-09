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
